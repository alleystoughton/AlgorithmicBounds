(* Adversarial Lower Bounds Framework *)

prover quorum=2 ["Z3" "Alt-Ergo"].  (* both provers must succeed on goals *)

timeout 2.  (* can increase *)

require import AllCore List FSetAux.
require import FRange.    (* finite ranges as sets *)
require import AllLists.  (* generating all lists of length over universe *)

(* theory parameters *)

type inp.  (* type of inputs *)

op univ : inp list.  (* universe with concrete ordering *)

op def : inp.  (* default inp *)

axiom univ_def : mem univ def.  (* default inp is in univ *)

axiom univ_uniq : uniq univ.  (* no duplicates in univ *)

type out.  (* type of outputs *)

op arity : {int | 0 <= arity} as ge0_arity.  (* arity of f *)

type aux.  (* auxiliary value, chosen by adversary *)

(* if xs : inp list has size arity and all of its elements
   are in univ, then good aux xs returns true iff xs is
   a valid argument to f aux *)

op good : aux -> inp list -> bool.

(* an argument xs to f aux should be a list of inputs of size arity,
   all of whose elements are in univ, and where good aux xs holds -
   note that there may be no such lists *)

op f : aux -> inp list -> out option.

(* when argument to f has the correct arity, is over univ, and
   satisfies good aux, we get Some of an answer *)

axiom good (aux : aux, xs : inp list) :
  size xs = arity => all (mem univ) xs => good aux xs =>
  exists (y : out), f aux xs = Some y.

(* when argument to f has the wrong arity, or is not over univ,
   or does not satisfy good aux, we get None *)

axiom bad (aux : aux, xs : inp list) :
  size xs <> arity \/ ! (all (mem univ) xs) \/ ! good aux xs =>
  f aux xs = None.

(* end of theory parameters *)

(* all possible lists of univ values of size arity that satisfy good
   aux; i.e., all possible arguments to f that will result in Some
   ...; it is possible for this to be the empty list *)

op init_inpss (aux : aux) : inp list list =
  List.filter (good aux) (AllLists.all_lists univ arity).

(* inpss invariant: all lists of possible inputs must cause (f aux) to
   return non-None answers: *)

op inpss_invar (aux : aux, inpss : inp list list) : bool =
  all is_some (map (f aux) inpss).

lemma inpss_invar_init (aux : aux) : 
  inpss_invar aux (init_inpss aux).
proof.
rewrite /inpss_invar /init_inpss.
have H := AllLists.all_lists_arity_wanted univ arity _.
  apply ge0_arity.
smt(allP mapP mem_filter good).
qed.

lemma inpss_invar_filter
      (aux: aux, inpss : inp list list, g : inp list -> bool) :
  inpss_invar aux inpss => inpss_invar aux (filter g inpss).
proof.
rewrite /inpss_invar.
smt(mapP mem_filter allP map_f).
qed.

lemma inpss_invar_size (aux : aux, inpss : inp list list) :
  inpss_invar aux inpss =>
  all (fun inps => size inps = arity) inpss.
proof.
rewrite /inpss_invar => all_is_some_map_f_inpss.
rewrite allP => inps inps_in_inpss /=.
rewrite allP in all_is_some_map_f_inpss.
have H := all_is_some_map_f_inpss (f aux inps) _.
  by rewrite (map_f (f aux)).
smt(good bad).
qed.

lemma inpss_invar_size_alt
      (aux : aux, inpss : inp list list, inps : inp list) :
  inpss_invar aux inpss => inps \in inpss =>
  size inps = arity.
proof.
move => inv.
have := inpss_invar_size aux inpss _.
  done.
rewrite allP /= => all_of_inpss_size inps_in_inpss.
by apply all_of_inpss_size.
qed.

(* filter a list of lists, keeping all the lists whose nth elements
   are y (n should be a valid index of all elements of xss) *)

op filter_nth (xss : 'a list list, n : int, y : 'a) : 'a list list =
  filter (fun xs => nth witness xs n = y) xss.

lemma mem_filter_nth (xss : 'a list list, n : int, y : 'a, ys : 'a list) :
  ys \in filter_nth xss n y <=> ys \in xss /\ nth witness ys n = y.
proof.
by rewrite mem_filter.
qed.

(* the game is done when (f aux) agrees on all possible input lists

   note that this could be true because inpss is empty *)

op inpss_done (aux : aux, inpss : inp list list) : bool =
  forall (x y : out option),
  x \in map (f aux) inpss => y \in map (f aux) inpss => x = y.

(* an adversary *)

module type ADV = {
  (* tell adversary to initialize itself and choose aux *)
  proc init() : aux

  (* ask adversary to answer query of what the ith input is *)
  proc ans_query(i : int) : inp
}.  

(* an algorithm *)

module type ALG = {
  (* tell algorithm to initialize itself, giving it aux *)
  proc init(aux : aux) : unit

  (* ask algorithm to make an input query, choosing an input index i
     such that 0 <= i < arity *)
  proc make_query() : int

  (* tell algorithm the result of its query *)
  proc query_result(x : inp) : unit
}.

(* game connecting algorithm and adversary *)

module G(Alg : ALG, Adv : ADV) = {
  proc main() : bool * int = {
    var inpss : inp list list;  (* current possible lists of inputs *)
    var don : bool;  (* is game done? *)
    var error : bool;  (* has game made illegal query? *)
    var stage : int;  (* stage of game *)
    var queries : int fset;  (* valid queries made by algorithm *)
    var aux : aux;  (* auxiliary value chosen by adversary *)

    var i : int;
    var inp : inp;

    aux <@ Adv.init();
    Alg.init(aux);
    inpss <- init_inpss aux;  (* start with all good lists of inputs *)
    (* by lemma inpss_invar_init, the invariant is established *)
    error <- false;  (* no error so far *)
    don <- inpss_done aux inpss;  (* are we already done? *)
    stage <- 0;
    queries <- fset0;
    while (!don /\ !error) {
      i <@ Alg.make_query();  (* let Alg make query *)
      if (0 <= i < arity /\ ! i \in queries) {
        queries <- queries `|` fset1 i;
        stage <- stage + 1;
        inp <@ Adv.ans_query(i);  (* ask Adv to answer query *)
        inp <- (inp \in univ) ? inp : def;  (* use def if inp not in universe *)
        Alg.query_result(inp);  (* tell Alg result of its query *)
        (* get rid of lists of inputs that aren't consistent with answer *)
        inpss <- filter_nth inpss i inp;
        don <- inpss_done aux inpss;  (* perhaps we're done now? *)
      }
      else {
        error <- true;  (* query was invalid *)
      }
    }
    return (error, stage);
  }
}.

op queries_in_range (queries : int fset) : bool =
  forall (i : int), i \in queries => 0 <= i < arity.

lemma queries_in_range0 :
  queries_in_range fset0.
proof.
move => i.
by rewrite in_fset0.
qed.

lemma queries_in_range_add (queries : int fset, i : int) :
  0 <= i < arity => queries_in_range queries =>
  queries_in_range (queries `|` fset1 i).
proof.
move => i_in_rng @/queries_in_range qir_queries j.
rewrite in_fsetU1 => [] [j_in_queries | -> //].
by apply qir_queries.
qed.

lemma queries_in_range_card_le_arity (queries : int fset) :
  queries_in_range queries => card queries <= arity.
proof.
move => qir_queries.
rewrite FRange.sub_range_card_leq 1:ge0_arity.
apply qir_queries.
qed.

op all_in_range_queries (queries : int fset) : bool =
  forall (i : int), 0 <= i < arity => i \in queries.

lemma all_queries_cond (queries : int fset) :
  queries_in_range queries =>
  (card queries = arity <=> all_in_range_queries queries).
proof.
move => qir_queries.
split => [card_queries_eq_arity i i_in_rng | airq_queries]. 
by rewrite (FRange.sub_range_card_max queries arity).
rewrite (lez_anti (card queries) arity) //.
split => [| _].
by rewrite (FRange.sub_range_card_leq queries arity) 1:ge0_arity.
by rewrite (FRange.all_range_card_geq queries arity) 1:ge0_arity.
qed.

op queries_eq_all_range (queries : int fset) : bool =
  queries_in_range queries /\ all_in_range_queries queries.

lemma all_queries_predP (queries : int fset, f : int -> bool) :
  queries_eq_all_range queries =>
  (all f (elems queries)) <=> (forall (i : int), 0 <= i < arity => f i).
proof.
move => @/queries_eq_all_range [#] qir_queries airq_queries.
split.
rewrite all_elemsP => all_queries_f i i_in_rng.
by rewrite all_queries_f airq_queries.
rewrite all_elemsP => H x x_in_queries.
by rewrite H qir_queries.
qed.

lemma G_ll (Alg <: ALG) (Adv <: ADV{Alg}) :
  islossless Alg.init => islossless Alg.make_query =>
  islossless Alg.query_result =>
  islossless Adv.init => islossless Adv.ans_query =>
  islossless G(Alg, Adv).main.
proof.
move =>
  Alg_init_ll Alg_make_query_ll Alg_query_result_ll
  Adv_init_ll Adv_ans_query_ll.    
proc.
while
  (queries_in_range queries /\ stage = card queries)
  (if error then 0 else arity - stage + 1).
move => z.
seq 1 :
  (queries_in_range queries /\ stage = card queries /\ !don /\ !error /\
  (if error then 0 else arity - stage + 1) = z).
auto.
call (_ : true).
auto.
if.
wp.
call (_ : true).
wp.
call (_ : true).
auto; progress.
by rewrite queries_in_range_add.
by rewrite fcardUindep1.
smt().
auto; progress; smt(queries_in_range_card_le_arity).
hoare.
call (_ : true).
auto.
smt().
wp.
call (_ : true).
call (_ : true).
auto; progress.
rewrite queries_in_range0.
by rewrite fcards0.
smt(queries_in_range_card_le_arity).
qed.
