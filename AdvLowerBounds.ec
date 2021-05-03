(* Adversarial Lower Bounds Framework *)

prover quorum=2 ["Z3" "Alt-Ergo"].  (* both provers must succeed on goals *)

timeout 2.  (* can increase *)

require import AllCore List FSet.

(* ------------------------- auxiliary lemmas ------------------------- *)

lemma fcardUindep1 (xs : 'a fset, x : 'a) :
  ! x \in xs => card (xs `|` fset1 x) = card xs + 1.
proof.
move => x_notin_xs.
by rewrite fcardUI_indep 1:fsetI1 1:x_notin_xs // fcard1.
qed.

lemma all_elemsP (f : 'a -> bool, xs : 'a fset) :
  all f (elems xs) <=> (forall (x : 'a), x \in xs => f x).
proof.
rewrite allP.
split => [H x x_in_xs | H x x_in_elems_xs].
by rewrite H -memE.
by rewrite H memE.
qed.

lemma all_elems_or (f : 'a -> bool, xs ys : 'a fset) :
  all f (elems (xs `|` ys)) <=> (all f (elems xs) /\ all f (elems ys)).
proof.
rewrite !all_elemsP.
split => [H | [#] H1 H2].
split => [z z_in_xs | z z_in_ys].
rewrite H in_fsetU; by left.
rewrite H in_fsetU; by right.
move => z; rewrite in_fsetU => [[z_in_xs | z_in_ys]].
by rewrite H1.
by rewrite H2.
qed.

(* ------------------- theory of finite set ranges -------------------- *)

theory FRange.

(* frange n is {i | 0 <= i < n} *)

op frange (n : int) : int fset = oflist (range 0 n).

(* let's prove this definition is good: *)

lemma frange_impl_range (n i : int) :
  i \in frange n => 0 <= i < n.
proof.
by rewrite mem_oflist mem_range.
qed.

lemma range_impl_frange (n i : int) :
  0 <= i < n => i \in frange n.
proof.
by rewrite mem_oflist mem_range.
qed.

lemma frange_iff_range (n i : int) :
  i \in frange n <=> 0 <= i < n.
proof.
split; [apply frange_impl_range | apply range_impl_frange].
qed.

lemma frange0 :
  frange 0 = fset0.
proof.
by rewrite /frange range_geq // -set0E.
qed.

lemma frangeS (n : int) :
  0 <= n => frange (n + 1) = frange n `|` fset1 n.
proof.
move => ge0_n.
rewrite fsetP => i.
rewrite in_fsetU1 2!mem_oflist 2!mem_range.
split => [[#] ge0_i i_lt_n_plus1 | [[#] ge0_i lt_i_n | ->]].
rewrite ltzS lez_eqVlt in i_lt_n_plus1.
elim i_lt_n_plus1 => [// | i_lt_n]; by left.
split => [// | _]; rewrite ltzS lez_eqVlt; by right.
split => [// |]; by rewrite ltzS lezz.
qed.

lemma card_frange (n : int) :
  0 <= n => card (frange n) = n.
proof.
elim n => [| i ge0_i IH].
by rewrite frange0 fcards0.
rewrite frangeS // fcardUindep1.
case (i \in frange i) => [| //].
by rewrite frange_iff_range.
by rewrite IH.
qed.

lemma sub_range_card_leq (xs : int fset, n : int) :
  0 <= n =>
  (forall (j : int), j \in xs => 0 <= j < n) =>  
  card xs <= n.
proof.
move => ge0_n xs_sub_range.
rewrite -card_frange // subset_leq_fcard => i i_in_xs.
by rewrite range_impl_frange xs_sub_range.
qed.

lemma all_range_card_geq (xs : int fset, n : int) :
  0 <= n =>
  (forall (j : int), 0 <= j < n => j \in xs) =>  
  n <= card xs.
proof.
move => ge0_n sub_xs.
rewrite -card_frange //.
rewrite subset_leq_fcard => i i_in_frange.
by rewrite sub_xs frange_impl_range.
qed.

lemma sub_range_card_max (xs : int fset, n : int) :
  card xs = n =>
  (forall (j : int), j \in xs => 0 <= j < n) =>
  (forall (j : int), 0 <= j < n => j \in xs).
proof.
move => <<- xs_sub_range j zero_le_j_lt_card_xs.
have -> : xs = frange (card xs).
  rewrite eqEcard.
  split => [i i_in_xs |].
  by rewrite range_impl_frange xs_sub_range.
  rewrite card_frange 1:fcard_ge0 lezz.
by rewrite range_impl_frange.
qed.

end FRange.

(* ---- theory for generating all lists of length over a universe ----- *)

theory AllLists.

lemma all_flatten (f : 'a -> bool, xss : 'a list list) :
  all f (flatten xss) = all (all f) xss.
proof.
elim xss => [| x xss IH /=].
by rewrite flatten_nil.
by rewrite flatten_cons all_cat IH.
qed.

op next (xs : 'a list, yss : 'a list list) : 'a list list =
  flatten  
  (map
   (fun x =>
      map (fun ys => x :: ys) yss)
   xs).

lemma next (xs : 'a list, yss : 'a list list) :
  next xs yss = 
  flatten  
  (map
   (fun x =>
      map (fun ys => x :: ys) yss)
   xs).
proof.
by rewrite /next.
qed.

op all_lists (xs : 'a list, n : int) = fold (next xs) [[]] n.

lemma all_lists0 (xs : 'a list) :
  all_lists xs 0 = [[]].
proof.
by rewrite /all_lists fold0.
qed.

lemma all_listsS (xs : 'a list, n : int) :
  0 <= n =>
  all_lists xs (n + 1) = next xs (all_lists xs n).
proof.
move => ge0_n.
by rewrite /all_lists foldS.
qed.

lemma all_listsS_iff (xs ys : 'a list, n : int) :
  0 <= n =>
  ys \in all_lists xs (n + 1) <=>
  exists (z : 'a, zs : 'a list),
  ys = z :: zs /\ z \in xs /\ zs \in all_lists xs n.
proof.
move => ge0_n.
rewrite all_listsS // next /= -flatten_mapP.
split => [[z] [#] /= |].
rewrite mapP => z_in_xs [zs] [#] => zs_in_all_n ->>.
by exists z zs.
move => [z zs] [#] -> z_in_xs zs_in_all_n.
exists z.
by rewrite z_in_xs /= (map_f ((::) z)).
qed.

lemma all_lists_arity_wanted (xs : 'a list, n : int) :
  0 <= n =>
  all
  (fun ys => size ys = n /\ all (mem xs) ys)
  (all_lists xs n).
proof.
elim n => [| i ge0_i IH].
by rewrite all_lists0.
rewrite allP in IH.
rewrite allP => zs.
rewrite all_listsS_iff //.
move => [w ws] [#] -> w_in_xs ws_in_all_i /=.
rewrite w_in_xs /=.
have /= [#] <- -> /= := (IH ws ws_in_all_i).
by rewrite addzC.
qed.

lemma all_lists_arity_have (xs ys : 'a list, n : int) :
  0 <= n => size ys = n => (all (mem xs) ys) =>
  ys \in all_lists xs n.  
proof.
move : n.
elim ys => [n ge0_n /= <- | y ys IH n ge0_n].
by rewrite all_lists0.
rewrite /= => <- [#] y_in_xs all_mem_xs_ys.
rewrite addzC all_listsS_iff 1:size_ge0.
exists y ys => /=.
by rewrite y_in_xs /= IH 1:size_ge0.
qed.

lemma size_nseq_norm (n : int, x : 'a) :
  0 <= n => size (nseq n x) = n.
proof.
rewrite lez_eqVlt => ge0_n.
rewrite size_nseq /max.
by elim ge0_n => ->.
qed.

lemma all_lists_nseq (x : 'a, xs : 'a list, n : int) :
  0 <= n => x \in xs => nseq n x \in all_lists xs n.
proof.
move => ge0_n x_in_xs.
rewrite all_lists_arity_have //.
by rewrite size_nseq_norm.
rewrite allP => z; by rewrite mem_nseq => [#] _ => ->>.
qed.

(* makes a list of length n all of whose elements are either
   x1 or x2; when the elements index i is in zs, x1 is used;
   otherwise x2 is used *)

op make_list_either (x1 x2 : 'a, f : int -> bool, n : int) : 'a list =
  mkseq (fun i => if f i then x1 else x2) n.

lemma make_list_either_size (x1 x2 : 'a, f : int -> bool, n : int) :
  0 <= n => size (make_list_either x1 x2 f n) = n.
proof.  
rewrite lez_eqVlt => ge0_n.
rewrite /make_list_either size_mkseq /max.
by elim ge0_n => ->.
qed.

lemma make_list_either_all_in
      (xs : 'a list, x1 x2 : 'a, f : int -> bool, n : int) :
  0 <= n => x1 \in xs => x2 \in xs =>
  all (mem xs) (make_list_either x1 x2 f n).
proof.
move => ge0_n x1_in_xs x2_in_xs.
rewrite /make_list_either allP => z.
rewrite mkseqP => [] [i] [#] ge0_i i_rng -> /=.
by case (f i).
qed.

lemma make_list_either_in_all_lists
      (xs : 'a list, x1 x2 : 'a, f : int -> bool, n : int) :
  0 <= n => x1 \in xs => x2 \in xs =>
  (make_list_either x1 x2 f n) \in all_lists xs n.
proof.
move => ge0_n x1_in_xs x2_in_xs.
by rewrite all_lists_arity_have // 1:make_list_either_size //
           make_list_either_all_in.
qed.

lemma make_list_either_nth (x1 x2 : 'a, f : int -> bool, n, i : int) :
  0 <= n => 0 <= i < n =>
  nth witness (make_list_either x1 x2 f n) i = if f i then x1 else x2.
proof.
move => ge0_n i_rng.
rewrite /make_list_either.
by rewrite nth_mkseq.
qed.

end AllLists.

(* ------------------- lower bounds abstract theory ------------------- *)

abstract theory LB.  (* must be cloned before use *)

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

end LB.
