(* Application of Adversarial Lower Bounds Framework to Or Function *)

prover quorum=2 ["Z3" "Alt-Ergo"].  (* both provers must succeed on goals *)

timeout 2.  (* can increase *)

require import AllCore List FSet LowerBounds.

type inp = bool.

op univ = [true; false].

type out = bool.

(* arity can be any non-negative number *)

op arity : {int | 0 <= arity} as ge0_arity.

type aux = unit.  (* auxiliary value conveys no information *)

(* these two operators assume argument has size arity *)

op all_false (inps : bool list) =
  forall (i : int),
  0 <= i < arity => nth witness inps i = false.

op some_true (inps : bool list) =
  exists (i : int),
  0 <= i < arity /\ nth witness inps i = true.

lemma some_true_equiv (inps : bool list) :
  some_true inps <=> ! (all_false inps).
proof.
rewrite /some_true /all_false negb_forall /=.
split => [[] i [] i_rng nth_i_true | [] i].
exists i.
by rewrite negb_imply neqF /= i_rng nth_i_true.
rewrite negb_imply neqF /= => [[]] x_rng nth_i.
exists i; by rewrite x_rng nth_i.
qed.

lemma all_false_equiv (inps : bool list) :
  all_false inps <=> ! (some_true inps).
proof.
rewrite /some_true /all_false negb_exists /=.
split => [H i | H i i_rng].
rewrite negb_and.
case (0 <= i < arity) => [i_arity | //].
right; by rewrite -neqF H.
have /negb_and [] // := H i.
by rewrite neqF eqT.
qed.

lemma all_false_nseq :
  all_false (nseq arity false).
proof.
rewrite /all_false => i i_rng.
by rewrite nth_nseq.
qed.

(* good says nothing more *)

op good (_ : aux, xs : inp list) : bool = true.

(* generalized or function *)

op f (_ : aux, xs : inp list) =
  if size xs <> arity
  then None
  else Some (some_true xs).

lemma f_false (xs : inp list) :
  size xs = arity => all_false xs => f () xs = Some false.
proof.
rewrite /f => -> /=.
by rewrite all_false_equiv neqF.
qed.

lemma f_false_nseq :
  f () (nseq arity false) = Some false.
proof.
rewrite f_false // 1:AllLists.size_nseq_norm 1:ge0_arity // all_false_nseq.
qed.

lemma f_true (xs : inp list) :
  size xs = arity => some_true xs => f () xs = Some true.
proof.
by rewrite /f => -> ->.
qed.

lemma all_mem_univ (xs : inp list) :
  all (mem univ) xs.
proof.
elim xs => [// | x ys IH].
rewrite /univ /=.
by case x.
qed.

clone import LB as LB' with
  type inp <- inp,
  op univ  <- univ,
  op def   <- true,
  type out <- out,
  op arity <- arity,
  type aux <- aux,
  op good  <- good,
  op f     <- f
proof *.
realize ge0_arity. rewrite ge0_arity. qed.

realize univ_uniq. by rewrite /univ. qed.

realize univ_def. by rewrite /univ. qed.

realize good.
rewrite /f => aux xs -> _.
by exists (some_true xs).
qed.

realize bad.
rewrite /f.
move => aux xs [-> // | []].
by have := all_mem_univ xs.
by rewrite /good.
qed.

lemma init_inpss_all :
  init_inpss () = AllLists.all_lists univ arity.
proof.
rewrite /init_inpss /good -all_filterP allP => xs //.
qed.

lemma nseq_false_in_init_inpss :
  nseq arity false \in init_inpss ().
proof.
rewrite init_inpss_all.
by rewrite AllLists.all_lists_nseq 1:ge0_arity.
qed.

(* here is our adversary *)

module Adv : ADV = {
  proc init() : unit = {
    return ();
  }

  proc ans_query(i : int) : inp = {
    return false;
  }
}.

lemma Adv_ans_query_false :
  hoare[Adv.ans_query : true ==> !res].
proof.
proc; auto.
qed.

lemma Adv_init_ll : islossless Adv.init.
proof.
proc; auto.
qed.

lemma Adv_ans_query_ll : islossless Adv.ans_query.
proof.
proc; auto.
qed.

op all_queries_false (queries : int fset, inps : inp list) : bool =
  all (fun i => nth witness inps i = false) (elems queries).

lemma all_queries_falseP (queries : int fset, inps : inp list) :
  queries_in_range queries =>
  all_queries_false queries inps <=>
  forall (i : int),
  0 <= i < arity => i \in queries =>
  ! nth witness inps i.
proof.
move => qir_queries.
rewrite /all_queries_false allP.
split => [H i i_rng i_in_queries | H x].
have /= -> // := H i _.
by rewrite -memE.
rewrite -memE /= => x_in_queries.
by rewrite neqF H 1:qir_queries.
qed.

lemma all_queries_false_queries_eq_all_range (queries : int fset) :
  queries_eq_all_range queries =>
  all_queries_false queries = all_false.
proof.
rewrite /queries_eq_all_range => [#] qir_queries airq_queries.
apply fun_ext => i.
rewrite eq_iff.
rewrite /all_queries_false all_queries_predP //.
by split => [| ?].
qed.

lemma all_queries_false_nseq (queries : int fset) :
  queries_in_range queries =>
  all_queries_false queries (nseq arity false).
proof.
move => qir_queries.
rewrite /all_queries_false all_elemsP => x x_in_queries /=.
by rewrite nth_nseq 1:qir_queries.
qed.

lemma filter_all_queries_false0 :
  filter (all_queries_false fset0) (init_inpss ()) = init_inpss ().
proof.
rewrite /all_queries_false /=.
have -> :
  (fun (inps : bool list) =>
   all (fun (i : int) => nth witness inps i = false) (elems fset0)) =
  predT.
  apply fun_ext => inps.
  by rewrite elems_fset0.
by rewrite filter_predT.
qed.

lemma filter_all_queries_false_add (queries : int fset, i : int) :
  filter (all_queries_false (queries `|` fset1 i)) (init_inpss ()) =
  filter
  (fun inps => nth witness inps i = false)
  (filter (all_queries_false queries) (init_inpss ())).
proof.   
rewrite init_inpss_all -filter_predI /predI.
congr.
apply fun_ext => bs.
by rewrite /all_queries_false all_elems_or elems_fset1 andbC.
qed.

lemma filter_all_queries_false_f_false (queries : int fset) :
  queries_in_range queries =>
  exists (xs : inp list),
  (xs \in filter (all_queries_false queries) (init_inpss ())) /\
   f () xs = Some false.
proof.
move => qir_queries.
exists (nseq arity false).
split.
rewrite mem_filter.
split.
by rewrite all_queries_false_nseq.
rewrite nseq_false_in_init_inpss.
apply f_false_nseq.
qed.

lemma f_true_all_lists_make (queries : int fset, i : int) :
  0 <= i < arity => ! (i \in queries) =>
  f () (AllLists.all_lists_make false true (fun i => i \in queries) arity) =
  Some true.
proof.
move => i_rng i_notin_queries.
rewrite f_true 1:AllLists.all_lists_make_size 1:ge0_arity //
        /some_true.
exists i.
split => [// |].
by rewrite AllLists.all_lists_make_nth // 1:ge0_arity /=
          i_notin_queries.
qed.

lemma filter_all_queries_false_f_true (queries : int fset, i : int) :
  queries_in_range queries => 0 <= i < arity => ! (i \in queries) =>
  exists (xs : inp list),
  (xs \in filter (all_queries_false queries) (init_inpss ())) /\
  f () xs = Some true.
proof.
move => qir_queries i_rng i_notin_queries.
exists (AllLists.all_lists_make false true (fun i => i \in queries) arity).
split.
rewrite mem_filter.
split.
rewrite all_queries_falseP // => j j_rng j_in_queries.
rewrite AllLists.all_lists_make_nth 1:ge0_arity 1:qir_queries //
           x_in_queries.
rewrite init_inpss_all AllLists.all_lists_make_have 1:ge0_arity //.
by rewrite (f_true_all_lists_make _ i).
qed.

lemma filter_all_queries_false_done (queries : int fset) :
  queries_in_range queries =>
  (card queries = arity <=>
   inpss_done () (filter (all_queries_false queries) (init_inpss ()))).
proof.    
move => qir_queries.
split => [cq_eq_arities | done_filtering].
rewrite all_queries_false_queries_eq_all_range.
rewrite all_queries_cond // in cq_eq_arities.
rewrite /inpss_done => out1 out2.
rewrite 2!mapP.
move => [xs] [#] xs_in_filter ->.
move => [ys] [#] ys_in_filter ->.
rewrite mem_filter in xs_in_filter.
rewrite mem_filter in ys_in_filter.
elim xs_in_filter => xs_af xs_in_init.
elim ys_in_filter => ys_af ys_in_init.
have size_xs : size xs = arity.
  rewrite (inpss_invar_size_alt () (init_inpss ())) 1:inpss_invar_init //.
have size_ys : size ys = arity.
  rewrite (inpss_invar_size_alt () (init_inpss ())) 1:inpss_invar_init //.
by rewrite f_false // f_false.
rewrite all_queries_cond // => i i_in_rng.
case (i \in queries) => [// | i_notin_queries].
rewrite /inpss_done in done_filtering.
have [] xs [#] xs_in_fil f_xs_false :
  exists (xs : inp list),
  xs \in filter (all_queries_false queries) (init_inpss ()) /\
  f () xs = Some false.
  by rewrite filter_all_queries_false_f_false.
have [] ys [#] ys_in_fil f_ys_true :
  exists (ys : inp list),
  ys \in filter (all_queries_false queries) (init_inpss ()) /\
  f () ys = Some true.
  by rewrite (filter_all_queries_false_f_true _ i).
have : f () xs = f () ys.
  apply done_filtering; by rewrite (map_f (f tt)).
by rewrite f_xs_false f_ys_true.
qed.

lemma G_Adv_main (Alg <: ALG{Adv}) :
  hoare [G(Alg, Adv).main : true ==> res.`1 \/ res.`2 = arity].
proof.
proc.
seq 7 :
  (inpss = init_inpss () /\ error = false /\ don = inpss_done () inpss /\
   stage = 0 /\ queries = fset0).
wp.
call (_ : true); first auto.
call (_ : true); first auto.
auto.
while
  (stage = card queries /\ queries_in_range queries /\
   inpss = filter (all_queries_false queries) (init_inpss ()) /\
   don = inpss_done () inpss).
seq 1 :
  (stage = card queries /\ queries_in_range queries /\
   inpss = filter (all_queries_false queries) (init_inpss ()) /\
   don = inpss_done () inpss /\ !don /\ !error).
call (_ : true); first auto.
if.
wp.
call (_ : true); first auto.
call Adv_ans_query_false.
auto; progress.
by rewrite fcardUindep1.
smt(queries_in_range_add).
by rewrite filter_all_queries_false_add H5.
auto.
auto; progress.
by rewrite fcards0.
by rewrite queries_in_range0.
by rewrite filter_all_queries_false0.
smt(filter_all_queries_false_done).
qed.

lemma lower_bound_or &m :
  exists (Adv <: ADV),
  islossless Adv.init /\ islossless Adv.ans_query /\
  forall (Alg <: ALG{Adv}),
  islossless Alg.init => islossless Alg.make_query =>
  islossless Alg.query_result =>
  Pr[G(Alg, Adv).main() @ &m : res.`1 \/ res.`2 = arity] = 1%r.
proof.
exists Adv.
split; first apply Adv_init_ll.
split; first apply Adv_ans_query_ll.
move => Alg Alg_init_ll Alg_make_query_ll Alg_query_result_ll.
byphoare => //.
conseq
  (_ : true ==> true)
  (_ : true ==> res.`1 \/ res.`2 = arity) => //.
apply (G_Adv_main Alg).
rewrite (G_ll Alg Adv) 1:Alg_init_ll 1:Alg_make_query_ll
        1:Alg_query_result_ll 1:Adv_init_ll Adv_ans_query_ll.
qed.
