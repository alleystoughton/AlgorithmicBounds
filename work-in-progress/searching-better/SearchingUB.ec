(* Application of Upper Bounds Framework to Searching in Ordered
   Lists *)

prover quorum=2 ["Z3" "Alt-Ergo"].  (* both provers must succeed on goals *)

timeout 2.  (* can increase *)

(* given a list of size arity at least one element of which is equal
   to k, the algorithm is trying to find the least list index such
   that the list has k at that position

   it can query the values of elements of the list *)

require import AllCore List FSetAux StdOrder IntDiv.
import IntOrder.

require UpperBounds.     (* upper bounds framework *)
require import IntLog.   (* integer logarithms *)
require import IntDiv2.  (* division by powers of two *)

type inp = int.

(* univ consists of min_inp ... max_inp, and there are
   at least two elements *)

op min_inp : inp.
op max_inp : inp.

axiom min_lt_max : min_inp < max_inp.

op univ = range min_inp (max_inp + 1).

lemma univ_size :
  size univ = max_inp - min_inp + 1.
proof.
rewrite size_range ler_maxr.
smt(min_lt_max).
smt().
qed.

lemma min_inp_univ :
  min_inp \in univ.
proof.
rewrite mem_range.
smt(min_lt_max).
qed.

lemma max_inp_univ :
  max_inp \in univ.
proof.
rewrite mem_range.
smt(min_lt_max).
qed.

type out = int.

(* arity can be any positive number (otherwise int_log_up 2 arity
   would be meaningless - see our main theorem at end) *)

op arity : {int | 1 <= arity} as ge1_arity.

type aux = int.  (* value to be searched for *)

(* a list xs of size arity of inputs that are in univ is good relative
   to aux iff it contains aux and is sorted in (not-necessarily
   strictly) ascending order (according to the usual total ordering on
   int)

   note that if aux is not in univ, then there will be no input lists
   xs of size arity, all of whose elements are in univ, and where good
   aux xs holds *)

op good (aux : aux, xs : inp list) : bool =
  aux \in xs /\
  forall (i j : int),
  0 <= i <= j < arity => nth witness xs i <= nth witness xs j.

(* we need a definition to help define our f *)

op min_aux_index_rel (aux : aux, xs : inp list, i : out) : bool =
  0 <= i < size xs /\ nth witness xs i = aux /\
  (forall (j : int),
   0 <= j < size xs => nth witness xs j = aux => i <= j).

lemma min_aux_index_rel_unique (aux : aux, xs : inp list, i j : out) :
  min_aux_index_rel aux xs i => min_aux_index_rel aux xs j =>
  i = j.
proof. smt(). qed.

lemma min_aux_index_rel_exists (aux : aux, xs : inp list) :
  aux \in xs => exists (i : int), min_aux_index_rel aux xs i.
proof.
elim xs => [// | x xs IH /=].
rewrite -oraE => [[<- | aux_ne_x aux_in_xs]].
exists 0.
rewrite /min_aux_index_rel /=.
smt(size_ge0).
have [i mair_aux_xs_i] := IH _.
  trivial.
exists (i + 1).
rewrite /min_aux_index_rel.
smt(size_ge0).
qed.

(* now we can use the choice function to define: *)

op min_aux_index (aux : aux, xs : inp list) : out =
  choiceb (min_aux_index_rel aux xs) 0.

(* min_aux_index works as we want: *)

lemma min_aux_indexP (aux : aux, xs : inp list) :
  aux \in xs =>
  0 <= min_aux_index aux xs < size xs /\
  nth witness xs (min_aux_index aux xs) = aux /\
  (forall (j : int),
   0 <= j < size xs => nth witness xs j = aux =>
   min_aux_index aux xs <= j).
proof.
move => aux_in_xs.
have := choicebP (min_aux_index_rel aux xs) 0 _.
  by apply min_aux_index_rel_exists.
rewrite -/(min_aux_index aux xs).
pose i := min_aux_index aux xs.
smt().
qed.

(* here is our searching function, f: *)

op f (aux : aux, xs : inp list) : out option =
  if size xs = arity /\ all (mem univ) xs /\ good aux xs
  then Some (min_aux_index aux xs)
  else None.

clone import UpperBounds as UB with
  type inp <- inp,
  op univ  <- univ,
  op def   <- min_inp,
  type out <- out,
  op arity <- arity,
  type aux <- aux,
  op good  <- good,
  op f     <- f
proof *.
(* beginning of realization *)
realize ge0_arity.
rewrite (lez_trans 1) // ge1_arity.
qed.

realize univ_uniq. rewrite range_uniq. qed.

realize univ_def. rewrite min_inp_univ. qed.

realize good. smt(). qed.

realize bad. smt(). qed.
(* end of realization *)

(* here is our algorithm: *)

module Alg : ALG = {
  var aux : aux
  var i : int
  var found : bool
  var low : int
  var high : int
  var mid : int

  (* more global variables .... *)

  proc init(aux' : aux) : unit = {
    aux <- aux';
    i <- 0;
    found <- false;
    low <- 0;
    high <- arity;
    mid <- (low + high) %/ 2;
  }

  proc make_query_or_report_output() : response = {
    var r : response;
    if (found) {
      r <- Response_Report i;
    }
    else {
      r <- Response_Query i;
    }
    return r;
  }

  proc query_result(x : inp) : unit = {
    if (x = aux) {
      found <- true;
    }
    else if (x < aux) {
      low <- mid;
      mid <- (low + high) %/ 2;
      i <- i + 1;
    }
    else {
      high <- mid - 1;
      mid <- (low + high) %/ 2;
      i <- i + 1;
    }
  }
}.

lemma Alg_init_ll : islossless Alg.init.
proof.
admit.
qed.

lemma Alg_make_query_or_report_output_ll :
  islossless Alg.make_query_or_report_output.
proof.
admit.
qed.

lemma Alg_query_result_ll :
  islossless Alg.query_result.
proof.
admit.
qed.

(* the main lemma: *)

lemma G_main (aux' : aux, inps' : inp list) :
  hoare
  [G(Alg).main :
   aux = aux' /\ inps = inps' /\ size inps = arity /\
   all (mem univ) inps /\ good aux inps ==>
   res.`1 = f aux' inps' /\ res.`2 <= int_log_up 2 arity].
proof.
admit.
qed.

(* here is our main theorem: *)

lemma upper_bound &m :
  islossless Alg.init /\ islossless Alg.make_query_or_report_output /\
  islossless Alg.query_result /\
  (forall (aux : aux, inps : inp list),
   size inps = arity => all (mem univ) inps => good aux inps =>
   Pr[G(Alg).main(aux, inps) @ &m :
      res.`1 = f aux inps /\ res.`2 <= int_log_up 2 arity] = 1%r).
proof.
split; first apply Alg_init_ll.
split; first apply Alg_make_query_or_report_output_ll.
split; first apply Alg_query_result_ll.
move => aux' inps' size_inps'_eq_arity all_inps'_in_univ good_aux'_inps'.
byphoare
  (_ :
   aux = aux' /\ inps = inps' /\ size inps = arity /\
   all (mem univ) inps /\ good aux inps ==>
   res.`1 = f aux' inps' /\ res.`2 <= int_log_up 2 arity) => //.
conseq
  (_ : true ==> true)
  (_ :
   aux = aux' /\ inps = inps' /\ size inps = arity /\
   all (mem univ) inps /\ good aux inps ==>
   res.`1 = f aux' inps' /\ res.`2 <= int_log_up 2 arity) => //.
by conseq (G_main aux' inps').
rewrite (G_ll Alg) 1:Alg_init_ll 1:Alg_make_query_or_report_output_ll
        Alg_query_result_ll.
qed.
