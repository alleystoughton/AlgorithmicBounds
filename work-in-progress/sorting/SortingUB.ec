(* Application of Upper Bounds Framework to Comparison-based
   Sorting *)

(* --------------------------------------------------------------------
 * Copyright (c) - 2021 - Boston University
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

prover quorum=2 ["Alt-Ergo" "Z3"].

timeout 2.  (* can increase *)

(* the algorithm is trying to figure out how a list of distinct
   elements of size len should be permuted in order to be sorted

   it can ask queries of the form (i, j), for 0 <= i, j < len,
   asking whether the ith element of the list is less-than-or-equal-to
   the jth element (the answer is true or false); it can't ask
   questions about the values of the list elements themselves *)

require import AllCore List IntDiv StdOrder IntMin FSetAux Perms Binomial.
import IntOrder.

require UpperBounds.       (* adversarial lower bounds framework *)
require import ListSizes.  (* showing uniq lists have the same size *)
require import AllLists.   (* generating all lists of length over universe *)
require import IntLog.     (* integer logarithms *)

require import SortingProb.  (* comparison-based sorting problem *)

clone import UpperBounds as UB with
  type inp <- inp,
  op univ  <- univ,
  op def   <- true,
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

realize univ_uniq. by rewrite /univ. qed.

realize univ_def. by rewrite /univ. qed.

realize good. smt(f_is_some). qed.

realize bad.
move => aux xs H.
have not_tot_ord_xs : ! total_ordering xs.
  elim H; first smt(total_ordering_size).
  elim; first smt(allP).
  smt().
by rewrite f_bad.
qed.
(* end of realization *)

(* here is our algorithm: *)

module Alg : ALG = {
  proc init(aux : aux) : unit = {
  }

  proc make_query_or_report_output() : response = {
    var r : response;
    return r;
  }

  proc query_result(x : inp) : unit = {
  }
}.

(* algorithm is lossless *)

lemma Alg_init_ll : islossless Alg.init.
proof.
proc; auto.
qed.

lemma Alg_make_query_or_report_output_ll :
  islossless Alg.make_query_or_report_output.
proof.
proc; auto.
qed.

lemma Alg_query_result_ll :
  islossless Alg.query_result.
proof.
proc; auto.
qed.
