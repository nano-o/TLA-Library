------------------------------ MODULE Quorums ------------------------------

(***************************************************************************)
(* Quorums, as used by distributed consensus algorithms.                   *)
(***************************************************************************)

EXTENDS FiniteSets, Naturals, Integers

CONSTANT Quorum, FastQuorum, P

ASSUME \A Q \in Quorum : Q \subseteq P
ASSUME \A Q1,Q2 \in Quorum : Q1 \cap Q2 # {}
ASSUME \A Q1,Q2 \in FastQuorum : \A Q3 \in Quorum : Q1 \cap Q2 \cap Q3 # {}

(***************************************************************************)
(* Majority quorums and three fourths quorums.  For provinding concrete    *)
(* quorums to the model-checker.                                           *)
(***************************************************************************)
MajQuorums == {Q \in SUBSET P : 2 * Cardinality(Q) > Cardinality(P)}
ThreeFourthQuorums == {Q \in SUBSET P : 4 * Cardinality(Q) > 3 * Cardinality(P)}

=============================================================================
\* Modification History
\* Last modified Wed Jun 08 11:25:00 EDT 2016 by nano
\* Created Mon May 02 21:03:00 EDT 2016 by nano
