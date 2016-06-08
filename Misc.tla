------------------------------- MODULE Misc -------------------------------

EXTENDS Naturals

None(S) == CHOOSE x : x \notin S

Some(S) == CHOOSE e \in S : TRUE

(***************************************************************************)
(* All sequences of elements of X which have a length smaller or equal to  *)
(* b.                                                                      *)
(***************************************************************************)
BSeq(X, b) == {<<>>} \cup UNION {[1..n -> X] : n \in 1..b}

Min(i,j) == IF i < j THEN i ELSE j

Max(S, LessEq(_,_)) == CHOOSE e \in S : \A e1 \in S : LessEq(e1,e)

=============================================================================
\* Modification History
\* Last modified Wed Jun 08 11:22:21 EDT 2016 by nano
\* Created Thu Feb 04 16:55:11 EST 2016 by nano
