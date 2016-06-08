--------------------------- MODULE OrderRelations ---------------------------

CONSTANTS S, _ \preceq _

(***************************************************************************)
(* Partial orders and total orders                                         *)
(***************************************************************************)

Transitivity ==
    \A s1,s2,s3 \in S : s1 \preceq s2 /\ s2 \preceq s3 => s1 \preceq s3

Antisymmetry ==
    \A s1,s2 \in S : s1 \preceq s2 /\ s2 \preceq s1 <=> s1 = s2

Total ==
    \A s1,s2 \in S : s1 \preceq s2 \/ s2 \preceq s1

IsPartialOrder == Transitivity /\ Antisymmetry

IsTotalOrder == IsPartialOrder /\ Total

(***************************************************************************)
(* Lower bounds and GLB                                                    *)
(***************************************************************************)

IsLB(lb, T) == 
    /\  lb \in S
    /\  \A t \in T : lb \preceq t 

IsGLB(glb, T) ==
    /\  IsLB(glb, T)
    /\  \A s \in S : IsLB(s, T) => s \preceq glb
    
GLB(T) == CHOOSE lb \in S : IsGLB(lb, T)

s1 \sqcap s2 == GLB({s1,s2})

(***************************************************************************)
(* Upper bounds and LUB                                                    *)
(***************************************************************************)

IsUB(ub, T) ==
    /\  ub \in S
    /\  \A t \in T : t \preceq ub

IsLUB(lub, T) ==
    /\  IsUB(lub, T)
    /\  \A s \in S : IsUB(s,T) => lub \preceq s
    
LUB(T) == CHOOSE ub \in S : IsLUB(ub, T)

s1 \sqcup s2 == LUB({s1,s2})

=============================================================================
\* Modification History
\* Last modified Wed Nov 11 15:17:11 EST 2015 by nano
\* Created Wed Nov 11 14:06:04 EST 2015 by nano
