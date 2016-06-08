------------------------------ MODULE CStruct ------------------------------

(***************************************************************************)
(* Lamport's CStructs.  See the paper "Generalized Consensus and Paxos".   *)
(***************************************************************************)

EXTENDS Sequences, Misc

CONSTANTS Cmd, CStruct, _ \bullet _, Bottom

(***************************************************************************)
(* Appending a sequence of commands to a CStruct                           *)
(***************************************************************************)
RECURSIVE StarRec(_,_)
StarRec(s, cs) ==
    IF cs = <<>>    
    THEN s
    ELSE StarRec(s \bullet Head(cs), Tail(cs))
    
s \star cs == StarRec(s, cs)

Str(C) == {Bottom \star cs : cs \in Seq(C)}

s \preceq t ==
    \/  /\  s \in CStruct
        /\  t \in CStruct
        /\  \E cs \in Seq(Cmd) : t = s \star cs
    \/  /\  s = None(CStruct)
        /\  t = None(CStruct)

s \sqsubset t ==
    /\  s \preceq t
    /\  s # t

INSTANCE OrderRelations WITH S <- CStruct

Compat(s,t) == 
    \E ub \in CStruct : IsUB(ub, {s,t})

IsCompatible(S) == 
    \A s,t \in S : Compat(s,t)

Contains(s, c) == 
    \E cs1,cs2 \in Seq(Cmd) : c = ((Bottom \star cs1) \bullet c) \star cs2

CS0 ==
    \A s \in CStruct, c \in Cmd : s \bullet c \in CStruct

CS1 ==
    CStruct = Str(Cmd)
    
CS2 == IsPartialOrder

CS3 == 
    \A P \in SUBSET Cmd \ {{}} :
        /\ \A s,t \in Str(P) :
            /\  s \sqcap t \in Str(P)
            /\  IsGLB(s \sqcap t, {s,t}) \* GLB exists
            /\  Compat(s,t) =>
                    /\  s \sqcup t \in Str(P)
                    /\  IsLUB(s \sqcup t, {s,t}) \* LUB exists

CS4 ==
    \A s,t \in CStruct, c \in Cmd :
        Compat(s,t) /\ Contains(s,c) /\ Contains(t,c) =>
            Contains(s \sqcap t, c)

IsCStruct == CS0 /\ CS1 /\ CS2 /\ CS3 /\ CS4 

=============================================================================
\* Modification History
\* Last modified Wed Jun 08 11:30:23 EDT 2016 by nano
\* Created Wed Nov 11 14:21:02 EST 2015 by nano
