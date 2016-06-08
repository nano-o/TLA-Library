--------------------------- MODULE SequenceUtils ---------------------------

EXTENDS Sequences, Maps, Naturals, Common

IsIncreasing(f) ==
    \A x,y \in DOMAIN f : x <= y => f[x] <= f[y]
    
IsSubSequence(s1, s2) == 
    \E f \in [DOMAIN s1 -> DOMAIN s2] :
        /\  IsInjective(f)
        /\  IsIncreasing(f)
        /\  \A i \in DOMAIN s1 : s1[i] = s2[f[i]]

Last(s) == s[Len(s)]

\* Sequences with no duplicates:
RECURSIVE NoDupRec(_,_)
NoDupRec(es, seen) == 
    IF es = <<>> 
    THEN TRUE 
    ELSE
        IF es[1] \in seen 
        THEN FALSE 
        ELSE NoDupRec(Tail(es), seen \cup {es[1]})
        
NoDup(es) ==
  NoDupRec(es,{})
  
NoDupSeq(E) == 
  {es \in Seq(E) : NoDup(es)}

\* Removing duplicates from a sequence:
RECURSIVE RemDupRec(_,_)
RemDupRec(es, seen) ==
  IF es = <<>>
  THEN <<>>
  ELSE
    IF es[1] \in seen
    THEN RemDupRec(Tail(es), seen)
    ELSE <<es[1]>> \o RemDupRec(Tail(es), seen \cup {es[1]}) 
RemDup(es) == RemDupRec(es, {})

\* Sequence prefix:
Prefix(s1,s2) == 
    /\  Len(s1) <= Len(s2)
    /\  \A i \in DOMAIN s1 : s1[i] = s2[i]

\* The longest common prefix of two sequences:
RECURSIVE LongestCommonPrefixLenRec(_,_,_)
LongestCommonPrefixLenRec(S,n,e1) ==
    IF S = {}
    THEN 0
    ELSE
        IF /\ \A e \in S : Len(e) >= n+1
           /\ \A e \in S : e[n+1] = e1[n+1]
        THEN LongestCommonPrefixLenRec(S,n+1,e1)
        ELSE n
    
LongestCommonPrefixLenSet(S) == LongestCommonPrefixLenRec(S, 0, Some(S))

LongestCommonPrefix(S) ==
    LET n == LongestCommonPrefixLenSet(S)
    IN  IF n = 0
        THEN <<>>
        ELSE [i \in 1..LongestCommonPrefixLenSet(S) |-> Some(S)[i]]
        
=============================================================================
\* Modification History
\* Last modified Wed Jun 08 11:19:59 EDT 2016 by nano
\* Created Wed Jun 08 11:11:31 EDT 2016 by nano
