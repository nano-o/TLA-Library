------------------------- MODULE LexicographicOrder -------------------------

EXTENDS Sequences

CONSTANT geq(_, _) 

RECURSIVE LexGeq(_,_)
LexGeq(v1, v2) ==
    IF Len(v1) = 1 THEN geq(v1[1], v2[1]) 
    ELSE 
        IF v1[1] = v2[1] THEN LexGeq(Tail(v1), Tail(v2))
        ELSE geq(v1[1], v2[1])

=============================================================================
\* Modification History
\* Last modified Fri Feb 17 18:27:41 PST 2017 by nano
\* Created Fri Feb 17 18:25:16 PST 2017 by nano
