-------------------------------- MODULE Maps --------------------------------

(***************************************************************************)
(* Adding a key-value mapping (kv[1] is the key, kv[2] the value) to a map *)
(***************************************************************************)
f ++ kv == [x \in DOMAIN f \union {kv[1]} |-> IF x = kv[1] THEN kv[2] ELSE f[x]]

(***************************************************************************)
(* The image of a map                                                      *)
(***************************************************************************)
Image(f) == {f[x] : x \in DOMAIN f}

IsBijection(f, X, Y) ==
    /\  DOMAIN f = X 
    /\  Image(f) = Y
    /\  \A x,y \in X : x # y => f[x] # f[y]
    /\  \A y \in Y : \E x \in X : f[x] = y

IsInjective(f) == \A x,y \in DOMAIN f : x # y => f[x] # f[y]


=============================================================================
\* Modification History
\* Last modified Wed Jun 08 11:17:10 EDT 2016 by nano
\* Created Mon May 02 21:01:30 EDT 2016 by nano
