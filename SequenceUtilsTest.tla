------------------------- MODULE SequenceUtilsTest -------------------------

EXTENDS SequenceUtils

ASSUME IsSubSequence(<<1,2>>,<<1,3,2>>)
ASSUME IsSubSequence(<<1,2>>,<<1,3,3,2>>)
ASSUME IsSubSequence(<<>>,<<1,3,2>>)
ASSUME IsSubSequence(<<>>,<<>>)
ASSUME IsSubSequence(<<1>>,<<1>>)

ASSUME \neg NoDup(<<1,1>>)
ASSUME NoDup(<<1,2>>)
ASSUME RemDup(<<1,1>>) = <<1>>


=============================================================================
\* Modification History
\* Last modified Wed Jun 08 11:23:19 EDT 2016 by nano
\* Created Wed Jun 08 11:14:00 EDT 2016 by nano
