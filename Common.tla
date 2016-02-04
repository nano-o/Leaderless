------------------------------- MODULE Common -------------------------------

EXTENDS Naturals, TLC

CONSTANT V
None == CHOOSE x : x \notin V
 

(***************************************************************************)
(* For TLC                                                                 *)
(***************************************************************************)
CONSTANT MaxSeq \* A set for containing model values (for TLC).
BSeq(X, b) == {<<>>} \cup UNION {[1..n -> X] : n \in 1..b}

=============================================================================
\* Modification History
\* Last modified Thu Feb 04 17:03:30 EST 2016 by nano
\* Created Thu Feb 04 16:55:11 EST 2016 by nano
