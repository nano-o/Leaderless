----------------------------- MODULE Consensus -----------------------------

CONSTANT V

VARIABLES proposed, decided

None == CHOOSE x : x \notin V

Init == proposed = {} /\ decided = None

Propose(v) ==
    /\  proposed' = proposed \cup {v}
    /\  UNCHANGED decided

Decide == 
    /\  decided = None
    /\  \E v \in proposed : decided' = v
    /\  UNCHANGED proposed

Next == Decide \/ \E v \in V : Propose(v)

Spec == Init /\ [][Next]_<<proposed, decided>>

THEOREM Spec => [](\A v \in V : decided = v => [](decided = v))

=============================================================================
\* Modification History
\* Last modified Thu Feb 04 16:44:51 EST 2016 by nano
\* Created Thu Feb 04 16:14:26 EST 2016 by nano
