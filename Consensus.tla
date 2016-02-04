----------------------------- MODULE Consensus -----------------------------

EXTENDS Common

VARIABLES state

Interface == INSTANCE ConsensusInterface

Init == Interface!Init(state)

Decide(v) == 
    /\  v \in state.proposed 
    /\  state.decided = None
    /\  Interface!Decide(v, state, state')

Propose(v) == Interface!Propose(v, state, state')

Next == \E v \in V : Decide(v) \/ Propose(v)

Spec == Init /\ [][Next]_<<state>>

THEOREM Spec => [](\A v \in V : state.decided = v => [](state.decided = v))

=============================================================================
\* Modification History
\* Last modified Thu Feb 04 18:46:41 EST 2016 by nano
\* Created Thu Feb 04 16:14:26 EST 2016 by nano
