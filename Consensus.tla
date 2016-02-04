----------------------------- MODULE Consensus -----------------------------

EXTENDS Common

VARIABLES state

Interface == INSTANCE ConsensusInterface

Init == Interface!Init(state)

Decide(v) == 
    /\  state.decided = None
    /\  \E s \in Interface!State : 
            /\  Interface!Decide(v, state, s)
            /\  state' = s

Propose(v) == \E s \in Interface!State : 
        /\  Interface!Propose(v, state, s)
        /\  state' = s

Next == \E v \in V : Decide(v) \/ Propose(v)

Spec == Init /\ [][Next]_<<state>>

THEOREM Spec => [](\A v \in V : state.decided = v => [](state.decided = v))

=============================================================================
\* Modification History
\* Last modified Thu Feb 04 17:54:29 EST 2016 by nano
\* Created Thu Feb 04 16:14:26 EST 2016 by nano
