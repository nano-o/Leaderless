------------------------- MODULE ModularLeaderless -------------------------

EXTENDS DiGraph, Common

VARIABLE 
    conss \* An array of states of consensus instances

Deps == SUBSET V

(***************************************************************************)
(* Consensus instances to decide on dependency sets                        *)
(***************************************************************************)
ConsInst == INSTANCE ConsensusInterface WITH V <- Deps

Init == conss = [v \in V |-> 
    CHOOSE s \in ConsInst!State : ConsInst!Init(s)]

(***************************************************************************)
(* Propose dependencies deps for v                                         *)
(***************************************************************************)
Propose(v, deps) ==
    \E s \in ConsInst!State : 
        /\  ConsInst!Propose(deps, conss[v], s)
        /\  conss' = [conss EXCEPT ![v] = s]

Decide(v, deps) ==
    \E s \in ConsInst!State :
        /\  ConsInst!Decide(deps, conss[v], s)
        /\  conss' = [conss EXCEPT ![v] = s]

Cons(state) == INSTANCE Consensus WITH V <- Deps

Next ==
    /\ \E v \in V, deps \in Deps : Propose(v, deps) \/ Decide(v, deps)
    /\ \E v \in V : Cons(conss[v])!Next

Spec == Init /\[][Next]_conss

(***************************************************************************)
(* A decision cannot change                                                *)
(***************************************************************************)
THEOREM [](\A v \in V : \A deps \in Deps : conss[v].decided = deps => [](conss[v].decided = deps))

=============================================================================
\* Modification History
\* Last modified Thu Feb 04 17:56:15 EST 2016 by nano
\* Created Thu Feb 04 12:27:45 EST 2016 by nano
