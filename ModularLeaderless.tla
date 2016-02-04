------------------------- MODULE ModularLeaderless -------------------------

EXTENDS DiGraph, Common

VARIABLE 
    conss, \* An array of states of consensus instances
    proposed, \* Maps a value to the sets of dependencies that have been proposed for this value.
    committed \* Maps a value to its committed set of dependencies.

(***************************************************************************)
(* Dependency sets                                                         *)
(***************************************************************************)
Deps == SUBSET V

(***************************************************************************)
(* Consensus instances to decide on dependency sets                        *)
(***************************************************************************)
ConsInst == INSTANCE ConsensusInterface WITH V <- Deps

Init == 
    /\ conss = [v \in V |-> 
        CHOOSE s \in ConsInst!State : ConsInst!Init(s)]
    /\ proposed = <<>>
    /\ committed = <<>>

(***************************************************************************)
(* Propose dependencies deps for v.                                        *)
(*                                                                         *)
(* We ensure the following invariant: for any two values v1 and v2         *)
(* proposed with deps1 and deps2, either v1 is in deps2 or vice versa.     *)
(***************************************************************************)
Propose(v, deps) ==
    /\ \E s \in ConsInst!State : 
        /\ ConsInst!Propose(deps, conss[v], s)
        /\ conss' = [conss EXCEPT ![v] = s]
    /\ \A v2 \in DOMAIN proposed : v2 # v => 
            \A deps2 \in proposed[v2] : v \in deps2 \/ v2 \in deps  
    /\ proposed' = [v2 \in DOMAIN proposed \cup {v} |-> 
        IF v2 = v THEN 
            IF v \in DOMAIN proposed 
            THEN proposed[v] \cup {deps}
            ELSE {deps}
        ELSE proposed[v2]]
    /\  UNCHANGED committed

Decide(v, deps) ==
    /\ \E s \in ConsInst!State :
        /\  ConsInst!Decide(deps, conss[v], s)
        /\  conss' = [conss EXCEPT ![v] = s]
    /\ committed' = [v2 \in DOMAIN committed \cup {v} |-> 
        IF v2 = v THEN IF v2 \in DOMAIN committed 
            THEN committed[v2] \cup {deps}
            ELSE {deps}
        ELSE committed[v2]] 
    /\ UNCHANGED proposed

Cons(state) == INSTANCE Consensus WITH V <- Deps

Next ==
    /\ \E v \in V, deps \in Deps : Propose(v, deps) \/ Decide(v, deps)
    /\ \E v \in V : Cons(conss[v])!Next

Spec == Init /\[][Next]_conss

(***************************************************************************)
(* A decision never changes                                                *)
(***************************************************************************)
DecisionIrrevocable == [](\A v \in V : \A deps \in Deps : conss[v].decided = deps 
    => [](conss[v].decided = deps))
THEOREM Spec => DecisionIrrevocable

(***************************************************************************)
(* A command is committed at most once                                     *)
(***************************************************************************)
AtMostOnce == \A v \in V : v \in DOMAIN committed 
    => Cardinality(committed[v]) = 1
THEOREM Spec => []AtMostOnce

=============================================================================
\* Modification History
\* Last modified Thu Feb 04 18:34:18 EST 2016 by nano
\* Created Thu Feb 04 12:27:45 EST 2016 by nano