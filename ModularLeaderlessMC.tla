------------------------ MODULE ModularLeaderlessMC ------------------------

EXTENDS GraphProcessing, Common

VARIABLE 
    conss, \* An array of states of consensus instances.
    proposed, \* Maps a value to the sets of dependencies that have been proposed for this value.
    committed, \* Maps a value to its committed set of dependencies.
    state

ConsInterface == INSTANCE ConsensusInterface

(***************************************************************************)
(* Dependency sets                                                         *)
(***************************************************************************)
Deps == SUBSET V

Init == 
    /\ conss = [v \in V |-> ConsInterface!Init]
    /\ proposed = <<>>
    /\ committed = <<>>

(***************************************************************************)
(* Propose dependencies deps for v.                                        *)
(*                                                                         *)
(* We ensure the following invariant: for any two values v1 and v2         *)
(* proposed with deps1 and deps2, either v1 is in deps2 or vice versa.     *)
(***************************************************************************)
Propose(v, deps) ==
    /\ v \notin deps
    /\ conss' = [conss EXCEPT ![v] = 
        [@ EXCEPT !.propose = @ \cup {v}, !.flag = \neg @]]
    \* Ensure the graph invariant:
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
    /\ v \in conss[v].proposed 
    /\ conss[v].decided = None
    /\ conss' = [conss EXCEPT ![v] = [@ EXCEPT !.decided = v, !.flag = \neg @]]
    /\ committed' = [v2 \in DOMAIN committed \cup {v} |-> 
        IF v2 = v THEN IF v2 \in DOMAIN committed 
            THEN committed[v2] \cup {deps}
            ELSE {deps}
        ELSE committed[v2]] 
    /\ UNCHANGED proposed

Next ==
    /\ \E v \in V, deps \in Deps : Propose(v, deps) \/ Decide(v, deps)

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
AtMostOnce == \A v \in DOMAIN committed : Cardinality(committed[v]) = 1
THEOREM Spec => []AtMostOnce

(***************************************************************************)
(* The set of dependencies committed for v (by invariant AtMostOnce, this  *)
(* set is uniquely determined.                                             *)
(***************************************************************************)
TheDeps(v) == CHOOSE deps \in committed[v] : TRUE

Graph(committed_) == [v \in DOMAIN committed_ |-> TheDeps(v)]
       
THEOREM \A f \in LinFunsRec(SUBSET V) : Spec => []Agreement(Graph(committed), f)

=============================================================================
\* Modification History
\* Last modified Tue Feb 09 10:12:55 EST 2016 by nano
\* Created Fri Feb 05 15:02:31 EST 2016 by nano
