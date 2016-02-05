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
    /\  v \notin deps
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
AtMostOnce == \A v \in DOMAIN committed : Cardinality(committed[v]) = 1
THEOREM Spec => []AtMostOnce

(***************************************************************************)
(* The set of dependencies committed for v (by invariant AtMostOnce, this  *)
(* set is uniquely determined.                                             *)
(***************************************************************************)
TheDeps(v, committed_) == CHOOSE deps \in committed_[v] : TRUE

(***************************************************************************)
(* Recursive definition of the CanExec(_,_) operator below.                *)
(***************************************************************************)
RECURSIVE CanExecRec(_,_,_)
CanExecRec(v, seen, committed_) ==
    /\  v \in DOMAIN committed_
    /\  LET deps == TheDeps(v, committed_)
        IN \A v2 \in deps : 
            \/  v2 \in seen
            \/  CanExecRec(v2, seen \cup {v2}, committed_)

(***************************************************************************)
(* Tests whether all the dependencies of a value have been committed.      *)
(***************************************************************************)          
CanExec(v) == CanExecRec(v, {v}, committed)

(***************************************************************************)
(* The part of the graph that does not dominate v.  This graph is of the   *)
(* form                                                                    *)
(*                                                                         *)
(*     SUBSET V \times SUBSET (V \times V)                                 *)
(***************************************************************************)
SubGraph(v, committed_) ==
    LET Graph == ConvertGraph(committed_)
        Vs == {v2 \in Vertices(Graph) : \neg
            Dominates(v2,v,Graph) /\ \neg Dominates(v,v2,Graph) }
        Es == {e \in Edges(Graph) : e[1] \in Vs /\ e[2] \in Vs}
    IN <<Vs, Es>>
    
(***************************************************************************)
(* The Agreement property: if two values v1 and v2 have all of their       *)
(* dependencies committed (i.e.  can be executed) then if l1 is obtained   *)
(* by linearizing the subgraph of v1 and l2 is obtained by linearizing the *)
(* subgraph of v2 then l2 is a prefix of l1 or vice versa.                 *)
(***************************************************************************)
Agreement == \A v1,v2 \in DOMAIN committed :
    (v1 # v2 /\ CanExec(v1) /\ CanExec(v2))
    => LET  l1 == EPaxosLinearization(SubGraph(v1, committed))
            l2 == EPaxosLinearization(SubGraph(v2, committed))
       IN   Prefix(l1,l2) \/ Prefix(l2,l1)
THEOREM Spec => []Agreement

=============================================================================
\* Modification History
\* Last modified Fri Feb 05 08:46:57 EST 2016 by nano
\* Created Thu Feb 04 12:27:45 EST 2016 by nano