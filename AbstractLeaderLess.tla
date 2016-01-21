--------------------------- MODULE AbstractLeaderLess -----------------------

(* Author: Giuliano Losa *)

(***************************************************************************)
(* This is a specification to test the basic ideas behind algorithms of    *)
(* the EPaxos family.  The specification is abstract (for example we don't *)
(* model the network) but should still exhibit interesting behaviors.  A   *)
(* process proposes at most one request, therefore we don't use instance   *)
(* numbers or commands: the identifier of a process acts as both instance  *)
(* number and command (this reduces the state-space).                      *)
(*                                                                         *)
(* We specify the fast path, the slow path, and the execution algorithm.   *)
(* However, the crash-recovery mechanism has not been formalized.          *)
(*                                                                         *)
(* The correctness of the algorithm seems to be based on the following     *)
(* invariants:                                                             *)
(*                                                                         *)
(* Inv1: For each instance i, every process agrees on the request          *)
(* committed at i and on its set of dependencies.                          *)
(*                                                                         *)
(* Inv2: For every request r that can be executed (all its dependencies    *)
(* are committed), for every requests r1 and r2 appearing in Graph(r,      *)
(* committed), either <<r1,r2>> \in G or <<r2,r1>> \in G (or both).        *)
(*                                                                         *)
(* Does Inv1 /\ Inv2 imply the agreement property?                         *)
(*                                                                         *)
(* Inv1 is ensured by running a traditional consensus algorithm.           *)
(*                                                                         *)
(* Inv2 is ensured by proposing depencies collected from a classic quorum. *)
(* Why does Inv2 hold? Consider two requests r1 and r2.  Since two classic *)
(* quorums intersect on at least one replica r, it is ensured that the     *)
(* request received last by r, say r2, will have the one received first,   *)
(* r1, in its dependencies.                                                *)
(*                                                                         *)
(* Inv1 and Inv2 ensure that for every request r that can be executed, the *)
(* dependency graph of r is a sequence of strongly connected components    *)
(* and that if r1 and r2 can both be executed, then the sequence of        *)
(* strongly connected components corresponding to r1's graph is a prefix   *)
(* of the one of r2, or vice-versa.                                        *)
(*                                                                         *)
(***************************************************************************)

EXTENDS FiniteSets

CONSTANT
    P, \* The processes
    FastQuorum, \* The set of all fast quorums
    ClassicQuorum \* The set of all classic quorums

(***************************************************************************)
(* Variables:                                                              *)
(*                                                                         *)
(* slowPath[p] is null or <<r, deps>>, indicating that p started the slow  *)
(* path for request r with dependencies deps.                              *)
(*                                                                         *)
(* preAccepted[p] is a set of pairs of the form <<r, deps>> where r has    *)
(* been preaccepted by p with dependencies deps.                           *)
(*                                                                         *)
(* accepted[p] is a set of pairs of the form <<r, deps>> where r has been  *)
(* accepted by p with dependencies deps.                                   *)
(*                                                                         *)
(* committed is a set of pairs of the form <<r, deps>> where r has been    *)
(* committed with dependencies deps.                                       *)
(*                                                                         *)
(* pending[p] is null or contains the pending request of p if p has one    *)
(***************************************************************************)
VARIABLES
    slowPath,
    preAccepted,
    accepted,
    committed,
    pending

vars == <<pending, preAccepted, accepted, committed, slowPath>>

(***************************************************************************)
(* Since every process will only propose a single command, we let the set  *)
(* of requests be the set of processes                                     *)
(***************************************************************************)
Req == P

(***************************************************************************)
(* We will use directed graphs over the set of requests to represent the   *)
(* interdependencies among requests.                                       *)
(***************************************************************************)
INSTANCE DiGraph WITH V <- Req


(***************************************************************************)
(* Pairs consisting of a request and a set of dependencies.                *)
(***************************************************************************)
ReqWithDeps == Req \X SUBSET Req

(***************************************************************************)
(* A null value that is no a request nor an element of ReqWithDeps         *)
(***************************************************************************)
null == CHOOSE n : n \notin (Req \cup ReqWithDeps) 

(***************************************************************************)
(* Invariant describing the type of the variables                          *)
(***************************************************************************)
TypeInvariant ==
        /\ \A p \in P :
            /\  pending[p] \in {null} \cup Req
            /\  preAccepted[p] \in SUBSET ReqWithDeps
            /\  accepted[p] \in SUBSET ReqWithDeps
            /\  slowPath[p] \in {null} \cup ReqWithDeps
        /\ committed \in SUBSET ReqWithDeps
        
(***************************************************************************)
(* Predicate describing the initial state of the system.                   *)
(***************************************************************************)
Init ==
    /\ pending = [p \in P |-> null]
    /\ preAccepted = [p \in P |-> {}]
    /\ accepted = [p \in P |-> {}]
    /\ committed = {}
    /\ slowPath = [p \in P |-> null]

(***************************************************************************)
(* The set of requests that process p has seen so far.                     *)
(***************************************************************************)
Seen(p) ==
    { rd[1] : rd \in preAccepted[p] \cup accepted[p] }
        \cup (IF pending[p] \in Req THEN {pending[p]} ELSE {})

(***************************************************************************)
(* Process p proposes a new request.                                       *)
(***************************************************************************)
Request(p) ==
    LET r == p
        prop == <<r, Seen(p)>> IN
    /\ pending[p] = null \* Only propose a request if none is pending
    /\ pending' = [pending EXCEPT ![p] = r]
    /\ UNCHANGED <<preAccepted, accepted, committed, slowPath>>

(***************************************************************************)
(* Process p pre-accepts a request from process q.                         *)
(***************************************************************************)
PreAccept(p) ==
    /\  \E q \in P : 
            /\  pending[q] \in Req \* we preaccept q's request
            /\  \A r \in Seen(p) : r # pending[q] \* p has not seen r
            /\  preAccepted' = [preAccepted EXCEPT ![p] = 
                    @ \cup {<<pending[q], Seen(p)>>}]
    /\  UNCHANGED <<pending, accepted, committed, slowPath>>

(***************************************************************************)
(* Process p commits its pending request in the fast path.                 *)
(***************************************************************************)
FastCommit(p) ==
    /\  slowPath[p] = null
    /\  \E q \in P : \E rd \in preAccepted[q] :
        /\  rd[1] = pending[p]
        /\  \E Q \in FastQuorum : 
                \A q2 \in Q : rd \in preAccepted[q2]
        /\  committed' = committed \cup {rd}
    /\  UNCHANGED <<pending, preAccepted, accepted, slowPath>>

(***************************************************************************)
(* TRUE when process p has pre-accepted request r                          *)
(***************************************************************************)
PreAccepted(p, r) == \E rd \in preAccepted[p] : rd[1] = r

(***************************************************************************)
(* Process p starts the slow path for its pending requests.                *)
(***************************************************************************)
SlowPath(p) ==
    /\  slowPath[p] = null
    /\  \E Q \in FastQuorum : 
            /\  \A q \in Q : PreAccepted(q, pending[p])
            /\  LET rds == { rd \in UNION { preAccepted[q] : 
                        q \in Q } : rd[1] = pending[p] } 
                IN  slowPath' = [slowPath EXCEPT ![p] = 
                        <<pending[p], UNION { rd[2] : rd \in rds } >> ] 
    /\ UNCHANGED <<pending, preAccepted, accepted, committed>>

(***************************************************************************)
(* Process p accepts a request from process q in the slow path (with the   *)
(* dependencies calculated by q.)                                          *)
(***************************************************************************)
Accept(p) ==
    /\  \E q \in P :
        /\  slowPath[q] # null
        /\  accepted' = [accepted EXCEPT ![p] = @ \cup { slowPath[q] } ]
    /\  UNCHANGED <<slowPath, pending, preAccepted, committed>>

(***************************************************************************)
(* Process p commits its pending request in the slow path.                 *)
(*                                                                         *)
(* TODO: when there will be a recovery path, this will not ensure Inv1.    *)
(* We may need to check for the intersection with a fast quorum among the  *)
(* classic quorum.                                                         *)
(***************************************************************************)
SlowCommit(p) ==
    /\  slowPath[p] # null
    /\  \E Q \in ClassicQuorum : \A q \in Q :
            slowPath[p] \in accepted[q]
    /\  committed' = committed \cup { slowPath[p] }
    /\  UNCHANGED <<slowPath, pending, preAccepted, accepted>>
            
(***************************************************************************)
(* Recursive definition of the CanExec(_,_) operator below.                *)
(***************************************************************************)
RECURSIVE CanExecRec(_,_,_)
CanExecRec(r, seen1, cs) ==
    \E a \in cs : 
        /\  a[1] = r
        /\  \A s \in a[2] : 
            \/  s \in seen1 
            \/ CanExecRec(s, seen1 \cup {s}, cs)

(***************************************************************************)
(* Tests whether all the dependencies of a request have been committed.    *)
(***************************************************************************)          
CanExec(r, cs) == CanExecRec(r, {r}, cs)

(***************************************************************************)
(* Recursive definition of the Graph(_,_) operator below.                  *)
(***************************************************************************)
RECURSIVE GraphRec(_,_,_)
GraphRec(r, seen1, cs) ==
    LET deps == (CHOOSE y \in cs : y[1] = r)[2] \* get the deps of r
    IN  {<<r, z>> : z \in deps} \cup
            UNION { GraphRec(z, seen1 \cup deps, cs) : z \in deps \ seen1}
        
(***************************************************************************)
(* The dependency graph of request r, given the set of commited requests   *)
(* and their dependencies                                                  *)
(***************************************************************************)
Graph(r, cs) == GraphRec(r, {r}, cs)

(***************************************************************************)
(* The next-state relation                                                 *)
(***************************************************************************)
Next == \E p \in P :
    \/ Request(p)
    \/ PreAccept(p)
    \/ FastCommit(p)
    \/ SlowPath(p)
    \/ Accept(p)
    \/ SlowCommit(p)

(***************************************************************************)
(* The agreement property.                                                 *)
(*                                                                         *)
(* Says that for all commands x and y, if x and y are different and both   *)
(* can be executed (i.e.  all their deps are commited), then the           *)
(* linearization of x's subgraph is a prefix of the linearization of y's   *)
(* subgraph, or vice versa.                                                *)
(*                                                                         *)
(***************************************************************************)
Agreement(cs) == 
    \/  Cardinality(cs) < 2
    \/  \A x,y \in cs :
            \/  x = y
            \/  ~(CanExec(x[1], cs) /\ CanExec(y[1], cs))
            \/  LET l1 == Linearization(Graph(x[1], cs))
                    l2 == Linearization(Graph(y[1], cs))
                IN  Prefix(l1,l2) \/ Prefix(l2,l1)
(***************************************************************************)
(* Note that Linearization(Graph(r, committed)), for a request r that can  *)
(* be executed, is what a process would obtain when locally executing      *)
(* request r.                                                              *)
(*                                                                         *)
(* TODO: This is not entirely accurate: consider the two following graphs: *)
(*                                                                         *)
(*     G1 == {<<1,2>>,<<2,1>>} and G2 == {<<1,2>>,<<2,1>>,<<3,2>>}         *)
(*                                                                         *)
(* With the current definition of Linearization and according to the       *)
(* semantics of TLA+, it would be possible that Linearization(G1) =        *)
(* <<1,2>> and Linearization(G2) == <<2,1,3>>.  However, TLC seem to       *)
(* resolve the nondeterminism of the semantics of TLA+ in our favor, and   *)
(* it works: no need to fix it for now.                                    *)
(*                                                                         *)
(* To fix this problem we need to linearize each strongly connected        *)
(* component separately, since those are guaranteed never to change when   *)
(* the graph grows.                                                        *)
(*                                                                         *)
(* More concretely: change the definition of                               *)
(* StronglyConnectedComponents(_) to include lone nodes; from G, build a   *)
(* graph whose vertices are the strongly connected components of G, in the *)
(* topological order defined by G; at this point the graph should be a     *)
(* sequence (by Inv2); linearize each strongly connected composnent        *)
(* separately and concatenate the results.                                 *)
(***************************************************************************)


(***************************************************************************)
(* The full specification                                                  *)
(***************************************************************************)
Spec == Init /\ [][Next]_vars

THEOREM Spec => []Agreement(committed)

=============================================================================
\* Modification History
\* Last modified Thu Jan 21 00:53:45 EST 2016 by nano
\* Created Wed Aug 12 08:12:23 EDT 2015 by nano
