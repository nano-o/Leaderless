----------------------- MODULE GraphProcessing -----------------------

(***************************************************************************)
(* Processing of a command-dependency graph like in EPaxos.  A local       *)
(* command-dependency graph is expected to be maintained by a node in the  *)
(* form                                                                    *)
(*                                                                         *)
(*      [V -> SUBSET V]                                                    *)
(*                                                                         *)
(* giving for each vertex v its set of neighbors.                          *)
(***************************************************************************)

EXTENDS DiGraph

(***************************************************************************)
(* The set of all graphs of the form                                       *)
(*                                                                         *)
(*     [Vs -> SUBSET V] where Vs \subseteq V                               *)
(***************************************************************************)
Graphs(x) == UNION {[Vs -> SUBSET V] : Vs \in SUBSET V}

(***************************************************************************)
(* Converts a graph g in the form                                          *)
(*                                                                         *)
(*     [Vs -> SUBSET V] where Vs \subseteq V                               *)
(*                                                                         *)
(* to a graph G of the form                                                *)
(*                                                                         *)
(*     SUBSET V \times SUBSET (V \times V)                                 *)
(*                                                                         *)
(* Any vertices v not in the domain of g will not appear in G (even if     *)
(* there is v2 where v \in g[v2]).                                         *)
(***************************************************************************)
ConvertGraph(G) ==
    LET Vs == DOMAIN G
        Es == UNION { {<<v1,v2>> : v2 \in (G[v1] \ {v1}) \cap Vs} : 
            v1 \in DOMAIN G}
    IN <<Vs, Es>>
   
(***************************************************************************)
(* EPaxos graph processing: given a graph G, first build a graph whose     *)
(* nodes are the stronly connected components of G, then make this graph a *)
(* total order TG, then, make organize the vertices of each stronly        *)
(* connected component in a sequence, and finally concatenate all the      *)
(* obtained sequences in the order given by TG.                            *)
(***************************************************************************)
RECURSIVE LinearizeDepsRec(_,_) 
LinearizeDepsRec(s, sccs) ==
    IF sccs # <<>>
    THEN 
        LET vSeq == CHOOSE es \in BSeq(Head(sccs), Cardinality(Head(sccs))) :
                NoDup(es) /\ Len(es) = Cardinality(Head(sccs)) 
        IN LinearizeDepsRec(vSeq \o s, Tail(sccs))
    ELSE s

LinearizeDeps(G) ==
    LET sccSeq == TotalOrder(SCCGraph(G))
    IN  LinearizeDepsRec(<<>>, sccSeq)
    
(***************************************************************************)
(* CanExec(v, g) tests whether all the dependencies of a vertice v have    *)
(* are in the domain of the graph g.  We must have g \in Graphs.           *)
(***************************************************************************)
RECURSIVE CanExecRec(_,_,_)
CanExecRec(v, seen, graph) ==
    /\  v \in DOMAIN graph
    /\  LET deps == graph[v]
        IN \A v2 \in deps : 
            \/  v2 \in seen
            \/  CanExecRec(v2, seen \cup {v2}, graph)
          
CanExec(v, g) == CanExecRec(v, {v}, g)

(***************************************************************************)
(* The part of the graph that does not dominate v.  Takes as parameter a   *)
(* graph in Graphs                                                         *)
(*                                                                         *)
(* The subgraph is of the form                                             *)
(*                                                                         *)
(*     SUBSET V \times SUBSET (V \times V)                                 *)
(***************************************************************************)
SubGraph(v, g) ==
    LET G == ConvertGraph(g)
        Vs == {v2 \in Vertices(G) : \neg
            (Dominates(v2,v,G) /\ \neg Dominates(v,v2,G)) }
        Es == {e \in Edges(G) : e[1] \in Vs /\ e[2] \in Vs}
    IN <<Vs, Es>>
    
(***************************************************************************)
(* The Agreement property: if two values v1 and v2 have all of their       *)
(* dependencies graph (i.e.  can be executed) then if l1 is obtained   *)
(* by linearizing the subgraph of v1 and l2 is obtained by linearizing the *)
(* subgraph of v2 then l2 is a prefix of l1 or vice versa.                 *)
(***************************************************************************)
Agreement(g) == \A v1,v2 \in DOMAIN g :
    (v1 # v2 /\ CanExec(v1, g) /\ CanExec(v2, g))
    => LET  l1 == LinearizeDeps(SubGraph(v1, g))
            l2 == LinearizeDeps(SubGraph(v2, g))
       IN   Prefix(l1,l2) \/ Prefix(l2,l1)

(***************************************************************************)
(* The invariant that EPaxos maintains: two non-commutative commands are   *)
(* necessarily related in the graph.  Here we assume that all command are  *)
(* non-commutative.                                                        *)
(***************************************************************************)
DependencyGraphInvariant(g) == 
    LET G == ConvertGraph(g)
    IN \A v1,v2 \in Vertices(G) :
        v1 # v2 => Dominates(v1, v2, G) \/ Dominates(v2, v1, G)

(***************************************************************************)
(* The safety property of the graph processing algorithm: if the           *)
(* dependency invariant is satisfied in a graph g, then for any two values *)
(* v1 and v2 in the domain of g and whose dependencies are all in the      *)
(* domain of g too then if l1 is obtained by running the graph processing  *)
(* algorithm on the subgraph of g consisting of the nodes not strictly     *)
(* dominating v1 and l2 is obtained by running the graph processing        *)
(* algorithm on the subgraph of g consisting of the nodes not strictly     *)
(* dominating v2, then l1 is a prefix of l2 or vice versa.                 *)
(***************************************************************************)
Safety(x) == \A g \in Graphs(TRUE) : DependencyGraphInvariant(g) => Agreement(g)

THEOREM Safety(TRUE)

SafetyDebug(x) == \A g \in Graphs(TRUE) :
    IF \neg (DependencyGraphInvariant(g) => Agreement(g))
    THEN 
        /\  PrintT(<<"g:", g>>)
        /\  PrintT(<<"ConvertGraph(g):", ConvertGraph(g)>>)
        /\  \A v \in DOMAIN g : PrintT(<<"subgraph", v, SubGraph(v, g)>>)
        /\  FALSE
    ELSE TRUE
    
=============================================================================
\* Modification History
\* Last modified Fri Feb 05 10:11:10 EST 2016 by nano
\* Created Fri Feb 05 09:08:21 EST 2016 by nano
