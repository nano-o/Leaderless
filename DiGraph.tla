------------------------------ MODULE DiGraph ------------------------------

(***************************************************************************)
(* A formalization of directed graphs.  Many definitions are recursive     *)
(* because TLC can evaluate them more efficiently than their more          *)
(* declarative counterpart (e.g.  CHOOSE x \in X : P(x)).                  *)
(***************************************************************************)

EXTENDS FiniteSets, Sequences, Naturals, Common

Image(f) == {f[x] : x \in DOMAIN f}

(***************************************************************************)
(* Prefix relation on sequences                                            *)
(***************************************************************************)
Prefix(s1,s2) == 
    /\  Len(s1) <= Len(s2)
    /\  \A i \in DOMAIN s1 : s1[i] = s2[i]

(***************************************************************************)
(* Sequences with no duplicates:                                           *)
(***************************************************************************)
RECURSIVE NoDupRec(_,_)
NoDupRec(es, seen) == 
    IF es = <<>> 
    THEN TRUE 
    ELSE
        IF es[1] \in seen 
        THEN FALSE 
        ELSE NoDupRec(Tail(es), seen \cup {es[1]})
        
NoDup(es) == 
  NoDupRec(es,{})

(***************************************************************************)
(* The declarative version of NoDup(_).                                    *)
(***************************************************************************)
NoDup2(es) == \A i,j \in DOMAIN es : i # j => es[i] # es[j]

THEOREM \A es \in Seq(Nat) : NoDup(es) = NoDup2(es) 

(***************************************************************************)
(* A digraph is a set of vertices and a set of edges, where an edge is a   *)
(* pair of vertices.                                                       *)
(***************************************************************************)
Vertices(G) == G[1]
Edges(G) == G[2]
IsDigraph(G) == Edges(G) \subseteq (Vertices(G) \times Vertices(G))

(***************************************************************************)
(* Recursive implementation of Dominates(v1,v2,G).                         *)
(***************************************************************************)
RECURSIVE DominatesRec(_,_,_,_)
DominatesRec(v1, v2, G, acc) ==
    \/ <<v1,v2>> \in Edges(G)
    \/ \E v \in Vertices(G) : 
        /\ \neg v \in acc
        /\ <<v1,v>> \in Edges(G)
        /\ DominatesRec(v, v2, G, acc \cup {v1}) 

(***************************************************************************)
(* True when there exists a path from v1 to v2 in the graph G              *)
(***************************************************************************)
Dominates(v1, v2, G) ==
    DominatesRec(v1,v2,G,{})

(***************************************************************************)
(* The topological order among vertices of the graph G.                    *)
(***************************************************************************)
TopologicalOrder(G) ==
    {<<v1,v2>> \in Vertices(G) \times Vertices(G) : 
        \neg Dominates(v1,v2,G) /\ Dominates(v2,v1,G)}
    
HasCycle(G) ==
    \E v1,v2 \in Vertices(G) : 
        /\  v1 # v2
        /\  Dominates(v1, v2, G)
        /\  Dominates(v2, v1, G)    

IsCycle(path) ==
    /\  Len(path) > 1
    /\  path[1] = path[Len(path)]

(***************************************************************************)
(* All the paths of length smaller or equal to n in graph G                *)
(***************************************************************************)
RECURSIVE Paths(_, _)
Paths(n, G) ==
    IF n = 1
    THEN 
        Edges(G)
    ELSE
        LET nextVs(p) == 
                { e[2] : e \in {e \in Edges(G) : e[1] = p[Len(p)]} }
            nextPaths(p) == { Append(p,v) : v \in nextVs(p) }
        IN
            UNION { nextPaths(p) : p \in Paths(n-1, G)}
            \cup Paths(n-1, G)
             
(***************************************************************************)
(* All cycles in G, includes all permutations of a given cycle.            *)
(***************************************************************************)   
Cycles2(G) ==
    { p \in Paths(Cardinality(Vertices(G))+1, G) : 
        IsCycle(p) /\ NoDup([i \in 1..(Len(p)-1) |-> p[i]]) }

CompleteSubGraphs(G) == 
    {W \in SUBSET Vertices(G) :
        /\  Cardinality(W) > 1 
        /\  \A v1,v2 \in W : 
                \/  v1 = v2 
                \/ (<<v1,v2>> \in Edges(G) /\ <<v2,v1>> \in Edges(G))}

IsMaximal(X, Xs) == \A Y \in Xs : X = Y \/ ~(X \subseteq Y)

Cliques(G) ==
    {W \in CompleteSubGraphs(G) : IsMaximal(W, CompleteSubGraphs(G))}

\* SC subgraphs as set of vertices
StronglyConnectedSubgraphs(G) ==
    {W \in SUBSET Vertices(G) : W # {} /\ \A v1,v2 \in W : 
        v1 = v2 \/ Dominates(v1,v2,G)}

(***************************************************************************)
(* The strongly connected components of G.                                 *)
(***************************************************************************)
SCCs(G) == {W \in StronglyConnectedSubgraphs(G) : 
    IsMaximal(W, StronglyConnectedSubgraphs(G))}

(***************************************************************************)
(* The graph formed by the strongly connected components of G and their    *)
(* topological ordering.                                                   *)
(***************************************************************************)
SCCGraph(G) == 
    LET edges == 
        {<<sc1, sc2>> \in SCCs(G) \times SCCs(G) :
            /\  \E v1 \in sc1, v2 \in sc2 :
                    <<v1,v2>> \in Edges(G)
            /\  sc1 # sc2}
    IN <<SCCs(G), edges>>
        

(***************************************************************************)
(* A sequence of vertices such that if v1 is related to v2 in the          *)
(* topological order of the graph G, then v2 appears before v1 in the      *)
(* sequence.  In other words, a total order compatible with the partial    *)
(* order given by the graph.                                               *)
(***************************************************************************)
TotalOrder(G) ==
    CHOOSE s \in BSeq(Vertices(G), Cardinality(Vertices(G))) :
        /\ NoDup(s) 
        /\ \A v \in Vertices(G) : \E i \in DOMAIN s : s[i] = v
        /\ \A i,j \in DOMAIN s : <<s[i],s[j]>> \in TopologicalOrder(G) => j < i


=============================================================================
\* Modification History
\* Last modified Tue Feb 09 09:13:23 EST 2016 by nano
\* Created Tue Jul 28 03:10:02 CEST 2015 by nano
