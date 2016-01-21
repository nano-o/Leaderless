------------------------------ MODULE DiGraph ------------------------------

(***************************************************************************)
(* A formalization of directed graphs.  Many definitions are recursive     *)
(* because TLC can evaluate them more efficiently than their more          *)
(* declarative counterpare (e.g.  CHOOSE x \in X : P(x)).                  *)
(***************************************************************************)

EXTENDS FiniteSets, Sequences, Naturals, TLC

CONSTANT V \* Set of vertices

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
(* A digraph is a set of edges, where an edge is a pair of vertices.       *)
(***************************************************************************)
IsDigraph(G) == 
    G \in SUBSET (V \times V)
    
(***************************************************************************)
(* Recursive implementation of Dominates(v1,v2,G).                         *)
(***************************************************************************)
RECURSIVE DominatesRec(_,_,_,_)
DominatesRec(v1,v2,G,acc) ==
    \/ <<v1,v2>> \in G
    \/ \E v \in V : 
        /\ \neg v \in acc
        /\ <<v1,v>> \in G
        /\ DominatesRec(v,v2,G,acc \cup {v1}) 

(***************************************************************************)
(* True when there exists a path from v1 to v2 in the graph G              *)
(***************************************************************************)
Dominates(v1, v2, G) ==
    DominatesRec(v1,v2,G,{})

(***************************************************************************)
(* The topological order among vertices of the graph G.                    *)
(***************************************************************************)
TopologicalOrder(G) ==
    {<<v1,v2>> \in V \times V : Dominates(v1,v2,G) /\ \neg Dominates(v2,v1,G)}
    
(***************************************************************************)
(* The set of all the vertices of G                                        *)
(***************************************************************************)
Vertices(G) ==
    {v \in V : \E v2 \in V : <<v,v2>> \in G \/ <<v2,v>> \in G}

(***************************************************************************)
(* A sequence of vertices such that if v1 is related to v2 in the          *)
(* topological order of the graph G, then v2 appears before v1 in the      *)
(* sequence.                                                               *)
(***************************************************************************)
Linearization(G) ==
    CHOOSE s \in Seq(V) : 
        /\ \A i \in DOMAIN s : s[i] \in Vertices(G)
        /\ \A v \in Vertices(G) : \E i \in DOMAIN s : s[i] = v
        /\ \A i,j \in DOMAIN s : <<s[i],s[j]>> \in TopologicalOrder(G) => j < i 

(***************************************************************************)
(* Below this comment is a set of definition that I used for debugging     *)
(* purposes.                                                               *)
(***************************************************************************)
    
HasCycle(G) ==
    \E v1,v2 \in Vertices(G) : 
        /\  v1 # v2
        /\  Dominates(v1, v2, G)
        /\  Dominates(v2, v1, G)    

ExtractCycle(path) ==
    LET i == CHOOSE j \in DOMAIN(path) : j # Len(path) /\ path[j] = path[Len(path)]
    IN [j \in 1..(Len(path)-i+1) |-> path[j+i-1]]

(***************************************************************************)
(* All cycles reachable from the last vertex of the given path, excluding  *)
(* from the graph the vertices in vs.                                      *)
(***************************************************************************)
RECURSIVE
CyclesFrom(_,_,_)
CyclesFrom(path, G, vs) ==
    LET lastV == path[Len(path)] \* The last vertex of the path
        \* The edges starting from the last vertex of the path which do not lead to a vertex in vs:
        nextEdges == {e \in G : e[1] = lastV /\ e[2] \notin vs} 
        \* The edges in nextEdges which bring back to some vertex of the path:
        cycleEdges == {e \in nextEdges : e[2] \in Image(path)}
        \* The cycles obtained in one step from path:
        cycles == {ExtractCycle(Append(path, e[2])) : e \in cycleEdges}
        \* The results of the recursive calls
        recResults == {CyclesFrom(p, G, vs) : p \in { Append(path, e[2]) : e \in nextEdges \ cycleEdges}}
        \* The cycles obtained in the recursive calls:
        recCycles == UNION {result[1] : result \in recResults}
        \* The vertices visisted by the recursive calls:
        recAcc == UNION {result[2] : result \in recResults}
    \* Return the cycles and the set of vertices visited
    IN  <<cycles \cup recCycles, {e[2] : e \in nextEdges \ cycleEdges} \cup recAcc>>
    
(***************************************************************************)
(* Cycles(G,{}) is the set of cycles found in the graph G.                 *)
(***************************************************************************)
RECURSIVE 
CyclesRec(_,_)
CyclesRec(G, acc) ==
    IF \E w \in Vertices(G) : w \notin acc
    THEN
        LET v == CHOOSE w \in Vertices(G) : w \notin acc
            x == CyclesFrom(<<v>>, G, acc)
            visited == acc \cup x[2] \cup {v}
            otherCycles == CyclesRec(G, visited)
        IN x[1] \cup otherCycles
    ELSE {} 

Cycles(G) == CyclesRec(G, {})
\* TODO: why not enumerate all paths and check for cycles?

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
        G
    ELSE
        LET nextVs(p) == 
                { e[2] : e \in {e \in G : e[1] = p[Len(p)]} }
            nextPaths(p) == { Append(p,v) : v \in nextVs(p) }
        IN
            UNION { nextPaths(p) : p \in Paths(n-1, G)}
            \cup Paths(n-1, G)
                
Cycles2(G) ==
    { p \in Paths(Cardinality(V)+1, G) : IsCycle(p) /\ NoDup([i \in 1..(Len(p)-1) |-> p[i]]) }
    

CompleteSubGraphs(G) == 
    {W \in SUBSET Vertices(G) :
        /\  Cardinality(W) > 1 
        /\  \A v1,v2 \in W : v1 = v2 \/ (<<v1,v2>> \in G /\ <<v2,v1>> \in G)}

IsMaximal(X, Xs) == \A Y \in Xs : X = Y \/ ~(X \subseteq Y)

Cliques(G) ==
    {W \in CompleteSubGraphs(G) : IsMaximal(W, CompleteSubGraphs(G))}

StronglyConnectedSubgraphs(G) ==
    {W \in SUBSET Vertices(G) : Cardinality(W) > 1 /\ \A v1,v2 \in W : v1 = v2 \/ Dominates(v1,v2,G)}

StronglyConnectedComponents(G) ==
    {W \in StronglyConnectedSubgraphs(G) : IsMaximal(W, StronglyConnectedSubgraphs(G))}

\* TODO: is wrong, because Cycles2 contains all the permutations of a cycle while Cycles does not.
ASSUME \A G \in SUBSET (V \X V) : Cycles(G) = Cycles2(G)


=============================================================================
\* Modification History
\* Last modified Thu Jan 21 01:00:20 EST 2016 by nano
\* Created Tue Jul 28 03:10:02 CEST 2015 by nano
