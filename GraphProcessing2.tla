-------------------------- MODULE GraphProcessing2 --------------------------

(***************************************************************************)
(* Formalization of the graph processing in the brief announcement.        *)
(***************************************************************************)

EXTENDS DiGraph, GraphProcessing

(***************************************************************************)
(* CanExec(v, g) tests whether all the dependencies of a vertice v have    *)
(* are in the domain of the graph g.  We must have g \in Graphs.           *)
(***************************************************************************)
RECURSIVE CanExecRec2(_,_,_)
CanExecRec2(v, seen, graph) ==
    /\  v \in DOMAIN graph
    /\  LET deps == graph[v]
        IN \A v2 \in deps : 
            \/  v2 \in seen
            \/  CanExecRec(v2, seen \cup {v2}, graph)
          
CanExec2(v, g) == CanExecRec2(v, {v}, g)

RestrictMap(m) ==
    [x \in {x \in DOMAIN m : CanExec(x,m)} |-> m[x]] 

ConvertGraph2(g) ==
    LET Vs == {v \in DOMAIN g : CanExec(v,g)}
        Es == UNION { {<<v1,v2>> : v2 \in (g[v1] \ {v1}) \cap Vs} : 
            v1 \in Vs}
    IN <<Vs, Es>>
    
CompatMaps(m1,m2) ==
    \A x \in DOMAIN m1 \cap DOMAIN m2 : m1[x] = m2[x]
    
(* m1 and m2 must be compatible for that to make sense *)
MapPlus(m1,m2) ==
    [v\in DOMAIN m1 \cup DOMAIN m2 |-> IF v \in DOMAIN m1 THEN m1[v] ELSE m2[v]]
    
GraphUnion(G1,G2) ==
    <<Vertices(G1)\cup Vertices(G2), Edges(G1)\cup Edges(G2)>>
    
GraphIntersection(G1,G2) ==
    <<Vertices(G1)\cap Vertices(G2), Edges(G1)\cap Edges(G2)>>
    
VerticeInducedSubgraph(G1,G2) ==
    /\ Vertices(G1) \subseteq Vertices(G2)
    /\ \A e \in Edges(G2) : 
        (e[1] \in Vertices(G1) /\ e[2] \in Vertices(G2)) = (e \in Edges(G1))

CompatGraphs(G1,G2) ==
    VerticeInducedSubgraph(GraphIntersection(G1,G2), GraphUnion(G1,G2))

THEOREM 
    \A m1,m2 \in Graphs(TRUE) : CompatMaps(m1,m2) => 
        CompatGraphs(ConvertGraph2(m2), ConvertGraph2(m1))
        
Test1(x) == \A m1,m2 \in Graphs(TRUE) : 
    IF CompatMaps(m1,m2) THEN PrintT(<<m1,m2>>) ELSE TRUE

GraphOrder(G) ==
    {<<v1,v2>> \in Vertices(G) \times Vertices(G) : 
        \neg Dominates(v1,v2,G) /\ Dominates(v2,v1,G)}
        
SeqOrder(seq) == {<<x,y>> \in Image(seq) \times Image(seq) : 
    \E i,j \in DOMAIN seq : i < j /\ seq[i] = x /\ seq[j] = y} 

IsLin(G, f, l) == LET Vs == Vertices(G) IN
    /\ l \in [1..Cardinality(Vs) -> Vs]
    /\ \A v \in Vs : \E i \in DOMAIN l : l[i] = v
    /\ \A i,j \in DOMAIN l : i # j =>
        /\ <<l[i],l[j]>> \in GraphOrder(G) => i < j
        /\ \A scc \in SCCs(G) : ((l[i] \in scc /\ l[j] \in scc /\ i < j) =>
                <<l[i],l[j]>> \in SeqOrder(f[scc]))

Linss(G,f) == LET Vs == Vertices(G) IN {l \in [1..Cardinality(Vs) -> Vs] : IsLin(G,f,l)}
           
(***************************************************************************)
(* This is almost right: instead of PrefixUpTo, we need to assert that l1  *)
(* and l2 are compatible (in the c-struct sense).                          *)
(***************************************************************************)     
Test3(R) ==
    LET f == CHOOSE f \in LinFunsRec(SUBSET V) : TRUE
    IN
        \A m1,m2 \in Graphs(TRUE) : (
            /\ CompatMaps(m1,m2) 
            /\ DependencyGraphInvariant2(MapPlus(m1,m2), R) )
            =>
                \A l1 \in Linss(ConvertGraph2(m1),f) : \A l2 \in Linss(ConvertGraph2(m2),f) :
                    IF PrefixUpTo(l1,l2,R) \/ PrefixUpTo(l2,l1,R) THEN TRUE ELSE PrintT(<<l1,l2>>)
                
Test2(x) ==
    LET f == CHOOSE f \in LinFunsRec(SUBSET V) : TRUE
    IN
    \A g \in Graphs(TRUE) : 
        LET G == ConvertGraph2(g)
            Vs == Vertices(G) IN
        /\  PrintT(<<"Graph",G>>)
        /\ \A l \in [1..Cardinality(Vs) -> Vs] :
             IF IsLin(G,f,l) THEN PrintT(<<G, l>>) ELSE TRUE
             
=============================================================================
\* Modification History
\* Last modified Fri Feb 12 00:16:59 EST 2016 by nano
\* Created Thu Feb 11 21:47:29 EST 2016 by nano
