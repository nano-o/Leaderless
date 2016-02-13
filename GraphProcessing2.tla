-------------------------- MODULE GraphProcessing2 --------------------------

(***************************************************************************)
(* Formalization of the graph processing in the brief announcement.        *)
(***************************************************************************)

EXTENDS DiGraph, CStruct


(***************************************************************************)
(* The set of all graphs of the form                                       *)
(*                                                                         *)
(*     [Vs -> SUBSET V] where Vs \subseteq V                               *)
(*                                                                         *)
(* We give Maps an unused parameter "x" to prevent TLC from                *)
(* unconditionally evaluating it.                                          *)
(***************************************************************************)
Maps(x) == UNION {[Vs -> SUBSET V] : Vs \in SUBSET V}
        
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
(* Restriction of a map m \in Graphs to its executable commands.           *)
(***************************************************************************)
RestrictToExecutable(m) ==
    [x \in {x \in DOMAIN m : CanExec(x,m)} |-> m[x]] 

(***************************************************************************)
(* Convert a map to a graph.                                               *)
(***************************************************************************)
ConvertMap(g) ==
    LET Vs == {v \in DOMAIN g : CanExec(v,g)} 
        Es == UNION { {<<v1,v2>> : v2 \in (g[v1] \ {v1}) \cap Vs} : 
            v1 \in Vs}
    IN <<Vs, Es>>

CompatMaps(m1,m2) ==
    \A x \in DOMAIN m1 \cap DOMAIN m2 : m1[x] = m2[x]

MapPlus(m1,m2) ==
    [v\in DOMAIN m1 \cup DOMAIN m2 |-> IF v \in DOMAIN m1 THEN m1[v] ELSE m2[v]]
    
GraphUnion(G1,G2) ==
    <<Vertices(G1)\cup Vertices(G2), Edges(G1)\cup Edges(G2)>>
    
GraphIntersection(G1,G2) ==
    <<Vertices(G1)\cap Vertices(G2), Edges(G1)\cap Edges(G2)>>
    
(***************************************************************************)
(* G1 is a vertice-induced subgraph of G2.                                 *)
(***************************************************************************)
VerticeInducedSubgraph(G1,G2) ==
    /\ Vertices(G1) \subseteq Vertices(G2)
    /\ \A e \in Edges(G2) : 
        (e[1] \in Vertices(G1) /\ e[2] \in Vertices(G2)) = (e \in Edges(G1))

(***************************************************************************)
(* G1 and G2 are compatible.                                               *)
(***************************************************************************)
CompatGraphs(G1,G2) ==
    VerticeInducedSubgraph(GraphIntersection(G1,G2), GraphUnion(G1,G2))

(***************************************************************************)
(* If two maps are compatible, then the two corresponding graphs are       *)
(* compatible.  In the generic leaderless algorithm, by property of the    *)
(* map-agreement abstraction, the maps of two different processes at two   *)
(* different times are always compatible.  Therefore, so are the           *)
(* corresponding graphs.                                                   *)
(***************************************************************************)
THEOREM \A m1,m2 \in Maps(TRUE) : CompatMaps(m1,m2) => 
    CompatGraphs(ConvertMap(m2), ConvertMap(m1))    
        
(***************************************************************************)
(* The ordering induced by a graph.                                        *)
(***************************************************************************)
GraphOrder(G) ==
    {<<v1,v2>> \in Vertices(G) \times Vertices(G) : 
        \neg Dominates(v1,v2,G) /\ Dominates(v2,v1,G)}

(***************************************************************************)
(* We now make some definitions to define functions from set of commands   *)
(* (i.e.  subsets of V) to total orders on V which map a set Vs to a total *)
(* order on Vs.  This set of functions is                                  *)
(*                                                                         *)
(*     {SeqOrder(f) : f \in LinFunsRec(SUBSET V)}                          *)
(***************************************************************************)

(***************************************************************************)
(* The set of sequences of elements of X and of length Cardinality(X).     *)
(***************************************************************************)
Lins(X) == { seq \in [1..Cardinality(X) -> X] : NoDup(seq)}

(***************************************************************************)
(* LinFunsRec(SUBSET X) shoud be the same as                               *)
(*                                                                         *)
(*     {seq \in [SUBSET X -> BSeq(X,Cardinality(X))] :                     *)
(*         Len(seq) = Cardinality(X) /\ NoDup(X) }                         *)
(***************************************************************************)
RECURSIVE LinFunsRec(_)
LinFunsRec(domain) ==
    LET Vs1 == CHOOSE Vs1 \in domain : TRUE
        recDom == domain \ {Vs1}
        recFuns == LinFunsRec(recDom)
        seqs == Lins(Vs1)
    IN  IF domain = {} THEN {<<>>}
        ELSE
            UNION {
                {[Vs \in domain |-> IF Vs = Vs1 THEN seq ELSE f[Vs]] : seq \in seqs}
                    : f \in recFuns }
(***************************************************************************)
(* Declarative version of LinFunsRec.                                      *)
(***************************************************************************)
LinFunsDecl(X) == {f \in [SUBSET X -> BSeq(X,Cardinality(X))] :
        \A xs \in DOMAIN f : Len(f[xs]) = Cardinality(xs) /\ NoDup(f[xs]) }
        
(***************************************************************************)
(* The declarative version and the recursive definition should coincide.   *)
(***************************************************************************)
THEOREM \A X : LinFunsDecl(X) = LinFunsRec(SUBSET X)
        
(***************************************************************************)
(* Converts a sequence to a total order.                                   *)
(***************************************************************************)
SeqOrder(seq) == {<<x,y>> \in Image(seq) \times Image(seq) : 
    \E i,j \in DOMAIN seq : i < j /\ seq[i] = x /\ seq[j] = y}

(***************************************************************************)
(* l is a linearization of G, where f is the mapping of sets of commands   *)
(* to total orders agreed upon by all the processes.                       *)
(***************************************************************************)
IsLin(G, f, l) == LET Vs == Vertices(G) IN
    /\ l \in [1..Cardinality(Vs) -> Vs]
    /\ \A v \in Vs : \E i \in DOMAIN l : l[i] = v
    /\ \A i,j \in DOMAIN l : i # j =>
        /\ <<l[i],l[j]>> \in GraphOrder(G) => i < j
        /\ \A scc \in SCCs(G) : ((l[i] \in scc /\ l[j] \in scc /\ i < j) =>
                <<l[i],l[j]>> \in SeqOrder(f[scc]))

(***************************************************************************)
(* The set of all linearizations of a graph G.                             *)
(***************************************************************************)
LinsOfGraph(G,f) == 
    LET Vs == Vertices(G) 
    IN {l \in [1..Cardinality(Vs) -> Vs] : IsLin(G,f,l)}

(***************************************************************************)
(* An interference relation is reflexive but does not contain <<v,v>> for  *)
(* any v (a request always commutes with itself, because we assume that    *)
(* requests are uniquely identified and should not have effect twice).     *)
(*                                                                         *)
(* <<v1,v2>> \in R iff v1 and v2 do not commute.                           *)
(***************************************************************************)
IsInterferenceRelation(R) ==
    /\ R \subseteq V \times V 
    /\ \A v \in V : \neg <<v,v>> \in R
    /\ \A v1, v2 \in V : v1 # v2 /\ <<v1,v2>> \in R => <<v2,v1>> \in R

(***************************************************************************)
(* Used to ease the literal definition of interference relations.          *)
(***************************************************************************)
ReflexiveClosure(R) == {d \in V \times V : d \in R \/ <<d[2],d[1]>> \in R}
           
(***************************************************************************)
(* The dependency map invariant.  R is the interference relation among     *)
(* commands, i.e.  <<v1,v2>> \in R iff v1 and v2 do not commute.           *)
(***************************************************************************)
DependencyGraphInvariant(m, R) ==
    LET G == ConvertMap(m)
    IN \A v1,v2 \in Vertices(G) :
        v1 # v2 /\ <<v1,v2>> \in R => 
            <<v1, v2>> \in Edges(G) \/ <<v2, v1>> \in Edges(G)

(***************************************************************************)
(* The prefix relation up to the reordering of commutative commands.  R is *)
(* the interference relation among commands, i.e.  <<v1,v2>> \in R iff v1  *)
(* and v2 do not commute.                                                  *)
(*                                                                         *)
(* s1 and s2 are expected not to contain any duplicates.                   *)
(***************************************************************************)
PrefixUpTo(s1, s2, R) ==
    /\ Len(s1) <= Len(s2)
    /\  LET permutations == {es \in BSeq(Image(s2),Len(s2)) :
            /\ Len(es) = Len(s2)
            /\ Image(es) = Image(s2)
            /\ \A i,j \in DOMAIN es : i < j /\ <<es[i],es[j]>> \in R => 
                \E k,l \in DOMAIN s2 : 
                    /\  k < l 
                    /\  es[i] = s2[k]
                    /\  es[j] = s2[l] }
        IN \E p \in permutations : Prefix(s1,p)


(***************************************************************************)
(* This is almost right: instead of PrefixUpTo, we need to assert that l1  *)
(* and l2 are compatible (in the c-struct sense).                          *)
(***************************************************************************)
Test3(R) ==
    LET f == CHOOSE f \in LinFunsRec(SUBSET V) : TRUE
    IN
        \A m1,m2 \in Maps(TRUE) : (
            /\ CompatMaps(m1,m2) 
            /\ DependencyGraphInvariant(MapPlus(m1,m2), R) )
            =>
                \A l1 \in LinsOfGraph(ConvertMap(m1),f) : \A l2 \in LinsOfGraph(ConvertMap(m2),f) :
                    IF PrefixUpTo(l1,l2,R) \/ PrefixUpTo(l2,l1,R) THEN TRUE ELSE PrintT(<<l1,l2>>)
=============================================================================
\* Modification History
\* Last modified Sat Feb 13 17:52:09 EST 2016 by nano
\* Created Thu Feb 11 21:47:29 EST 2016 by nano
