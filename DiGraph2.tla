------------------------------ MODULE DiGraph2 ------------------------------

EXTENDS DiGraph

(***************************************************************************)
(* I'm not sure anymore what all the stuff below does...                   *)
(***************************************************************************)
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

\* TODO: is wrong, because Cycles2 contains all the permutations of a cycle while Cycles does not.
\* ASSUME \A G \in SUBSET (V \X V) : Cycles(G) = Cycles2(G)

=============================================================================
\* Modification History
\* Last modified Thu Feb 04 16:09:34 EST 2016 by nano
\* Created Thu Feb 04 16:09:09 EST 2016 by nano
