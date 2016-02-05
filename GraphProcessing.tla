----------------------- MODULE GraphProcessing -----------------------

(***************************************************************************)
(* Processing of a command-dependency graph like in EPaxos.                *)
(***************************************************************************)

EXTENDS DiGraph
   
(***************************************************************************)
(* EPaxos graph processing                                                 *)
(***************************************************************************)
RECURSIVE LinearizeDepsRec(_,_) 
LinearizeDepsRec(s, sccs) ==
    IF sccs # <<>>
    THEN 
        LET sccLin == CHOOSE es \in BSeq(Head(sccs), Cardinality(Head(sccs))) :
                NoDup(es) /\ Len(es) = Cardinality(Head(sccs)) 
        IN LinearizeDepsRec(sccLin \o s, Tail(sccs))
    ELSE s

LinearizeDeps(G) ==
    LET SCCLin == TotalOrder(SCCGraph(G))
    IN  LinearizeDepsRec(<<>>, SCCLin)



(***************************************************************************)
(* Converts a graph in the form                                            *)
(*                                                                         *)
(*     [V -> SUBSET V]                                                     *)
(*                                                                         *)
(* to the form                                                             *)
(*                                                                         *)
(*     SUBSET V \times SUBSET (V \times V)                                 *)
(*                                                                         *)
(* This may be useful in algorithms where the processes collect a set of   *)
(* dependencies for each command.                                          *)
(***************************************************************************)
ConvertGraph(G) ==
    LET Vs == DOMAIN G
        Es == UNION { {<<v1,v2>> : v2 \in G[v1] \ {v1}} : v1 \in DOMAIN G}
    IN <<Vs, Es>>

=============================================================================
\* Modification History
\* Last modified Fri Feb 05 09:17:19 EST 2016 by nano
\* Created Fri Feb 05 09:08:21 EST 2016 by nano
