------------------------- MODULE ConsensusInterface -------------------------

EXTENDS Common

Init == [proposed |-> {}, decided |-> None, flag |-> TRUE]

\* Init(s) == s = [proposed |-> {}, decided |-> None, flag |-> TRUE]

\* flag is there just to prevent stuttering transitions on the interface
State == [proposed : SUBSET V, decided : V \cup {None}, flag : BOOLEAN]

Propose(v, s, t) == t = [
    proposed |->  s.proposed \cup {v},
    decided |-> s.decided,
    flag |-> \neg s.flag]

Decide(v, s, t) == t = [
    decided |-> v,
    proposed |-> s.proposed,
    flag |-> \neg s.flag]

=============================================================================
\* Modification History
\* Last modified Fri Feb 05 11:16:48 EST 2016 by nano
\* Created Thu Feb 04 17:10:30 EST 2016 by nano
