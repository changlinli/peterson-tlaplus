------------------------------ MODULE Peterson ------------------------------

EXTENDS Integers

VARIABLES turn, processState, flag

vars == <<turn, processState, flag>>

TypeOK ==
    /\ \A p \in {0, 1} : flag[p] \in {TRUE, FALSE}
    /\ turn \in {0, 1}
    /\ \A p \in {0, 1} : processState[p] \in {"idle", "sentRequest", "waiting", "critical"}

Init ==
    /\ flag = [i \in {0, 1} |-> FALSE]
    /\ turn \in {0, 1}
    /\ processState = [i \in {0, 1} |-> "idle"]
    
ProcessRequestFlag(p) ==
    /\ processState[p] = "idle"
    /\ flag' = [flag EXCEPT ![p] = TRUE]
    /\ processState' = [processState EXCEPT ![p] = "sentRequest"]
    /\ UNCHANGED <<turn>>
    
ProcessBeginWaiting(p) ==
    /\ processState[p] = "sentRequest"
    /\ turn' = 1 - p
    /\ processState' = [processState EXCEPT ![p] = "waiting"]
    /\ UNCHANGED <<flag>>
    
ProcessEnterCritical(p) ==
    /\ processState[p] = "waiting"
    /\ (flag[(1 - p)] = FALSE \/ turn /= (1 - p))
    /\ processState' = [processState EXCEPT ![p] = "critical"]
    /\ UNCHANGED <<flag, turn>>

ProcessExitCritical(p) ==
    /\ processState[p] = "critical"
    /\ processState' = [processState EXCEPT ![p] = "idle"]
    /\ flag' = [flag EXCEPT ![p] = FALSE]
    /\ UNCHANGED <<turn>>

Next ==
    \E p \in {0, 1} :
        \/ ProcessRequestFlag(p)
        \/ ProcessBeginWaiting(p)
        \/ ProcessEnterCritical(p)
        \/ ProcessExitCritical(p)
    
Spec == Init /\ [][Next]_vars 

SpecWithFairness == Spec /\ WF_vars(Next) /\ \A p \in {0, 1} : WF_vars(ProcessRequestFlag(p))

MutualExclusion == ~(processState[0] = "critical" /\ processState[1] = "critical")

WillEventuallyEnterCritical == <>(processState[0] = "critical") /\ <>(processState[1] = "critical")

=============================================================================
\* Modification History
\* Last modified Wed Jul 24 21:20:26 EDT 2019 by changlin
\* Created Wed Jul 24 18:56:50 EDT 2019 by changlin
