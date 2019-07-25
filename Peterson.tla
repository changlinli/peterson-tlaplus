------------------------------ MODULE Peterson ------------------------------

VARIABLES flag0, flag1, turn, process0State, process1State, processState, flag

vars == <<flag0, flag1, turn, process0State, process1State>>

TypeOK ==
    /\ flag0 \in {TRUE, FALSE}
    /\ flag1 \in {TRUE, FALSE}
    /\ turn \in {0, 1}
    /\ process0State \in {"idle", "requestedFlag", "waiting", "critical"}
    /\ process1State \in {"idle", "requestedFlag", "waiting", "critical"}

Init ==
    /\ flag0 = FALSE
    /\ flag1 = FALSE
    /\ turn \in {0, 1}
    /\ process0State = "idle"
    /\ process1State = "idle"
    
ProcessRequestFlag(p) ==
    /\ processState[p] = "idle"
    /\ flag' = [flag EXCEPT ![p] = TRUE]
    /\ processState' = [processState EXCEPT ![p] = "requestedFlag"]
    /\ UNCHANGED <<turn>>
    
ProcessBeginWaiting(p) ==
    /\ processState[p] = "sentRequest"
    /\ turn' = p
    /\ processState' = [processState EXCEPT ![p] = "waiting"]
    /\ UNCHANGED <<flag1, flag0, process1State>>
    
ProcessEnterCritical(p) ==
    /\ processState[p] = "waiting"
    /\ (flag[p] = FALSE \/ turn /= 1)
    /\ processState' = [processState EXCEPT ![p] = "critical"]
    /\ UNCHANGED <<flag>>

ProcessExitCritical(p) ==
    /\ processState[p] = "critical"
    /\ processState' = [processState EXCEPT ![p] = "idle"]
    /\ flag' = [flag EXCEPT ![p] = FALSE]
    /\ UNCHANGED <<turn>>

Next ==
    \A p \in {0, 1} :
        \/ ProcessRequestFlag(p)
        \/ ProcessBeginWaiting(p)
        \/ ProcessEnterCritical(p)
        \/ ProcessExitCritical(p)
    
Spec == Init /\ [][Next]_vars 

SpecWithFairness == Spec /\ WF_vars(Next) /\ WF_vars(Process0RequestFlag) /\ WF_vars(Process1RequestFlag)
    
MutualExclusion == ~(process0State = "critical" /\ process1State = "critical")

WillEventuallyEnterCritical == <>(process0State = "critical") /\ <>(process1State = "critical")

=============================================================================
\* Modification History
\* Last modified Wed Jul 24 20:43:26 EDT 2019 by changlin
\* Created Wed Jul 24 18:56:50 EDT 2019 by changlin
