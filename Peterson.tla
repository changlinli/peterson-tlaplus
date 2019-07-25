------------------------------ MODULE Peterson ------------------------------

(***************************************************************************)
(* This is a specification following Peterson's algorithm as documented at *)
(* https://en.wikipedia.org/wiki/Peterson%27s_algorithm.  I also hope for  *)
(* this to be an intermediate introduction to how a TLA+ spec reads if     *)
(* you're already familiar with the basics of TLA+.                        *)
(*                                                                         *)
(* This is a loose translation of the original pseudo-code that attempts   *)
(* to preserve the intent of the algorithm rather than following the       *)
(* pseudo-code to the T.  This hopefully results in a more natural TLA+    *)
(* specification rather than a mechanical logical translation of           *)
(* imperative code.                                                        *)
(*                                                                         *)
(* Peterson's algorithm is an attempt to allow two concurrent processes to *)
(* access the same resource (alternatively enter a critical section)       *)
(* exclusively.  That is the resource should be only accessed by at most a *)
(* single process at any time.                                             *)
(*                                                                         *)
(* The central intuition behind Peterson's algorithm is to use three       *)
(* separate items to coordinate efforts between the processes: one item to *)
(* coordinate whose turn it is to access the resource and then an          *)
(* additional flag per process to indicate that a process wishes to access *)
(* the resource.  It might seem that the single item keeping track of      *)
(* whose turn it is is enough to mediate access to the resource.           *)
(* Unfortunately, this breaks down if one process wishes to repeatedly     *)
(* access the resource whereas the other process remains idle the entire   *)
(* time.  For more details see                                             *)
(* https://github.com/changlinli/bad-peterson-tlaplus for what goes wrong. *)
(*                                                                         *)
(* There is one meta-invariant here that I attempt to preserve here.       *)
(* Peterson's algorithm is meant to be used in an environment with few     *)
(* atomicity guarantees.  In particular it assumes you can atomically set  *)
(* those three items mentioned earlier and have their changes propagate    *)
(* instantly, but no more.                                                 *)
(*                                                                         *)
(* That means each step in a TLA+ behavior should only change at most one  *)
(* of the three aforementioned items (although the internal state of a     *)
(* process could change as well).  Each step should also only read from at *)
(* most item (in addition to reading a process's internal state).  Finally *)
(* no step should both read and write to one of the three items (although  *)
(* a step could read a process's internal state and then write to one of   *)
(* the three items and modify its own internal state all in one go).       *)
(***************************************************************************)

EXTENDS Integers

VARIABLES 
    turn, (*****************************************************************)
          (* This is one of the three items that mutate in Peterson's      *)
          (* algorithm.  It is what keeps track of which process's turn it *)
          (* is to access the shared resource                              *)
          (*****************************************************************)
    processState, (*********************************************************)
                  (* This is a function mapping each process (represented  *)
                  (* by an integer 0 or 1) to its current state (a         *)
                  (* string).                                              *)
                  (*********************************************************)
    flag (******************************************************************)
         (* This contains the remaining two of the three items that mutate *)
         (* in Peterson' algorithm.  It is a function mapping each process *)
         (* (represented by an integer 0 or 1) to a boolean flag           *)
         (* indicating whether the process would like to access the shared *)
         (* resource.                                                      *)
         (******************************************************************)

vars == <<turn, processState, flag>> (**************************************)
                                     (* This is simply a convenient        *)
                                     (* grouping of variables to use later *)
                                     (* on when defining temporal          *)
                                     (* properties to save on tedious      *)
                                     (* typing.                            *)
                                     (**************************************)

(***************************************************************************)
(* The following property is an enumeration of all possible valid values   *)
(* for each variable previously defined.  The only thing of note here is   *)
(* the possible states a process can be in.  These are                     *)
(*                                                                         *)
(*     "idle": that is the process is neither accessing the resource nor   *)
(*      wants to access the resource at the moment)                        *)
(*                                                                         *)
(*     "sentRequest": the process now wants to access the resource and     *)
(*     has sent a request to do so                                         *)
(*                                                                         *)
(*     "waiting": the process is currently waiting to access a resource,   *)
(*     usually because the other process is currently accessing the        *)
(*     resource)                                                           *)
(*                                                                         *)
(*     "critical": the process has entered a critical section,             *)
(*     i.e. it is currently accessing the shared resource                  *)
(*                                                                         *)
(***************************************************************************)
TypeOK ==
    /\ \A p \in {0, 1} : flag[p] \in {TRUE, FALSE}
    /\ turn \in {0, 1}
    /\ \A p \in {0, 1} : processState[p] \in {"idle", "sentRequest", "waiting", "critical"}

(***************************************************************************)
(* This is one possible initial state of Peterson's algorithm.  It is the  *)
(* most "natural" one, that is the one where both processes are idle and   *)
(* have not yet decided to access the resource.                            *)
(***************************************************************************)
Init ==
    /\ flag = [i \in {0, 1} |-> FALSE]
    /\ turn \in {0, 1}
    /\ processState = [i \in {0, 1} |-> "idle"]
    
(***************************************************************************)
(* This predicate describes how a process can send a request to access a   *)
(* resource, which essentially amounts to setting its request flag to      *)
(* true.                                                                   *)
(***************************************************************************)    
ProcessRequestFlag(p) ==
    /\ processState[p] = "idle"
    /\ flag' = [flag EXCEPT ![p] = TRUE]
    /\ processState' = [processState EXCEPT ![p] = "sentRequest"]
    /\ UNCHANGED <<turn>>

(***************************************************************************)
(* This predicate describes how a process begins to wait on accessing a    *)
(* resource.  It may not be obvious why the turn should be set to the      *)
(* other process.  There are two reasons.                                  *)
(*                                                                         *)
(* First, by giving the other process a chance first to access the         *)
(* resource we ensure that both processes will eventually have a chance to *)
(* access the resource.  Otherwise one process could continually maintain  *)
(* a monopoly on the resource and leave the other process waiting forever. *)
(*                                                                         *)
(* Second, without the ability to atomically both read and write, this     *)
(* also can lead to mutual exclusion failure, i.e.  both processes         *)
(* accessing the resource at the same time.  This is because a process can *)
(* wrest away the turn from the other process while the other process is   *)
(* accessing the resource, since the flags cannot distinguish between a    *)
(* process that would like to access a resource and one that already is    *)
(* doing so.                                                               *)
(*                                                                         *)
(* For more on these two errors, see the invariants at the end of the      *)
(* file.                                                                   *)
(*                                                                         *)
(* These violations can be seen clearly if you change turn' to p and walk  *)
(* through the error trace TLC finds.                                      *)
(***************************************************************************)  
ProcessBeginWaiting(p) ==
    /\ processState[p] = "sentRequest"
    /\ turn' = 1 - p
    /\ processState' = [processState EXCEPT ![p] = "waiting"]
    /\ UNCHANGED <<flag>>
    
(***************************************************************************)
(* This predicate describes how a process accesses a resource, i.e.        *)
(* enters a critical section.  Note that even though it looks like we read *)
(* from two resources here, this is an OR clause, meaning we only do one   *)
(* actual read, preserving the meta-invariant of reading from at most one  *)
(* of the three items (two flags + turn).                                  *)
(*                                                                         *)
(* Note as well that a process p can access a resource even if turn is not *)
(* p.  You can see this by the failure of CanOnlyBeCriticalIfTurn to hold  *)
(* in TLC.  This is to prevent a process from indefinitely giving its turn *)
(* away in ProcessBeginWaiting if the other process is still idle and has  *)
(* no intention of accessing the shared resource.                          *)
(***************************************************************************)
ProcessEnterCritical(p) ==
    /\ processState[p] = "waiting"
    /\ (flag[(1 - p)] = FALSE \/ turn = p)
    /\ processState' = [processState EXCEPT ![p] = "critical"]
    /\ UNCHANGED <<flag, turn>>

(***************************************************************************)
(* This predicate describes how a process returns to an idle state after   *)
(* finishing accessing the shared resource, i.e.  leaves its critical      *)
(* section.                                                                *)
(*                                                                         *)
(* In addition to becoming idle, the process also resets its flag thereby  *)
(* indicating it no longer wishes to access the shared resource.           *)
(***************************************************************************)
ProcessExitCritical(p) ==
    /\ processState[p] = "critical"
    /\ processState' = [processState EXCEPT ![p] = "idle"]
    /\ flag' = [flag EXCEPT ![p] = FALSE]
    /\ UNCHANGED <<turn>>

(***************************************************************************)
(* This predicate describes how the state machine of this algorithm should *)
(* evolve over time.  The existential quantification here is simply to     *)
(* reduce duplication (so I don't have to rewrite each line with both 0    *)
(* and 1 as an argument).                                                  *)
(***************************************************************************)
Next ==
    \E p \in {0, 1} :
        \/ ProcessRequestFlag(p)
        \/ ProcessBeginWaiting(p)
        \/ ProcessEnterCritical(p)
        \/ ProcessExitCritical(p)
    
(***************************************************************************)
(* Our basic specification without additional fairness guarantees.  This   *)
(* is sufficient to show mutual exclusion, but fails to demonstrate        *)
(* liveness requirements (see WillEventuallyEnterCritical).  This is       *)
(* because of stuttering (where the state of the processes don't change);  *)
(* both processes could decide to e.g.  be idle forever and thereby never  *)
(* enter a critical section.  This is also because of a partial variant of *)
(* stuttering, i.e.  while the overall state continues to evolve, only one *)
(* process is doing anything while the other remains idle.                 *)
(***************************************************************************)
Spec == Init /\ [][Next]_vars 

(***************************************************************************)
(* Adds fairness guarantees to our basic specification.  This allows us to *)
(* show liveness (WillEventuallyEnterCritical) by postulating that the     *)
(* overall state always eventually changes and that both processes will    *)
(* eventually request to access the shared resource.                       *)
(***************************************************************************)
SpecWithFairness == Spec /\ WF_vars(Next) /\ \A p \in {0, 1} : WF_vars(ProcessRequestFlag(p))

(***************************************************************************)
(* Now we move on to the invariants we wish to hold! (And one which we     *)
(* don't).  Note that there is one property of Peterson's algorithm which  *)
(* we do not show here; in fact as far as I'm aware it is not possible to  *)
(* show with TLA+ without some invasive contortions.  Bounded waiting,     *)
(* that is that a process will never wait more than a fixed N steps to     *)
(* enter its critical section after requesting to do so, is hard to show   *)
(* in TLA+ because TLA+ doesn't offer tools to reason about the particular *)
(* execution trace of a model over time.                                   *)
(***************************************************************************)

(***************************************************************************)
(* This is the basic mutual exclusion property.  Only one process at a     *)
(* time should access the shared resource, i.e.  enter its own critical    *)
(* section.  This is the central purpose of Peterson's algorithm.          *)
(***************************************************************************)
MutualExclusion == ~(processState[0] = "critical" /\ processState[1] = "critical")

THEOREM Spec => []MutualExclusion

(***************************************************************************)
(* This is a basic liveness requirement that corresponds to what is called *)
(* "Progress" in the Wikipedia article.  Both processes should eventually  *)
(* be able to enter their critical sections.                               *)
(***************************************************************************)
WillEventuallyEnterCritical == <>(processState[0] = "critical") /\ <>(processState[1] = "critical")

THEOREM SpecWithFairness => WillEventuallyEnterCritical

(***************************************************************************)
(* THIS INVARIANT DOES NOT HOLD AND SHOULD NOT HOLD! It's merely           *)
(* instructive of something a reader may intuitively believe about this    *)
(* algorithm that turns out to be false.                                   *)
(*                                                                         *)
(* See the note in ProcessEnterCritical.                                   *)
(***************************************************************************)
CanOnlyBeCriticalIfTurn == \A p \in {0, 1} : processState[p] = "critical" => turn = p

(***************************************************************************)
(* Finally we note simply that our variables should always stay within the *)
(* bounds we enumerated earlier.                                           *)
(***************************************************************************)
THEOREM Spec => TypeOK

=============================================================================
\* Modification History
\* Last modified Thu Jul 25 11:05:46 EDT 2019 by changlin
\* Created Wed Jul 24 18:56:50 EDT 2019 by changlin
