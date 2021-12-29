----------------------- MODULE bully --------------------
EXTENDS TLC, Integers, FiniteSets, Randomization

CONSTANT PeersAmount

ASSUME PeersAmount \in Nat \ {0, 1}

IDS == 1..PeersAmount

(* --algorithm bully
variables 
    failed_leader = PeersAmount,

    initiator \in IDS \ {failed_leader},
    
    \* Some coordinated peers also can fail
    n \in 0..Cardinality(IDS \ {failed_leader, initiator}),
    others_who_failed = RandomSubset(n, IDS \ {failed_leader, initiator}),

    \* Channel buffers between each pair of peers
    channels = [sender \in IDS |-> [receiver \in IDS \ {sender} |-> ""]],
    
    \* Current leader for each peer
    leader = [id \in IDS |-> failed_leader];
  
define 
    IDSBiggerThan  == [id_1 \in IDS |-> {id_2 \in IDS : id_2 > id_1}]
                
    IDSSmallerThan == [id_1 \in IDS |-> {id_2 \in IDS : id_2 < id_1}]
            
    IDSBiggerThanExceptFailedLeader == 
        [id \in IDS |-> IDSBiggerThan[id] \ {failed_leader}]

    \* We don't need to wait for a timeout because we already know
    \* which peers can't answer our requests.
    DoesNotReceiveAnyResponse(id) == 
        IDSBiggerThanExceptFailedLeader[id] \ others_who_failed = {}
    
    \* Peers, that declared themselves as leaders to the receiver
    NewLeaders(receiver) == 
        {sender \in IDS \ {receiver} : channels[sender][receiver] = "Leader"}

    \* We don't need to wait for a timeout because we already know
    \* which peers can't answer our requests.
    DoesNotReceiveOKResponseFromNewLeaders(receiver) == 
        LET old_leader == leader[receiver] IN
        \E new_leader \in IDSBiggerThanExceptFailedLeader[receiver] :
        /\ new_leader \notin others_who_failed
        /\ IF old_leader = failed_leader THEN new_leader > old_leader ELSE TRUE
    
    \* Peers, that have sent "Election" requests to the receiver
    ElectionInitiators(receiver) == 
        {sender \in IDS \ {receiver} : channels[sender][receiver] = "Election"} 

    \* Peers, that have sent any messages to the receiver
    MessageSenders(receiver) ==
        {sender \in IDS \ {receiver} : channels[sender][receiver] /= ""}
    
    FailedIDS == others_who_failed \union {failed_leader}

    WorkingIDS == IDS \ FailedIDS

    IDThatShouldBecomeNewLeader ==
        CHOOSE new_leader \in WorkingIDS : 
        \A id \in WorkingIDS \ {new_leader} : new_leader > id

    AllWorkingIDSAreCoordinatedByNewLeader ==
        \A id \in WorkingIDS : leader[id] = IDThatShouldBecomeNewLeader

    EventuallySolved == []<>AllWorkingIDSAreCoordinatedByNewLeader
            
end define;

fair process Peer \in IDS
begin
Initialize:
    if self \in FailedIDS then
        goto Failed;
    elsif self = initiator then
        goto BecomeLeaderOrStartElection;
    else
        goto NormalExecution;
    end if;

\* If there are no peers with ID bigger than this peer has, then he himself becomes 
\* the new leader and sends "Leader" requests to all the other peers.
\* Otherwise, the peer sends "Election" messages to peers that have bigger IDs.
BecomeLeaderOrStartElection:
    if IDSBiggerThanExceptFailedLeader[self] = {} then
        leader[self] := self ||
        channels[self] := 
        [receiver \in DOMAIN channels[self] |-> 
            IF receiver \in IDSSmallerThan[self] THEN "Leader" ELSE ""];
        goto NormalExecution;
    else
        channels[self] := 
        [receiver \in DOMAIN channels[self] |-> 
            IF receiver \in IDSBiggerThan[self] THEN "Election" ELSE ""];
    end if;

\* If nobody responses to "Election" requests (timeout), then this peer becomes
\* the new leader and sends "Leader" requests to all the other peers. 
CheckElectionTimeout:
    if DoesNotReceiveAnyResponse(self) then
        leader[self] := self ||
        channels[self] := 
        [receiver \in DOMAIN channels[self] |-> 
            IF receiver \in IDSSmallerThan[self] THEN "Leader" ELSE ""];
        goto NormalExecution;
    end if;

\* Receives "OK" responses from proclaimed leaders until it reachers timeout.
CheckOkTimeout:
    if DoesNotReceiveOKResponseFromNewLeaders(self) then
        goto NormalExecution;
    end if;
AcceptNewLeader:
    with new_leader \in NewLeaders(self) do
        leader[self] := new_leader ||
        channels[new_leader][self] := "";
        goto CheckOkTimeout;
    end with;

\* If the peer receives "Election" request, he sends "OK" response and then acts like initiator
NormalExecution:
    with sender \in MessageSenders(self) do
        if channels[sender][self] = "Election" then
            channels[self][sender] := "OK" ||
            channels[sender][self] := "";
            goto BecomeLeaderOrStartElection;
        elsif channels[sender][self] = "Leader" then
            leader[self] := sender ||
            channels[sender][self] := "";
            goto NormalExecution;
        else
            channels[sender][self] := "";
        end if;
    end with;

Failed:
    skip;
end process;

end algorithm *)
\* BEGIN TRANSLATION (chksum(pcal) = "499ab1c7" /\ chksum(tla) = "70ed46e0")
VARIABLES failed_leader, initiator, n, others_who_failed, channels, leader, 
          pc

(* define statement *)
IDSBiggerThan  == [id_1 \in IDS |-> {id_2 \in IDS : id_2 > id_1}]

IDSSmallerThan == [id_1 \in IDS |-> {id_2 \in IDS : id_2 < id_1}]

IDSBiggerThanExceptFailedLeader ==
    [id \in IDS |-> IDSBiggerThan[id] \ {failed_leader}]



DoesNotReceiveAnyResponse(id) ==
    IDSBiggerThanExceptFailedLeader[id] \ others_who_failed = {}


NewLeaders(receiver) ==
    {sender \in IDS \ {receiver} : channels[sender][receiver] = "Leader"}



DoesNotReceiveOKResponseFromNewLeaders(receiver) ==
    LET old_leader == leader[receiver] IN
    \E new_leader \in IDSBiggerThanExceptFailedLeader[receiver] :
    /\ new_leader \notin others_who_failed
    /\ IF old_leader = failed_leader THEN new_leader > old_leader ELSE TRUE


ElectionInitiators(receiver) ==
    {sender \in IDS \ {receiver} : channels[sender][receiver] = "Election"}


MessageSenders(receiver) ==
    {sender \in IDS \ {receiver} : channels[sender][receiver] /= ""}

FailedIDS == others_who_failed \union {failed_leader}

WorkingIDS == IDS \ FailedIDS

IDThatShouldBecomeNewLeader ==
    CHOOSE new_leader \in WorkingIDS :
    \A id \in WorkingIDS \ {new_leader} : new_leader > id

AllWorkingIDSAreCoordinatedByNewLeader ==
    \A id \in WorkingIDS : leader[id] = IDThatShouldBecomeNewLeader

EventuallySolved == []<>AllWorkingIDSAreCoordinatedByNewLeader


vars == << failed_leader, initiator, n, others_who_failed, channels, leader, 
           pc >>

ProcSet == (IDS)

Init == (* Global variables *)
        /\ failed_leader = PeersAmount
        /\ initiator \in IDS \ {failed_leader}
        /\ n \in 0..Cardinality(IDS \ {failed_leader, initiator})
        /\ others_who_failed = RandomSubset(n, IDS \ {failed_leader, initiator})
        /\ channels = [sender \in IDS |-> [receiver \in IDS \ {sender} |-> ""]]
        /\ leader = [id \in IDS |-> failed_leader]
        /\ pc = [self \in ProcSet |-> "Initialize"]

Initialize(self) == /\ pc[self] = "Initialize"
                    /\ IF self \in FailedIDS
                          THEN /\ pc' = [pc EXCEPT ![self] = "Failed"]
                          ELSE /\ IF self = initiator
                                     THEN /\ pc' = [pc EXCEPT ![self] = "BecomeLeaderOrStartElection"]
                                     ELSE /\ pc' = [pc EXCEPT ![self] = "NormalExecution"]
                    /\ UNCHANGED << failed_leader, initiator, n, 
                                    others_who_failed, channels, leader >>

BecomeLeaderOrStartElection(self) == /\ pc[self] = "BecomeLeaderOrStartElection"
                                     /\ IF IDSBiggerThanExceptFailedLeader[self] = {}
                                           THEN /\ /\ channels' = [channels EXCEPT ![self] = [receiver \in DOMAIN channels[self] |->
                                                                                                 IF receiver \in IDSSmallerThan[self] THEN "Leader" ELSE ""]]
                                                   /\ leader' = [leader EXCEPT ![self] = self]
                                                /\ pc' = [pc EXCEPT ![self] = "NormalExecution"]
                                           ELSE /\ channels' = [channels EXCEPT ![self] = [receiver \in DOMAIN channels[self] |->
                                                                                              IF receiver \in IDSBiggerThan[self] THEN "Election" ELSE ""]]
                                                /\ pc' = [pc EXCEPT ![self] = "CheckElectionTimeout"]
                                                /\ UNCHANGED leader
                                     /\ UNCHANGED << failed_leader, initiator, 
                                                     n, others_who_failed >>

CheckElectionTimeout(self) == /\ pc[self] = "CheckElectionTimeout"
                              /\ IF DoesNotReceiveAnyResponse(self)
                                    THEN /\ /\ channels' = [channels EXCEPT ![self] = [receiver \in DOMAIN channels[self] |->
                                                                                          IF receiver \in IDSSmallerThan[self] THEN "Leader" ELSE ""]]
                                            /\ leader' = [leader EXCEPT ![self] = self]
                                         /\ pc' = [pc EXCEPT ![self] = "NormalExecution"]
                                    ELSE /\ pc' = [pc EXCEPT ![self] = "CheckOkTimeout"]
                                         /\ UNCHANGED << channels, leader >>
                              /\ UNCHANGED << failed_leader, initiator, n, 
                                              others_who_failed >>

CheckOkTimeout(self) == /\ pc[self] = "CheckOkTimeout"
                        /\ IF DoesNotReceiveOKResponseFromNewLeaders(self)
                              THEN /\ pc' = [pc EXCEPT ![self] = "NormalExecution"]
                              ELSE /\ pc' = [pc EXCEPT ![self] = "AcceptNewLeader"]
                        /\ UNCHANGED << failed_leader, initiator, n, 
                                        others_who_failed, channels, leader >>

AcceptNewLeader(self) == /\ pc[self] = "AcceptNewLeader"
                         /\ \E new_leader \in NewLeaders(self):
                              /\ /\ channels' = [channels EXCEPT ![new_leader][self] = ""]
                                 /\ leader' = [leader EXCEPT ![self] = new_leader]
                              /\ pc' = [pc EXCEPT ![self] = "CheckOkTimeout"]
                         /\ UNCHANGED << failed_leader, initiator, n, 
                                         others_who_failed >>

NormalExecution(self) == /\ pc[self] = "NormalExecution"
                         /\ \E sender \in MessageSenders(self):
                              IF channels[sender][self] = "Election"
                                 THEN /\ channels' = [channels EXCEPT ![self][sender] = "OK",
                                                                      ![sender][self] = ""]
                                      /\ pc' = [pc EXCEPT ![self] = "BecomeLeaderOrStartElection"]
                                      /\ UNCHANGED leader
                                 ELSE /\ IF channels[sender][self] = "Leader"
                                            THEN /\ /\ channels' = [channels EXCEPT ![sender][self] = ""]
                                                    /\ leader' = [leader EXCEPT ![self] = sender]
                                                 /\ pc' = [pc EXCEPT ![self] = "NormalExecution"]
                                            ELSE /\ channels' = [channels EXCEPT ![sender][self] = ""]
                                                 /\ pc' = [pc EXCEPT ![self] = "Failed"]
                                                 /\ UNCHANGED leader
                         /\ UNCHANGED << failed_leader, initiator, n, 
                                         others_who_failed >>

Failed(self) == /\ pc[self] = "Failed"
                /\ TRUE
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << failed_leader, initiator, n, others_who_failed, 
                                channels, leader >>

Peer(self) == Initialize(self) \/ BecomeLeaderOrStartElection(self)
                 \/ CheckElectionTimeout(self) \/ CheckOkTimeout(self)
                 \/ AcceptNewLeader(self) \/ NormalExecution(self)
                 \/ Failed(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in IDS: Peer(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in IDS : WF_vars(Peer(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
====
