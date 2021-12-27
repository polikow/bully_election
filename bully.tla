----------------------- MODULE bully --------------------
EXTENDS TLC, Integers, Sequences, FiniteSets, Randomization

CONSTANT PeersAmount \* число пиров в системе

ASSUME PeersAmount \in Nat \ {0, 1}

\* Множество всех ID узлов
IDS == 1..PeersAmount

\* Множество возможных значений в каналах обмена сообщениями
Messages == {"", "Election", "OK", "Leader"}

(* --algorithm bully
variables 
    \* ID отказавшего узла
    failed_leader = PeersAmount,

    \* ID узла, который инициализировал проверку
    \* Проверяются все возможные варианты (кроме того, когда инициатором становится отказавший)
    initiator \in IDS \ {failed_leader},
    
    \* Некоторые подчиненные узлы также могут отказать
    n \in 0..Cardinality(IDS \ {failed_leader, initiator}),
    others_who_failed = RandomSubset(n, IDS \ {failed_leader, initiator}),

    \* Каналы передачи между каждой парой узлов (кроме канала к самому себе)
    \* [отправитель][получатель]
    channels = [sender \in IDS |-> [receiver \in IDS \ {sender} |-> ""]],
    
    \* Текущий лидер для каждого ID
    leader = [id \in IDS |-> failed_leader];
  
define 
    \* Множество идентификаторов, которые больше заданного
    IDSBiggerThan  == [id_1 \in IDS |-> {id_2 \in IDS : id_2 > id_1}]
                
    \* Множество идентификаторов, которые меньше заданного
    IDSSmallerThan == [id_1 \in IDS |-> {id_2 \in IDS : id_2 < id_1}]
            
    \* Множество идентификаторов, которые больше по ID (кроме отказавшего лидера)
    IDSBiggerThanExceptFailedLeader == [id \in IDS |-> IDSBiggerThan[id] \ {failed_leader}]

    \* Не получает ответ от узлов, которые больше него
    \* (только в том случае, если они тоже отказали)
    DoesNotReceiveAnyResponse(id) == 
        IDSBiggerThanExceptFailedLeader[id] \ others_who_failed = {}
    
    \* множество ID узлов, которые объявили себя лидерами
    NewLeaders(receiver) == 
        {sender \in IDS \ {receiver} : channels[sender][receiver] = "Leader"}

    \* Получает ли ответы от новых лидеров с большим ID
    ReceivesResponseFromNewLeaders(receiver) == 
        LET old_leader == leader[receiver]
        IN
        \E new_leader \in IDSBiggerThanExceptFailedLeader[receiver] :
        /\ new_leader \notin others_who_failed
        /\ IF old_leader = failed_leader THEN TRUE ELSE new_leader > old_leader
    
    \* множество ID узлов, которые объявили голосование
    ElectionInitiators(receiver) == 
        {sender \in IDS \ {receiver} : channels[sender][receiver] = "Election"} 

    \* множество узлов, которые прислали сообщения этому получателю    
    MessageSenders(receiver) ==
        {sender \in IDS \ {receiver} : channels[sender][receiver] /= ""}
    
    FailedIDS == others_who_failed \union {failed_leader}

    WorkingIDS == IDS \ FailedIDS

    IDThatShouldBecomeNewLeader ==
        CHOOSE new_leader \in WorkingIDS : 
        \A id \in WorkingIDS \ {new_leader} : new_leader > id

    AllAliveIDSAreCoordinatedByNewLeader ==
        \A id \in WorkingIDS : leader[id] = IDThatShouldBecomeNewLeader

    EventuallySolved == []<>AllAliveIDSAreCoordinatedByNewLeader

    CorrectMessages == 
        [](\A sender \in IDS : \A receiver \in IDS \ {sender} : channels[sender][receiver] \in Messages)

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

\* Если никого с большим ID нет, то этот узел автоматически становится
\* лидером и посылает всем остальным сообщение об этом.
\* Иначе если он не с самым большим ID, то отсылает узлам сообщение о выборах.
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

\* Если никто не отвечает на его запросы о выборах, 
\* (возможно только в том случае, когда эти узлы тоже отказали)
\* то этот узел сам становится лидером и посылает всем остальным сообщение об этом.
CheckElectionTimeout:
    if DoesNotReceiveAnyResponse(self) then
        leader[self] := self ||
        channels[self] := 
        [receiver \in DOMAIN channels[self] |-> 
            IF receiver \in IDSSmallerThan[self] THEN "Leader" ELSE ""];
        goto NormalExecution;
    end if;

\* Принимает "OK" сообщения и делает отправителя своим лидером.
\* Выполняется до тех пор, пока не узлы не перестанут посылать "OK".
CheckOkTimeout:
    if ~ReceivesResponseFromNewLeaders(self) then
        goto NormalExecution;
    end if;
AcceptNewLeader:
    with new_leader \in NewLeaders(self) do
        leader[self] := new_leader ||
        channels[new_leader][self] := "";
        goto CheckOkTimeout;
    end with;

\* В любой момент узел может получить сообщение о начале голосования.
\* При его получении он отправляет "OK" и сам пытается стать лидером.
NormalExecution:
    with sender \in MessageSenders(self) do
        if channels[sender][self] = "Election" then
            channels[self][sender] := "OK" ||
            channels[sender][self] := "";
            goto BecomeLeaderOrStartElection;
        elsif channels[sender][self] = "Leader" then
            channels[sender][self] := "" ||
            leader[self] := sender;
            goto NormalExecution;
        else
            channels[sender][self] := "";
        end if;
    end with;

Failed:
    skip;

end process;

end algorithm *)
\* BEGIN TRANSLATION (chksum(pcal) = "57599cbe" /\ chksum(tla) = "fd905753")
VARIABLES failed_leader, initiator, n, others_who_failed, channels, leader, 
          pc

(* define statement *)
IDSBiggerThan  == [id_1 \in IDS |-> {id_2 \in IDS : id_2 > id_1}]


IDSSmallerThan == [id_1 \in IDS |-> {id_2 \in IDS : id_2 < id_1}]


IDSBiggerThanExceptFailedLeader == [id \in IDS |-> IDSBiggerThan[id] \ {failed_leader}]



DoesNotReceiveAnyResponse(id) ==
    IDSBiggerThanExceptFailedLeader[id] \ others_who_failed = {}


NewLeaders(receiver) ==
    {sender \in IDS \ {receiver} : channels[sender][receiver] = "Leader"}


ReceivesResponseFromNewLeaders(receiver) ==
    LET old_leader == leader[receiver]
    IN
    \E new_leader \in IDSBiggerThanExceptFailedLeader[receiver] :
    /\ new_leader \notin others_who_failed
    /\ IF old_leader = failed_leader THEN TRUE ELSE new_leader > old_leader


ElectionInitiators(receiver) ==
    {sender \in IDS \ {receiver} : channels[sender][receiver] = "Election"}


MessageSenders(receiver) ==
    {sender \in IDS \ {receiver} : channels[sender][receiver] /= ""}

FailedIDS == others_who_failed \union {failed_leader}

WorkingIDS == IDS \ FailedIDS

IDThatShouldBecomeNewLeader ==
    CHOOSE new_leader \in WorkingIDS :
    \A id \in WorkingIDS \ {new_leader} : new_leader > id

AllAliveIDSAreCoordinatedByNewLeader ==
    \A id \in WorkingIDS : leader[id] = IDThatShouldBecomeNewLeader

EventuallySolved == []<>AllAliveIDSAreCoordinatedByNewLeader

CorrectMessages ==
    [](\A sender \in IDS : \A receiver \in IDS \ {sender} : channels[sender][receiver] \in Messages)


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
                        /\ IF ~ReceivesResponseFromNewLeaders(self)
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
