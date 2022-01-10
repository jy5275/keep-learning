---- MODULE waf ----
EXTENDS Integers, TLC

VARIABLE redisVer, localVer, pc, threadVer, DBData, localData, threadData
CONSTANTS DataDomain, ProcSet, r1, r2, r3, t1, t2, t3

vars == << redisVer, localVer, pc, threadVer, localData, threadData, DBData>>

Init == /\ redisVer = -1 /\ localVer = -1 /\ localData = "" /\ DBData = ""
        /\ threadVer = [self \in ProcSet |-> -1]
        /\ pc = [self \in ProcSet |-> "A"]
        /\ threadData = [self \in ProcSet |-> ""]

RedisExpire == /\ threadData = [self \in ProcSet |-> DBData]
               /\ redisVer' = -1
               /\ DBData' \in DataDomain
               /\ UNCHANGED <<localVer, threadVer, localData, threadData, pc>>

ReadRedis(self) == /\ pc[self] = "A"
                   /\ threadVer' = [threadVer EXCEPT ![self] = redisVer]
                   /\ \/ /\ redisVer = -1
                         /\ pc' = [pc EXCEPT ![self] = "C"]
                      \/ /\ redisVer # -1
                         /\ pc' = [pc EXCEPT ![self] = "F"]
                   /\ UNCHANGED <<localVer, redisVer, localData, threadData, DBData>>

SetRedis(self) == /\ pc[self] = "C"
                  /\ \/ /\ redisVer # -1    \* SetNX failed => use existing redis
                        /\ redisVer' = redisVer
                        /\ threadVer' = [threadVer EXCEPT ![self] = redisVer] \* Not strictly the same!
                     \/ /\ redisVer = -1    \* SetNX ok => change redis
                        /\ redisVer' \in 1600012345..1600012350
                        /\ threadVer' = [threadVer EXCEPT ![self] = redisVer']
                  /\ pc' = [pc EXCEPT ![self] = "I"]
                  /\ UNCHANGED <<localVer, localData, threadData, DBData>>

CheckLocal(self) == /\ pc[self] = "F"
                    /\ \/ /\ localVer = threadVer[self]    \* Normal case
                          /\ threadData' = [threadData EXCEPT ![self] = localData]
                          /\ pc' = [pc EXCEPT ![self] = "H"]
                       \/ /\ localVer # threadVer[self]
                          /\ pc' = [pc EXCEPT ![self] = "I"]
                          /\ threadData' = threadData
                    /\ UNCHANGED <<redisVer, localVer, localData, threadVer, DBData>>

SetLocal(self) == /\ pc[self] = "I"
                  /\ localVer' = threadVer[self]
                  /\ localData' = DBData
                  /\ threadData' = [threadData EXCEPT ![self] = DBData]
                  /\ pc' = [pc EXCEPT ![self] = "H"]
                  /\ UNCHANGED <<redisVer, threadVer, DBData>>

ReturnResult(self) == /\ pc[self] = "H"
                    \*   /\ PrintT(<<threadVer[self], threadData[self]>>)
                      /\ pc' = [pc EXCEPT ![self] = "Done"]
                      /\ UNCHANGED <<redisVer, localVer, threadVer, localData, threadData, DBData>>

Again(self) == /\ pc[self] = "Done"
               /\ pc' = [pc EXCEPT ![self] = "A"]
               /\ UNCHANGED <<redisVer, localVer, threadVer, localData, threadData, DBData>>

Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

ReadRedisFor == \E self \in ProcSet: ReadRedis(self)
SetRedisFor == \E self \in ProcSet: SetRedis(self)
CheckLocalFor == \E self \in ProcSet: CheckLocal(self)
SetLocalFor == \E self \in ProcSet: SetLocal(self)
ReturnResultFor == \E self \in ProcSet: ReturnResult(self)

Proceed(t) == ReadRedis(t) \/ SetRedis(t) \/ CheckLocal(t) \/ SetLocal(t) \/ ReturnResult(t) \/ Again(t)

Next == \/ RedisExpire
        \/ \E t \in ProcSet: Proceed(t)
        \* \/ Terminating
        \* \/ \E self \in ProcSet: Again(self)

\* Termination == <>(\A self \in ProcSet: pc[self] = "Done")

FairForEveryone == \A t \in ProcSet: SF_vars(Proceed(t))

Spec == /\ Init /\ [][Next]_vars /\ FairForEveryone

symm == Permutations({r1, r2, r3}) \union Permutations({t1, t2, t3})

\* Cannot satisified since there may be consecutive DB writes
EventualCons == \A v \in DataDomain: DBData = v ~> threadData = [t \in ProcSet |-> v]
ECSpec == Spec /\ EventualCons

==== 
(*
A: threadVer := redisVer
   if threadVer == nil:         // Redis has expired
C:    threadVer := time()       // Try to set Redis
      res := SetNX(threadVer)
      if res == False:          // Another thread preceded
          threadVer = redisVer  // Use that redis var
   else
F:    if localVer == threadVer:
H:        return Success
X: localData = DBData
   localVer = threadVer
*)
