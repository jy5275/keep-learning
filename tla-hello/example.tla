---- MODULE example ----
EXTENDS Integers

VARIABLE i,cnt

vars == << i,cnt >>

Init == i = 0 /\ cnt = 0

Circle == /\ IF i = 5
                THEN i' = 0
                ELSE i' = i + 1
          /\ cnt' = cnt + 1

Break == /\ i = 5
         /\ i' = 6
         /\ cnt' = cnt + 1

Explore == /\ i > 5
           /\ i' = i + 1
           /\ cnt' = cnt + 1

Next == Circle \/ Break \/ Explore

Live == WF_vars(Break)

Spec == Init /\ [][Next]_vars /\ Live

Con == i <= 100

====
