\* https://learntla.com/pluscal/a-simple-spec/

---- MODULE basic ----
EXTENDS TLC

(* --algorithm hello_world
variable s \in {"Hello", "World!"}, n \in {1,2,3};
begin
  A:
    print s;
end algorithm; *)

\* BEGIN TRANSLATION (chksum(pcal) = "e36882d2" /\ chksum(tla) = "82df0cf2")
VARIABLES s, n, pc

vars == << s, n, pc >>

Init == (* Global variables *)
        /\ s \in {"Hello", "World!"}
        /\ n \in {1,2,3}
        /\ pc = "A"

A == /\ pc = "A"
     /\ PrintT(s)
     /\ pc' = "Done"
     /\ UNCHANGED << s, n >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == A
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

====
