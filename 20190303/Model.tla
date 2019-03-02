------------------- MODULE Model --------------------
EXTENDS Naturals, Sequences, TLC
VARIABLES power, actions
------------------------------------------------------

vars == << power, actions >>

on == "on"
off == "off"
Action == {on, off}

On ==
    \* guard
    /\ power = 0
    \* result
    /\ power' = 1
    /\ actions' = Append(actions, on)


Off ==
    \* guard
    /\ power = 1
    \* result
    /\ power' = 0
    /\ actions' = Append(actions, off)


Init ==
    /\ power = 0
    /\ actions = << >>

Next == 
    \/ On
    \/ Off

Spec == Init /\ [][Next]_vars

TypeInvariant ==
    /\ power \in 0..1
    /\ actions \in Seq(Action)

====================================
