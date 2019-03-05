------------------- MODULE String --------------------
EXTENDS Naturals, Sequences, TLC

digitc[n \in 0..9] ==
IF n=0 THEN "0"
ELSE IF n=1 THEN "1"
ELSE IF n=2 THEN "2"
ELSE IF n=3 THEN "3"
ELSE IF n=4 THEN "4"
ELSE IF n=5 THEN "5"
ELSE IF n=6 THEN "6"
ELSE IF n=7 THEN "7"
ELSE IF n=8 THEN "8"
ELSE "9"

toString[n \in Nat] == IF n < 10
    THEN digitc[n]
        ELSE toString[n \div 10] \o digitc[n % 10]

====================================
