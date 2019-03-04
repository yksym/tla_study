------------------- MODULE Date --------------------
EXTENDS Naturals, Sequences, TLC
------------------------------------------------------

\* ignore leap second
\* 
\* only UTC

TIMESTAMP_START == 1546300800  \* This range prevents stackoverflows
TIMESTAMP_END   == 1893456000
YEAR_START == 2019
YEAR_END   == 2030
Timestamp       == TIMESTAMP_START..TIMESTAMP_END \* unix timestamp 0 means 01970-01-01 (Thu).
YearMonth    == [year : YEAR_START..YEAR_END, month : 1..12]

DAY_SEC == 24 * 3600
WEEK_SEC == DAY_SEC * 7

IsLeapYear(year) ==
    /\ year % 4 = 0
    /\ ~(year % 100 = 0 /\ year % 400 /= 0)

numOfDays(ym) == IF ym.month = 2
    THEN IF IsLeapYear(ym.year)
        THEN 29
        ELSE 28
    ELSE IF ym.month \in {4,6,9,11}
        THEN 30
        ELSE 31

prevMonth(ym) == IF ym.month = 1
    THEN [ym EXCEPT !.year = ym.year - 1, !.month = 12]
    ELSE [ym EXCEPT !.month = ym.month - 1]

nextMonth(ym) == IF ym.month = 12
    THEN [ym EXCEPT !.year = ym.year + 1, !.month = 1]
    ELSE [ym EXCEPT !.month = ym.month + 1]

yearMonth2Timestamp[ym \in YearMonth] == IF ym.year = YEAR_START /\ ym.month = 1
    THEN TIMESTAMP_START
    ELSE numOfDays(ym) * DAY_SEC + yearMonth2Timestamp[prevMonth(ym)]

_timestamp2YearMonth[remainSec \in Nat, ym \in YearMonth] ==  IF remainSec < numOfDays(ym) * DAY_SEC
    THEN ym
    ELSE _timestamp2YearMonth[(remainSec - numOfDays(ym) * DAY_SEC), nextMonth(ym)]

timestamp2YearMonth[t \in Timestamp] == _timestamp2YearMonth[t - TIMESTAMP_START, [year |-> YEAR_START, month |-> 1]]

startOfWeek(t) == LET d == t \div DAY_SEC
                      offset == t % DAY_SEC
                  IN (t - (DAY_SEC * ((d + 4) % 7))) - offset

startOfMonth(t) == yearMonth2Timestamp[timestamp2YearMonth[t]]

\* https://url-c.com/tc/
\* date -u --date "@0"
\* date -u -d '06/12/2012 07:21:22' +"%s"
Test == 
    /\ timestamp2YearMonth[1551674281] = [year |-> 2019, month |-> 3]
    /\ timestamp2YearMonth[TIMESTAMP_START] = [year |-> YEAR_START, month |-> 1]
    /\ timestamp2YearMonth[1577836800-1] = [year |-> 2019, month |-> 12]
    /\ timestamp2YearMonth[1577836800] = [year |-> 2020, month |-> 1]
    /\ timestamp2YearMonth[1609459200-1] = [year |-> 2020, month |-> 12]
    /\ timestamp2YearMonth[1609459200] = [year |-> 2021, month |-> 1]
    /\ yearMonth2Timestamp[[year |-> 2019, month |-> 1]] = TIMESTAMP_START
    /\ yearMonth2Timestamp[[year |-> 2020, month |-> 1]] = 1577836800
    /\ yearMonth2Timestamp[[year |-> 2021, month |-> 1]] = 1609459200
    /\ startOfWeek(1551676169) = 1551571200
    /\ startOfMonth(1551676169) = 1551398400

=======================================================