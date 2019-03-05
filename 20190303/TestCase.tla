------------------- MODULE TestCase --------------------
EXTENDS Naturals, Sequences, TLC, Model
------------------------------------------------------

TestCase == [
    name : STRING
  , scenario  : Seq(Action) \* アクション列
  , check: BOOLEAN          \* テスト成功条件
]

scenarios == <<
  [name |-> "Usecase1",
   scenario |-> <<on, off, on, off>>,
   check |-> power = 0
  ]
, [name |-> "BadCase1",
   scenario |-> <<on, on>>,
   check |-> FALSE  \* FALSEにすると、拒否すべきイベント列であることを意味する
  ]
>>

debug == [power |-> power]

\* 到達出来ないアクション列については何も表示されない
TestCaseConstraint == LET
    f(s) == 
    /\ Len(actions) <= Len(s.scenario)
    /\ actions = SubSeq(s.scenario, 1, Len(actions))
    /\ (actions = s.scenario) => 
        /\ PrintT((IF s.check THEN "SUCCESS: " ELSE "FAILURE: ")  \o s.name)
        /\ IF s.check THEN TRUE ELSE PrintT(debug)
         \* /\ Assert(s.check, s.name)
    IN Len(SelectSeq(scenarios, f)) > 0

TestCaseNext == IF TestCaseConstraint THEN Next ELSE UNCHANGED(vars)
TestCaseSpec == Init /\ [][TestCaseNext]_vars

====================================
