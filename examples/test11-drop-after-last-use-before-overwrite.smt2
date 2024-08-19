(set-logic HORN)
(set-option :fp.engine spacer)
(set-option :model true)

(declare-fun q1 (Int) Bool)
(declare-fun q2 (Int Int) Bool)
(declare-fun q3 (Int Int Int Int) Bool)
(declare-fun q4 (Int Int Int Int) Bool)
(declare-fun q5 (Int Int) Bool)
(declare-fun q6 (Int) Bool)
(declare-fun q7 (Int Int Int) Bool)
(declare-fun q8 (Int Int) Bool)
(declare-fun q9 () Bool)
(assert (forall ((|a| Int)) (=> (and (= |a| 4)) (q1 |a|))))
(assert (forall ((|a| Int) (|b| Int)) (=> (and (q1 |a|) (= |b| 0)) (q2 |a| |b|))))
(assert (forall ((|a| Int) (|a'| Int) (|b| Int) (|r_a*| Int) (|r_a^| Int)) (=> (and (q2 |a| |b|) (= |r_a*| |a|) (= |a'| |r_a^|)) (q3 |a'| |b| |r_a*| |r_a^|))))
(assert (forall ((|a| Int) (|b| Int) (|r_a'*| Int) (|r_a*| Int) (|r_a^| Int)) (=> (and (q3 |a| |b| |r_a*| |r_a^|) (= |r_a'*| 3)) (q4 |a| |b| |r_a'*| |r_a^|))))
(assert (forall ((|a| Int) (|b| Int) (|r_a*| Int) (|r_a^| Int)) (=> (and (q4 |a| |b| |r_a*| |r_a^|) (= |r_a^| |r_a*|)) (q5 |a| |b|))))
(assert (forall ((|a| Int) (|b| Int)) (=> (and (q5 |a| |b|)) (= |a| 3))))
(assert (forall ((|a| Int) (|b| Int)) (=> (and (q5 |a| |b|)) (q6 |b|))))
(assert (forall ((|b| Int) (|b'| Int) (|r_a*| Int) (|r_a^| Int)) (=> (and (q6 |b|) (= |r_a*| |b|) (= |b'| |r_a^|)) (q7 |b'| |r_a*| |r_a^|))))
(assert (forall ((|b| Int) (|r_a*| Int) (|r_a^| Int)) (=> (and (q7 |b| |r_a*| |r_a^|)) (q8 |r_a*| |r_a^|))))
(assert (forall ((|r_a*| Int) (|r_a^| Int)) (=> (and (q8 |r_a*| |r_a^|)) (= |r_a*| 0))))
(assert (forall ((|r_a*| Int) (|r_a^| Int)) (=> (and (q8 |r_a*| |r_a^|) (= |r_a^| |r_a*|)) q9)))

(check-sat)
(get-model)