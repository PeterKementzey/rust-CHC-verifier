(set-logic HORN)
(set-option :fp.engine spacer)
(set-option :model true)

(declare-fun q1 (Int) Bool)
(declare-fun q2 (Int Int) Bool)
(declare-fun q3 (Int Int Int Int) Bool)
(declare-fun q4 (Int Int Int) Bool)
(declare-fun q5 (Int Int Int Int Int) Bool)
(declare-fun q6 (Int Int Int Int) Bool)
(declare-fun q7 (Int Int Int Int Int Int) Bool)
(declare-fun q8 (Int Int Int Int) Bool)
(declare-fun q9 (Int Int Int Int Int Int) Bool)
(declare-fun q10 (Int Int Int Int) Bool)
(declare-fun q11 (Int Int Int Int Int Int) Bool)
(declare-fun q12 (Int Int Int Int) Bool)
(declare-fun q13 (Int Int) Bool)
(declare-fun q14 () Bool)
(assert (forall ((|a| Int)) (=> (and (= |a| 1)) (q1 |a|))))
(assert (forall ((|a| Int) (|b| Int)) (=> (and (q1 |a|) (= |b| 2)) (q2 |a| |b|))))
(assert (forall ((|a| Int) (|a'| Int) (|b| Int) (|r_a*| Int) (|r_a^| Int)) (=> (and (q2 |a| |b|) (= |r_a*| |a|) (= |a'| |r_a^|)) (q3 |a'| |b| |r_a*| |r_a^|))))
(assert (forall ((|a| Int) (|b| Int) (|r_a*| Int) (|r_a^| Int)) (=> (and (q3 |a| |b| |r_a*| |r_a^|)) (q4 |b| |r_a*| |r_a^|))))
(assert (forall ((|b| Int) (|b'| Int) (|r_a*| Int) (|r_a^| Int) (|r_b*| Int) (|r_b^| Int)) (=> (and (q4 |b| |r_a*| |r_a^|) (= |r_b*| |b|) (= |b'| |r_b^|)) (q5 |b'| |r_a*| |r_a^| |r_b*| |r_b^|))))
(assert (forall ((|b| Int) (|r_a*| Int) (|r_a^| Int) (|r_b*| Int) (|r_b^| Int)) (=> (and (q5 |b| |r_a*| |r_a^| |r_b*| |r_b^|)) (q6 |r_a*| |r_a^| |r_b*| |r_b^|))))
(assert (forall ((|r_a'*| Int) (|r_a*| Int) (|r_a^| Int) (|r_b*| Int) (|r_b^| Int) (|temp*| Int) (|temp^| Int)) (=> (and (q6 |r_a*| |r_a^| |r_b*| |r_b^|) (= |temp*| |r_a*|) (= |r_a'*| |temp^|)) (q7 |r_a'*| |r_a^| |r_b*| |r_b^| |temp*| |temp^|))))
(assert (forall ((|r_a*| Int) (|r_a^| Int) (|r_b*| Int) (|r_b^| Int) (|temp*| Int) (|temp^| Int)) (=> (and (q7 |r_a*| |r_a^| |r_b*| |r_b^| |temp*| |temp^|) (= |r_a^| |r_a*|)) (q8 |r_b*| |r_b^| |temp*| |temp^|))))
(assert (forall ((|r_a*| Int) (|r_a^| Int) (|r_b'*| Int) (|r_b*| Int) (|r_b^| Int) (|temp*| Int) (|temp^| Int)) (=> (and (q8 |r_b*| |r_b^| |temp*| |temp^|) (= |r_a*| |r_b*|) (= |r_b'*| |r_a^|)) (q9 |r_b'*| |r_b^| |temp*| |temp^| |r_a*| |r_a^|))))
(assert (forall ((|r_a*| Int) (|r_a^| Int) (|r_b*| Int) (|r_b^| Int) (|temp*| Int) (|temp^| Int)) (=> (and (q9 |r_b*| |r_b^| |temp*| |temp^| |r_a*| |r_a^|) (= |r_b^| |r_b*|)) (q10 |temp*| |temp^| |r_a*| |r_a^|))))
(assert (forall ((|r_a*| Int) (|r_a^| Int) (|r_b*| Int) (|r_b^| Int) (|temp'*| Int) (|temp*| Int) (|temp^| Int)) (=> (and (q10 |temp*| |temp^| |r_a*| |r_a^|) (= |r_b*| |temp*|) (= |temp'*| |r_b^|)) (q11 |temp'*| |temp^| |r_a*| |r_a^| |r_b*| |r_b^|))))
(assert (forall ((|r_a*| Int) (|r_a^| Int) (|r_b*| Int) (|r_b^| Int) (|temp*| Int) (|temp^| Int)) (=> (and (q11 |temp*| |temp^| |r_a*| |r_a^| |r_b*| |r_b^|) (= |temp^| |temp*|)) (q12 |r_a*| |r_a^| |r_b*| |r_b^|))))
(assert (forall ((|r_a*| Int) (|r_a^| Int) (|r_b*| Int) (|r_b^| Int)) (=> (and (q12 |r_a*| |r_a^| |r_b*| |r_b^|)) (= |r_a*| 2))))
(assert (forall ((|r_a*| Int) (|r_a^| Int) (|r_b*| Int) (|r_b^| Int)) (=> (and (q12 |r_a*| |r_a^| |r_b*| |r_b^|) (= |r_a^| |r_a*|)) (q13 |r_b*| |r_b^|))))
(assert (forall ((|r_b*| Int) (|r_b^| Int)) (=> (and (q13 |r_b*| |r_b^|)) (= |r_b*| 1))))
(assert (forall ((|r_b*| Int) (|r_b^| Int)) (=> (and (q13 |r_b*| |r_b^|) (= |r_b^| |r_b*|)) q14)))

(check-sat)
(get-model)
