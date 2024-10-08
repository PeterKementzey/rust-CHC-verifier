(set-logic HORN)
(set-option :fp.engine spacer)
(set-option :model true)

(declare-fun q1 (Int) Bool)
(declare-fun q2 (Int Int Int) Bool)
(declare-fun q3 (Int Int Int Int) Bool)
(declare-fun q4 (Int Int Int Int Int Int) Bool)
(declare-fun q5 (Int Int Int Int Int) Bool)
(declare-fun q6 (Int Int Int) Bool)
(declare-fun q7 (Int Int Int Int Int) Bool)
(declare-fun q8 (Int Int Int Int) Bool)
(declare-fun q9 (Int Int) Bool)
(declare-fun q10 () Bool)
(assert (forall ((|x| Int)) (=> (and (= |x| 42)) (q1 |x|))))
(assert (forall ((|x| Int) (|x'| Int) (|y*| Int) (|y^| Int)) (=> (and (q1 |x|) (= |y*| |x|) (= |x'| |y^|)) (q2 |x'| |y*| |y^|))))
(assert (forall ((|a| Int) (|x| Int) (|y*| Int) (|y^| Int)) (=> (and (q2 |x| |y*| |y^|) (= |a| 0)) (q3 |x| |y*| |y^| |a|))))
(assert (forall ((|a| Int) (|a'| Int) (|b*| Int) (|b^| Int) (|x| Int) (|y*| Int) (|y^| Int)) (=> (and (q3 |x| |y*| |y^| |a|) (= |b*| |a|) (= |a'| |b^|)) (q4 |x| |y*| |y^| |a'| |b*| |b^|))))
(assert (forall ((|a| Int) (|b*| Int) (|b^| Int) (|x| Int) (|y*| Int) (|y^| Int)) (=> (and (q4 |x| |y*| |y^| |a| |b*| |b^|)) (q5 |x| |y*| |y^| |b*| |b^|))))
(assert (forall ((|b*| Int) (|b^| Int) (|x| Int) (|y*| Int) (|y^| Int)) (=> (and (q5 |x| |y*| |y^| |b*| |b^|)) (= |y*| 42))))
(assert (forall ((|b*| Int) (|b^| Int) (|x| Int) (|y*| Int) (|y^| Int)) (=> (and (q5 |x| |y*| |y^| |b*| |b^|) (= |y^| |y*|)) (q6 |x| |b*| |b^|))))
(assert (forall ((|b'*| Int) (|b*| Int) (|b^| Int) (|x| Int) (|y*| Int) (|y^| Int)) (=> (and (q6 |x| |b*| |b^|) (= |y*| |b*|) (= |b'*| |y^|)) (q7 |x| |b'*| |b^| |y*| |y^|))))
(assert (forall ((|b*| Int) (|b^| Int) (|x| Int) (|y*| Int) (|y^| Int)) (=> (and (q7 |x| |b*| |b^| |y*| |y^|)) (= |x| 42))))
(assert (forall ((|b*| Int) (|b^| Int) (|x| Int) (|y*| Int) (|y^| Int)) (=> (and (q7 |x| |b*| |b^| |y*| |y^|)) (q8 |b*| |b^| |y*| |y^|))))
(assert (forall ((|b*| Int) (|b^| Int) (|y*| Int) (|y^| Int)) (=> (and (q8 |b*| |b^| |y*| |y^|)) (= |y*| 0))))
(assert (forall ((|b*| Int) (|b^| Int) (|y*| Int) (|y^| Int)) (=> (and (q8 |b*| |b^| |y*| |y^|) (= |y^| |y*|)) (q9 |b*| |b^|))))
(assert (forall ((|b*| Int) (|b^| Int)) (=> (and (q9 |b*| |b^|)) (= |b*| 0))))
(assert (forall ((|b*| Int) (|b^| Int)) (=> (and (q9 |b*| |b^|) (= |b^| |b*|)) q10)))

(check-sat)
(get-model)
