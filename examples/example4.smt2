(set-logic HORN)
(set-option :fp.engine spacer)
(set-option :model true)

(declare-fun q1 (Int) Bool)
(declare-fun q2 (Int Int Int) Bool)
(declare-fun q3 (Int Int) Bool)
(declare-fun q4 (Int Int) Bool)
(declare-fun q5 (Int Int) Bool)
(declare-fun q6 (Int Int) Bool)
(declare-fun q7 () Bool)
(assert (forall ((|x| Int)) (=> (and (= |x| 42)) (q1 |x|))))
(assert (forall ((|x| Int) (|x'| Int) (|y*| Int) (|y^| Int)) (=> (and (q1 |x|) (= |y*| |x|) (= |x'| |y^|)) (q2 |x'| |y*| |y^|))))
(assert (forall ((|x| Int) (|y*| Int) (|y^| Int)) (=> (and (q2 |x| |y*| |y^|)) (q3 |y*| |y^|))))
(assert (forall ((|y*| Int) (|y^| Int)) (=> (and (q3 |y*| |y^|)) (= |y*| 42))))
(assert (forall ((|b*| Int) (|b^| Int) (|y*| Int) (|y^| Int)) (=> (and (q3 |y*| |y^|) (= |b*| |y*|) (= |b^| |y^|)) (q4 |b*| |b^|))))
(assert (forall ((|b*| Int) (|b^| Int)) (=> (and (q4 |b*| |b^|)) (q5 |b*| |b^|))))
(assert (forall ((|b*| Int) (|b^| Int) (|y*| Int) (|y^| Int)) (=> (and (q5 |b*| |b^|) (= |y*| |b*|) (= |y^| |b^|)) (q6 |y*| |y^|))))
(assert (forall ((|y*| Int) (|y^| Int)) (=> (and (q6 |y*| |y^|)) (= |y*| 42))))
(assert (forall ((|y*| Int) (|y^| Int)) (=> (and (q6 |y*| |y^|) (= |y^| |y*|)) q7)))

(check-sat)
(get-model)
