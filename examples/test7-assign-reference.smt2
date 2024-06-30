(set-logic HORN)
(set-option :fp.engine spacer)
(set-option :model true)

(declare-fun q1 (Int) Bool)
(declare-fun q2 (Int Int Int) Bool)
(declare-fun q3 (Int Int Int Int) Bool)
(declare-fun q4 (Int Int Int Int Int Int) Bool)
(declare-fun q5 (Int Int Int Int Int Int) Bool)
(declare-fun q6 (Int Int Int Int Int Int) Bool)
(declare-fun q7 (Int Int Int Int) Bool)
(declare-fun q8 (Int Int Int Int) Bool)
(declare-fun q9 (Int Int Int Int) Bool)
(declare-fun q10 (Int Int) Bool)
(declare-fun q11 (Int) Bool)
(declare-fun q12 () Bool)
(assert (forall ((|x| Int)) (=> (and (= |x| 42)) (q1 |x|))))
(assert (forall ((|x| Int) (|x'| Int) (|y*| Int) (|y^| Int)) (=> (and (q1 |x|) (= |y*| |x|) (= |x'| |y^|)) (q2 |x'| |y*| |y^|))))
(assert (forall ((|a| Int) (|x| Int) (|y*| Int) (|y^| Int)) (=> (and (q2 |x| |y*| |y^|) (= |a| 0)) (q3 |x| |y*| |y^| |a|))))
(assert (forall ((|a| Int) (|a'| Int) (|b*| Int) (|b^| Int) (|x| Int) (|y*| Int) (|y^| Int)) (=> (and (q3 |x| |y*| |y^| |a|) (= |b*| |a|) (= |a'| |b^|)) (q4 |x| |y*| |y^| |a'| |b*| |b^|))))
(assert (forall ((|a| Int) (|b*| Int) (|b^| Int) (|x| Int) (|y'*| Int) (|y*| Int) (|y^| Int)) (=> (and (q4 |x| |y*| |y^| |a| |b*| |b^|) (= |y'*| (+ |y*| 1))) (q5 |x| |y'*| |y^| |a| |b*| |b^|))))
(assert (forall ((|a| Int) (|b'*| Int) (|b*| Int) (|b^| Int) (|x| Int) (|y*| Int) (|y^| Int)) (=> (and (q5 |x| |y*| |y^| |a| |b*| |b^|) (= |b'*| 4)) (q6 |x| |y*| |y^| |a| |b'*| |b^|))))
(assert (forall ((|a| Int) (|b*| Int) (|b^| Int) (|x| Int) (|y*| Int) (|y^| Int)) (=> (and (q6 |x| |y*| |y^| |a| |b*| |b^|) (= |y^| |y*|)) (q7 |x| |a| |b*| |b^|))))
(assert (forall ((|a| Int) (|b*| Int) (|b^| Int) (|x| Int) (|y*| Int) (|y^| Int)) (=> (and (q7 |x| |a| |b*| |b^|) (= |y*| |b*|) (= |y^| |b^|)) (q8 |x| |a| |y*| |y^|))))
(assert (forall ((|a| Int) (|x| Int) (|y'*| Int) (|y*| Int) (|y^| Int)) (=> (and (q8 |x| |a| |y*| |y^|) (= |y'*| (+ |y*| 1))) (q9 |x| |a| |y'*| |y^|))))
(assert (forall ((|a| Int) (|x| Int) (|y*| Int) (|y^| Int)) (=> (and (q9 |x| |a| |y*| |y^|) (= |y^| |y*|)) (q10 |x| |a|))))
(assert (forall ((|a| Int) (|x| Int)) (=> (and (q10 |x| |a|)) (= |x| 43))))
(assert (forall ((|a| Int) (|x| Int)) (=> (and (q10 |x| |a|)) (q11 |a|))))
(assert (forall ((|a| Int)) (=> (and (q11 |a|)) (= |a| 5))))
(assert (forall ((|a| Int)) (=> (and (q11 |a|)) q12)))

(check-sat)
(get-model)