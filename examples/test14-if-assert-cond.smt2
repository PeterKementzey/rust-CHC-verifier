(set-logic HORN)
(set-option :fp.engine spacer)
(set-option :model true)

(declare-fun q1 (Int) Bool)
(declare-fun q2 (Int Int Int) Bool)
(declare-fun q3 (Int Int Int) Bool)
(declare-fun q4 (Int Int Int) Bool)
(declare-fun q5 (Int Int Int) Bool)
(declare-fun q6 (Int) Bool)
(declare-fun q7 () Bool)
(declare-fun q8 (Int) Bool)
(declare-fun q9 () Bool)
(assert (forall ((|x| Int)) (=> (and (= |x| 42)) (q1 |x|))))
(assert (forall ((|x| Int) (|x'| Int) (|y*| Int) (|y^| Int)) (=> (and (q1 |x|) (= |y*| |x|) (= |x'| |y^|)) (q2 |x'| |y*| |y^|))))
(assert (forall ((|x| Int) (|y'*| Int) (|y*| Int) (|y^| Int)) (=> (and (q2 |x| |y*| |y^|) (= |y'*| 51)) (q3 |x| |y'*| |y^|))))
(assert (forall ((|x| Int) (|y*| Int) (|y^| Int)) (=> (and (q3 |x| |y*| |y^|) (> |y*| 50)) (q4 |x| |y*| |y^|))))
(assert (forall ((|x| Int) (|y*| Int) (|y^| Int)) (=> (and (q4 |x| |y*| |y^|) (= |y^| |y*|)) (q6 |x|))))
(assert (forall ((|x| Int)) (=> (and (q6 |x|)) (> |x| 50))))
(assert (forall ((|x| Int)) (=> (and (q6 |x|)) q7)))
(assert (forall ((|x| Int) (|y*| Int) (|y^| Int)) (=> (and (q3 |x| |y*| |y^|) (not (> |y*| 50))) (q5 |x| |y*| |y^|))))
(assert (forall ((|x| Int) (|y*| Int) (|y^| Int)) (=> (and (q5 |x| |y*| |y^|) (= |y^| |y*|)) (q8 |x|))))
(assert (forall ((|x| Int)) (=> (and (q8 |x|)) (<= |x| 50))))
(assert (forall ((|x| Int)) (=> (and (q8 |x|)) q9)))
(assert (=> (and q7) q9))

(check-sat)
(get-model)
