(set-logic HORN)
(set-option :fp.engine spacer)
(set-option :model true)

(declare-fun q1 (Int) Bool)
(declare-fun q2 (Int Int) Bool)
(declare-fun q3 (Int) Bool)
(declare-fun q4 () Bool)
(assert (forall ((|x| Int)) (=> (and (= |x| 42)) (q1 |x|))))
(assert (forall ((|x| Int) (|y| Int)) (=> (and (q1 |x|) (= |y| 4)) (q2 |x| |y|))))
(assert (forall ((|x| Int) (|y| Int)) (=> (and (q2 |x| |y|)) (= |x| |x|))))
(assert (forall ((|x| Int) (|y| Int)) (=> (and (q2 |x| |y|)) (distinct |y| |x|))))
(assert (forall ((|x| Int) (|y| Int)) (=> (and (q2 |x| |y|)) (< |y| |x|))))
(assert (forall ((|x| Int) (|y| Int)) (=> (and (q2 |x| |y|)) (<= |y| |x|))))
(assert (forall ((|x| Int) (|y| Int)) (=> (and (q2 |x| |y|)) (> |x| |y|))))
(assert (forall ((|x| Int) (|y| Int)) (=> (and (q2 |x| |y|)) (>= |x| |y|))))
(assert (forall ((|x| Int) (|y| Int)) (=> (and (q2 |x| |y|)) (q3 |y|))))
(assert (forall ((|y| Int)) (=> (and (q3 |y|)) q4)))

(check-sat)
(get-model)
