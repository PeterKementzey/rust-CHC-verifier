(set-logic HORN)
(declare-fun q1 (Int) Bool)
(declare-fun q2 (Int) Bool)
(declare-fun q3 (Int Int) Bool)
(assert (forall ((|x| Int)) (=> (and (= |x| 42)) (q1 |x|))))
(assert (forall ((|x'| Int) (|x| Int)) (=> (and (q1 |x|) (= |x'| (+ |x| 1))) (q2 |x'|))))
(assert (forall ((|x| Int)) (=> (and (q2 |x|)) (= |x| 43))))
(assert (forall ((|y| Int) (|x| Int)) (=> (and (q2 |x|) (= |y| (* |x| 2))) (q3 |x| |y|))))
(assert (forall ((|y| Int) (|x| Int)) (=> (and (q3 |x| |y|)) (= |y| 86))))
(check-sat)
(get-model)