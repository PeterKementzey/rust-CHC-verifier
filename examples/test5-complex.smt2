(set-logic HORN)
(set-option :fp.engine spacer)
(set-option :model true)

(declare-fun q1 (Int) Bool)
(declare-fun q2 () Bool)
(assert (forall ((|x| Int)) (=> (and (= |x| 0)) (q1 |x|))))
(assert (forall ((|x| Int)) (=> (and (q1 |x|)) (and (not (not (or (= 42 41) (and (< 3 4) (not (> 5 6)))))) (= |x| 0)))))
(assert (forall ((|x| Int)) (=> (and (q1 |x|)) q2)))

(check-sat)
(get-model)
