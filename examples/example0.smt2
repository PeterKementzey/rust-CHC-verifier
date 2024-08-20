(set-logic HORN)
(set-option :fp.engine spacer)
(set-option :model true)

(declare-fun q1 (Int) Bool)
(declare-fun q2 (Int Int Int) Bool)
(declare-fun q3 (Int Int Int) Bool)
(declare-fun q4 (Int) Bool)
(declare-fun q5 () Bool)
(assert (forall ((|x| Int)) (=> (and (= |x| 42)) (q1 |x|))))
(assert (forall ((|r*| Int) (|r^| Int) (|x| Int) (|x'| Int)) (=> (and (q1 |x|) (= |r*| |x|) (= |x'| |r^|)) (q2 |x'| |r*| |r^|))))
(assert (forall ((|r'*| Int) (|r*| Int) (|r^| Int) (|x| Int)) (=> (and (q2 |x| |r*| |r^|) (= |r'*| (+ |r*| 1))) (q3 |x| |r'*| |r^|))))
(assert (forall ((|r*| Int) (|r^| Int) (|x| Int)) (=> (and (q3 |x| |r*| |r^|) (= |r^| |r*|)) (q4 |x|))))
(assert (forall ((|x| Int)) (=> (and (q4 |x|)) (= |x| 43))))
(assert (forall ((|x| Int)) (=> (and (q4 |x|)) q5)))

(check-sat)
(get-model)