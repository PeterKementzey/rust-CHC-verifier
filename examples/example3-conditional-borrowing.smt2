(set-logic HORN)
(set-option :fp.engine spacer)
(set-option :model true)

(declare-fun q1 (Int) Bool)
(declare-fun q2 (Int Int) Bool)
(declare-fun q3 (Int Int Int) Bool)
(declare-fun q4 (Int Int Int Int Int) Bool)
(declare-fun q5 (Int Int Int Int) Bool)
(declare-fun q6 (Int Int) Bool)
(declare-fun q7 (Int Int) Bool)
(declare-fun q8 (Int Int) Bool)
(declare-fun q9 (Int Int Int Int) Bool)
(declare-fun q10 (Int Int Int Int) Bool)
(declare-fun q11 (Int Int Int Int) Bool)
(declare-fun q12 (Int Int) Bool)
(declare-fun q13 (Int) Bool)
(declare-fun q14 () Bool)
(assert (forall ((|x| Int)) (=> (and (= |x| 1)) (q1 |x|))))
(assert (forall ((|x| Int) (|y| Int)) (=> (and (q1 |x|) (= |y| 2)) (q2 |x| |y|))))
(assert (forall ((|unused| Int) (|x| Int) (|y| Int)) (=> (and (q2 |x| |y|) (= |unused| 0)) (q3 |x| |y| |unused|))))
(assert (forall ((|r*| Int) (|r^| Int) (|unused| Int) (|unused'| Int) (|x| Int) (|y| Int)) (=> (and (q3 |x| |y| |unused|) (= |r*| |unused|) (= |unused'| |r^|)) (q4 |x| |y| |unused'| |r*| |r^|))))
(assert (forall ((|r*| Int) (|r^| Int) (|unused| Int) (|x| Int) (|y| Int)) (=> (and (q4 |x| |y| |unused| |r*| |r^|)) (q5 |x| |y| |r*| |r^|))))
(assert (forall ((|r*| Int) (|r^| Int) (|x| Int) (|y| Int)) (=> (and (q5 |x| |y| |r*| |r^|) (= |r^| |r*|)) (q6 |x| |y|))))
(assert (forall ((|$rand0| Int) (|x| Int) (|y| Int)) (=> (and (q6 |x| |y|) (> |x| |$rand0|)) (q7 |x| |y|))))
(assert (forall ((|r*| Int) (|r^| Int) (|x| Int) (|x'| Int) (|y| Int)) (=> (and (q7 |x| |y|) (= |r*| |x|) (= |x'| |r^|)) (q9 |x'| |y| |r*| |r^|))))
(assert (forall ((|$rand0| Int) (|x| Int) (|y| Int)) (=> (and (q6 |x| |y|) (not (> |x| |$rand0|))) (q8 |x| |y|))))
(assert (forall ((|r*| Int) (|r^| Int) (|x| Int) (|y| Int) (|y'| Int)) (=> (and (q8 |x| |y|) (= |r*| |y|) (= |y'| |r^|)) (q10 |x| |y'| |r*| |r^|))))
(assert (forall ((|r*| Int) (|r^| Int) (|x| Int) (|y| Int)) (=> (and (q9 |x| |y| |r*| |r^|)) (q10 |x| |y| |r*| |r^|))))
(assert (forall ((|r'*| Int) (|r*| Int) (|r^| Int) (|x| Int) (|y| Int)) (=> (and (q10 |x| |y| |r*| |r^|) (= |r'*| 3)) (q11 |x| |y| |r'*| |r^|))))
(assert (forall ((|r*| Int) (|r^| Int) (|x| Int) (|y| Int)) (=> (and (q11 |x| |y| |r*| |r^|) (= |r^| |r*|)) (q12 |x| |y|))))
(assert (forall ((|x| Int) (|y| Int)) (=> (and (q12 |x| |y|)) (or (and (= |x| 3) (= |y| 2)) (and (= |x| 1) (= |y| 3))))))
(assert (forall ((|x| Int) (|y| Int)) (=> (and (q12 |x| |y|)) (q13 |y|))))
(assert (forall ((|y| Int)) (=> (and (q13 |y|)) q14)))

(check-sat)
(get-model)