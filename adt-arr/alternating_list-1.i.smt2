;(set-logic HORN)

;(declare-datatypes () ((T (mk_T1 (s1 Int))))) ; sat
(declare-datatypes () ((T (mk_T1 (s1 Int)) (mk_T2 (s2 Int))))) ; error

(declare-fun I1 (Int) Bool)

(assert (forall ((y Int)) (or (not (= y (s1 (mk_T1 42)))) (< y 0))))

(check-sat)