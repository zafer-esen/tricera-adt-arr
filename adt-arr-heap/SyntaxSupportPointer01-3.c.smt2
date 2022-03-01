(set-logic HORN)
(set-info :source |
    Benchmark: C_VC
    Output by Princess (http://www.philipp.ruemmer.org/princess.shtml)
|)
(set-info :status sat)
(declare-heap Heap Addr HeapObject
 defObj
 ((HeapObject 0)) (
  (
   (O_Int (getInt Int))
   (O_UInt (getUInt Int))
   (O_Addr (getAddr Addr))
   (defObj)
  )
))
(declare-fun inv_main2 (Heap) Bool)
(declare-fun inv_main3 (Heap Addr) Bool)
(declare-fun inv_main5 (Heap Addr) Bool)
(assert (inv_main2 emptyHeap))
(assert (forall ((var0 Int) (var1 Heap)) (or (not (inv_main2 var1)) (inv_main3 (newHeap (alloc var1 (O_Int var0))) (newAddr (alloc var1 (O_Int var0)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Heap)) (or (not (and (inv_main5 var4 var3) (and (is-O_Int (read var4 var3)) (and (and (= var2 var4) (= var1 var3)) (= var0 (getInt (read var4 var3))))))) (inv_main3 (write var2 var1 (O_Int (+ var0 (- 1)))) var1))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Addr) (var4 Heap)) (or (not (and (inv_main3 var4 var3) (and (and (<= 0 var2) (is-O_Int (read var4 var3))) (and (and (= var1 var4) (= var0 var3)) (= var2 (getInt (read var4 var3))))))) (inv_main5 var1 var0))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main3 var1 var0) (not (is-O_Int (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main5 var1 var0) (not (is-O_Int (read var1 var0)))))))
(check-sat)
