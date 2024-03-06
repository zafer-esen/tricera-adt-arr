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
   (O_AddrRange (getAddrRange AddrRange))
   (defObj)
  )
))
(declare-fun inv_main (Heap Addr) Bool)
(declare-fun inv_main14_2 (Heap) Bool)
(declare-fun inv_main15_8 (Heap Addr) Bool)
(declare-fun inv_main17_3 (Heap Addr Int) Bool)
(declare-fun inv_main_3 (Heap Addr) Bool)
(assert (forall ((var0 Heap)) (or (not (= var0 emptyHeap)) (inv_main14_2 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap)) (or (not (and (inv_main_3 var2 var1) (and (is-O_Int (read var2 var1)) (= var0 (getInt (read var2 var1)))))) (inv_main17_3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Addr) (var4 Heap)) (or (not (and (inv_main var4 var3) (and (and (<= 0 var2) (is-O_Int (read var4 var3))) (and (and (= var1 var4) (= var0 var3)) (= var2 (getInt (read var4 var3))))))) (inv_main_3 var1 var0))))
(assert (forall ((var0 Int) (var1 Heap) (var2 Addr) (var3 Heap)) (or (not (and (inv_main15_8 var3 var2) (and (and (is-O_Int (read var3 var2)) (is-O_Int (read var3 var2))) (= var1 (write var3 var2 (O_Int var0)))))) (inv_main var1 var2))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Addr) (var3 Heap)) (or (not (and (inv_main17_3 var3 var2 var1) (and (is-O_Int (read var3 var2)) (= var0 (write var3 var2 (O_Int (+ var1 (- 1)))))))) (inv_main var0 var2))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Heap) (var3 Heap)) (or (not (and (inv_main14_2 var3) (and (= var2 (newHeap (alloc var3 (O_Int var1)))) (= var0 (newAddr (alloc var3 (O_Int var1))))))) (inv_main15_8 var2 var0))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main15_8 var1 var0) (not (is-O_Int (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main15_8 var1 var0) (and (is-O_Int (read var1 var0)) (not (is-O_Int (read var1 var0))))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main var1 var0) (not (is-O_Int (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main_3 var1 var0) (not (is-O_Int (read var1 var0)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap)) (not (and (inv_main17_3 var2 var1 var0) (not (is-O_Int (read var2 var1)))))))
(check-sat)
