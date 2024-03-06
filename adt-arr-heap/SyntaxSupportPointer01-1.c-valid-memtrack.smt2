(set-logic HORN)
(set-info :source |
    Benchmark: C_VC
    Output by Princess (http://www.philipp.ruemmer.org/princess.shtml)
|)
(set-info :status unknown)
(declare-datatype bool (
  (true)
  (false)
))
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
(declare-fun inv_main (Heap Addr Addr) Bool)
(declare-fun inv_main14_2 (Heap Addr) Bool)
(declare-fun inv_main20_9 (Heap Addr Int) Bool)
(assert (forall ((var0 Addr) (var1 Heap)) (or (not (and (= var1 emptyHeap) (= var0 nullAddr))) (inv_main14_2 var1 var0))))
(assert (forall ((var0 Int) (var1 Heap) (var2 Addr) (var3 Bool) (var4 Addr) (var5 Int) (var6 Heap) (var7 Addr) (var8 Heap)) (or (not (and (inv_main14_2 var8 var7) (and (and (and (= var6 (newHeap (alloc var8 (O_Int var5)))) (or (and var3 (= var4 (newAddr (alloc var8 (O_Int var5))))) (and (not var3) (= var4 var7)))) (= var2 (newAddr (alloc var8 (O_Int var5))))) (= var1 (write var6 var2 (O_Int var0)))))) (inv_main var1 var4 var2))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Heap)) (or (not (and (inv_main var11 var10 var9) (and (and (and (and (and (= var8 var7) (= var6 var5)) (= var4 var3)) (= var2 (getInt (read var7 var3)))) (and (<= 0 var1) (and (and (and (= var7 var11) (= var5 var10)) (= var3 var9)) (= var1 (getInt (read var11 var9)))))) (= var0 (write var8 var4 (O_Int (+ var2 (- 1)))))))) (inv_main var0 var6 var4))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Int) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main var10 var9 var8) (and (and (and (not (<= 0 var7)) (and (and (and (= var6 var10) (= var5 var9)) (= var4 var8)) (= var7 (getInt (read var10 var8))))) (and (and (= var3 (write var6 var4 defObj)) (or (and (= var5 var4) (= var2 nullAddr)) (and (not (= var5 var4)) (= var2 var5)))) (= var1 var4))) (= var0 0)))) (inv_main20_9 var3 var2 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap)) (not (and (inv_main20_9 var2 var1 var0) (not (= var1 nullAddr))))))
(check-sat)
