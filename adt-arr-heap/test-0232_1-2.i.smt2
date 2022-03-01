(set-logic HORN)
(set-info :source |
    Benchmark: C_VC
    Output by Princess (http://www.philipp.ruemmer.org/princess.shtml)
|)
(set-info :status sat)
(declare-heap Heap Addr HeapObject
 defObj
 ((HeapObject 0) (item 0)) (
  (
   (O_Int (getInt Int))
   (O_UInt (getUInt Int))
   (O_Addr (getAddr Addr))
   (O_item (getitem item))
   (defObj)
  )
  (
   (item (next Addr) (data Addr))
  )
))
(declare-fun inv_main13 (Heap Int Addr Int Int Addr) Bool)
(declare-fun inv_main14 (Heap Int Addr Int Int Addr) Bool)
(declare-fun inv_main16 (Heap Int Addr Int Int Addr Addr) Bool)
(declare-fun inv_main2 (Heap Int) Bool)
(declare-fun inv_main21 (Heap Int Addr Int) Bool)
(declare-fun inv_main23 (Heap Int Addr Int Addr) Bool)
(declare-fun inv_main28 (Heap Int Addr Int) Bool)
(assert (inv_main2 emptyHeap 0))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Addr) (var4 Int) (var5 Heap)) (or (not (and (inv_main13 var5 var4 var3 var2 var1 var0) (is-O_item (read var5 var0)))) (inv_main14 (write var5 var0 (O_item (item var3 (data (getitem (read var5 var0)))))) var4 var3 var2 var1 var0))))
(assert (forall ((var0 item) (var1 Int) (var2 Addr) (var3 Int) (var4 Int) (var5 Addr) (var6 Addr) (var7 Int) (var8 Int) (var9 Heap) (var10 Heap) (var11 Int) (var12 Int) (var13 Addr) (var14 Addr) (var15 Int) (var16 Int) (var17 Addr) (var18 Int) (var19 Heap)) (or (not (and (inv_main16 var19 var18 var17 var16 var15 var14 var13) (and (and (and (not (= var12 0)) (not (= var11 0))) (and (and (and (and (= var10 var9) (= var8 var7)) (= var6 var5)) (= var4 (+ var3 1))) (or (and (<= 0 (+ (+ 20 (* (- 1) var7)) (- 1))) (= var12 1)) (and (not (<= 0 (+ (+ 20 (* (- 1) var7)) (- 1)))) (= var12 0))))) (and (is-O_item (read var19 var14)) (and (and (and (and (and (= var9 (write var19 var14 (O_item (item (next (getitem (read var19 var14))) var13)))) (= var7 var18)) (= var2 var17)) (= var3 var16)) (= var1 var15)) (= var5 var14)))))) (inv_main13 (newHeap (alloc var10 (O_item var0))) (+ var8 1) var6 var4 2 (newAddr (alloc var10 (O_item var0)))))))
(assert (forall ((var0 item) (var1 Addr) (var2 Int) (var3 Heap) (var4 Int) (var5 Heap)) (or (not (and (inv_main2 var5 var4) (and (and (= var3 var5) (= var2 var4)) (= var1 nullAddr)))) (inv_main13 (newHeap (alloc var3 (O_item var0))) (+ var2 1) var1 0 2 (newAddr (alloc var3 (O_item var0)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Int) (var4 Heap) (var5 Int) (var6 Int) (var7 Addr) (var8 Addr) (var9 Int) (var10 Int) (var11 Addr) (var12 Int) (var13 Heap)) (or (not (and (inv_main16 var13 var12 var11 var10 var9 var8 var7) (and (<= 0 (+ (+ var6 1) (- 1))) (and (= var5 0) (and (is-O_item (read var13 var8)) (and (and (and (and (and (= var4 (write var13 var8 (O_item (item (next (getitem (read var13 var8))) var7)))) (= var3 var12)) (= var2 var11)) (= var6 var10)) (= var1 var9)) (= var0 var8))))))) (inv_main21 var4 var3 var0 (+ var6 1)))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Int) (var6 Int) (var7 Heap) (var8 Heap) (var9 Int) (var10 Int) (var11 Int) (var12 Addr) (var13 Addr) (var14 Int) (var15 Int) (var16 Addr) (var17 Int) (var18 Heap)) (or (not (and (inv_main16 var18 var17 var16 var15 var14 var13 var12) (and (<= 0 (+ var11 (- 1))) (and (and (and (= var10 0) (not (= var9 0))) (and (and (and (and (= var8 var7) (= var6 var5)) (= var4 var3)) (= var11 (+ var2 1))) (or (and (<= 0 (+ (+ 20 (* (- 1) var5)) (- 1))) (= var10 1)) (and (not (<= 0 (+ (+ 20 (* (- 1) var5)) (- 1)))) (= var10 0))))) (and (is-O_item (read var18 var13)) (and (and (and (and (and (= var7 (write var18 var13 (O_item (item (next (getitem (read var18 var13))) var12)))) (= var5 var17)) (= var1 var16)) (= var2 var15)) (= var0 var14)) (= var3 var13))))))) (inv_main21 var8 var6 var4 var11))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap) (var4 Addr) (var5 Int) (var6 Addr) (var7 Int) (var8 Heap) (var9 Int) (var10 Addr) (var11 Int) (var12 Addr) (var13 Int) (var14 Heap)) (or (not (and (inv_main23 var14 var13 var12 var11 var10) (and (<= 0 (+ (+ var9 (- 1)) (- 1))) (and (and (is-O_item (read var14 var12)) (and (and (and (and (= var8 (write var14 (data (getitem (read var14 var12))) defObj)) (= var7 var13)) (= var6 var12)) (= var5 var11)) (= var4 var10))) (and (and (and (and (= var3 (write var8 var6 defObj)) (= var2 var7)) (= var1 var6)) (= var9 var5)) (= var0 var4)))))) (inv_main28 var3 var2 var0 (+ var9 (- 1))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap) (var4 Addr) (var5 Int) (var6 Addr) (var7 Int) (var8 Heap) (var9 Int) (var10 Int) (var11 Addr) (var12 Int) (var13 Heap)) (or (not (and (inv_main28 var13 var12 var11 var10) (and (<= 0 (+ (+ var9 (- 1)) (- 1))) (and (and (is-O_item (read var13 var11)) (and (and (and (and (= var8 var13) (= var7 var12)) (= var6 var11)) (= var5 var10)) (= var4 (next (getitem (read var13 var11)))))) (and (and (and (and (= var3 (write var8 var6 defObj)) (= var2 var7)) (= var1 var6)) (= var9 var5)) (= var0 var4)))))) (inv_main28 var3 var2 var0 (+ var9 (- 1))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Int) (var4 Heap) (var5 Int) (var6 Int) (var7 Addr) (var8 Addr) (var9 Int) (var10 Int) (var11 Addr) (var12 Int) (var13 Heap)) (or (not (and (inv_main16 var13 var12 var11 var10 var9 var8 var7) (and (<= 0 (+ (+ var6 1) (- 1))) (and (not (<= 0 (+ (+ var6 1) (- 1)))) (and (= var5 0) (and (is-O_item (read var13 var8)) (and (and (and (and (and (= var4 (write var13 var8 (O_item (item (next (getitem (read var13 var8))) var7)))) (= var3 var12)) (= var2 var11)) (= var6 var10)) (= var1 var9)) (= var0 var8)))))))) (inv_main28 var4 var3 var0 (+ var6 1)))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Int) (var6 Int) (var7 Heap) (var8 Heap) (var9 Int) (var10 Int) (var11 Int) (var12 Addr) (var13 Addr) (var14 Int) (var15 Int) (var16 Addr) (var17 Int) (var18 Heap)) (or (not (and (inv_main16 var18 var17 var16 var15 var14 var13 var12) (and (<= 0 (+ var11 (- 1))) (and (not (<= 0 (+ var11 (- 1)))) (and (and (and (= var10 0) (not (= var9 0))) (and (and (and (and (= var8 var7) (= var6 var5)) (= var4 var3)) (= var11 (+ var2 1))) (or (and (<= 0 (+ (+ 20 (* (- 1) var5)) (- 1))) (= var10 1)) (and (not (<= 0 (+ (+ 20 (* (- 1) var5)) (- 1)))) (= var10 0))))) (and (is-O_item (read var18 var13)) (and (and (and (and (and (= var7 (write var18 var13 (O_item (item (next (getitem (read var18 var13))) var12)))) (= var5 var17)) (= var1 var16)) (= var2 var15)) (= var0 var14)) (= var3 var13)))))))) (inv_main28 var8 var6 var4 var11))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Addr) (var4 Int) (var5 Heap)) (or (not (and (inv_main14 var5 var4 var3 var2 var1 var0) (and (and (and (is-O_item (read var5 var0)) (not (= (next (getitem (read var5 var0))) nullAddr))) (is-O_item (read var5 var0))) (is-O_item (read var5 (next (getitem (read var5 var0)))))))) (inv_main16 var5 var4 var3 var2 var1 var0 (data (getitem (read var5 (next (getitem (read var5 var0))))))))))
(assert (forall ((var0 item) (var1 Addr) (var2 Int) (var3 Int) (var4 Addr) (var5 Int) (var6 Heap)) (or (not (and (inv_main14 var6 var5 var4 var3 var2 var1) (and (is-O_item (read var6 var1)) (= (next (getitem (read var6 var1))) nullAddr)))) (inv_main16 (newHeap (alloc var6 (O_item var0))) var5 var4 var3 var2 var1 (newAddr (alloc var6 (O_item var0)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Heap)) (or (not (and (inv_main21 var3 var2 var1 var0) (is-O_item (read var3 var1)))) (inv_main23 var3 var2 var1 var0 (next (getitem (read var3 var1)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Addr) (var4 Int) (var5 Heap)) (not (and (inv_main13 var5 var4 var3 var2 var1 var0) (not (is-O_item (read var5 var0)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Addr) (var4 Int) (var5 Heap)) (not (and (inv_main14 var5 var4 var3 var2 var1 var0) (not (is-O_item (read var5 var0)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Addr) (var4 Int) (var5 Heap)) (not (and (inv_main14 var5 var4 var3 var2 var1 var0) (and (and (is-O_item (read var5 var0)) (not (= (next (getitem (read var5 var0))) nullAddr))) (not (is-O_item (read var5 var0))))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Addr) (var4 Int) (var5 Heap)) (not (and (inv_main14 var5 var4 var3 var2 var1 var0) (and (and (and (is-O_item (read var5 var0)) (not (= (next (getitem (read var5 var0))) nullAddr))) (is-O_item (read var5 var0))) (not (is-O_item (read var5 (next (getitem (read var5 var0)))))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Addr) (var5 Int) (var6 Heap)) (not (and (inv_main16 var6 var5 var4 var3 var2 var1 var0) (not (is-O_item (read var6 var1)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Heap)) (not (and (inv_main21 var3 var2 var1 var0) (not (is-O_item (read var3 var1)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Int) (var4 Heap)) (not (and (inv_main23 var4 var3 var2 var1 var0) (not (is-O_item (read var4 var2)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Heap)) (not (and (inv_main28 var3 var2 var1 var0) (not (is-O_item (read var3 var1)))))))
(check-sat)
