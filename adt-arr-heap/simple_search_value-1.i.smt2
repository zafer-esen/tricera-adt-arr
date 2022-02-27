(set-logic HORN)
(set-info :source |
    Benchmark: C_VC
    Output by Princess (http://www.philipp.ruemmer.org/princess.shtml)
|)
(set-info :status sat)
(declare-heap Heap Addr HeapObject
 defObj
 ((HeapObject 0) (node 0)) (
  (
   (O_Int (getInt Int))
   (O_Addr (getAddr Addr))
   (O_node (getnode node))
   (defObj)
  )
  (
   (node (h Int) (n Addr))
  )
))
(declare-fun inv_main12 (Heap Addr Addr Addr Int) Bool)
(declare-fun inv_main13 (Heap Addr Addr Addr Int) Bool)
(declare-fun inv_main14 (Heap Addr Addr Addr Int) Bool)
(declare-fun inv_main2 (Heap) Bool)
(declare-fun inv_main20 (Heap Addr Addr Addr Int) Bool)
(declare-fun inv_main23 (Heap Addr Addr Addr Int Int) Bool)
(declare-fun inv_main26 (Heap Addr Addr Addr Int) Bool)
(declare-fun inv_main29 (Heap Addr Addr Addr Int) Bool)
(declare-fun inv_main35 (Heap Addr Addr Addr Int Int Int) Bool)
(declare-fun inv_main36 (Heap Addr Addr Addr Int Int Int) Bool)
(declare-fun inv_main40 (Heap Addr Addr Addr Int Int Int) Bool)
(declare-fun inv_main46 (Heap Addr Addr Addr Int Int Int) Bool)
(declare-fun inv_main7 (Heap Addr Int) Bool)
(assert (inv_main2 emptyHeap))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Int)) (or (not (inv_main13 var1 var0 var2 var3 var4)) (inv_main29 (write var1 var3 (O_node (node var4 (n (getnode (read var1 var3)))))) var0 var2 var3 var4))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Int)) (or (not (inv_main20 var1 var0 var2 var3 var4)) (inv_main26 (write var1 var3 (O_node (node (h (getnode (read var1 var3))) var2))) var0 var2 var3 var4))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Int)) (or (not (and (inv_main12 var2 var1 var3 var4 var5) (and (= var0 0) (not (<= 0 (+ (+ 10 (* (- 1) var5)) (- 1))))))) (inv_main13 var2 var1 var3 var4 var5))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Int) (var10 Int)) (or (not (and (inv_main26 var2 var1 var5 var6 var9) (and (and (and (and (and (= var0 var2) (= var8 var1)) (= var4 var5)) (= var7 var6)) (= var10 var9)) (= var3 (n (getnode (read var2 var6))))))) (inv_main12 var0 var8 var4 var3 (+ var10 1)))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 node) (var3 Addr) (var4 Heap)) (or (not (and (inv_main2 var0) (and (not (= var3 nullAddr)) (and (= var4 (newHeap (alloc var0 (O_node var2)))) (= var3 (newAddr (alloc var0 (O_node var2)))))))) (inv_main12 var4 var3 var1 var3 0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap)) (or (not (inv_main7 var2 var1 var0)) (inv_main7 var2 var1 var0))))
(assert (forall ((var0 Heap) (var1 node) (var2 Heap) (var3 Addr)) (or (not (and (inv_main2 var0) (and (= var3 nullAddr) (and (= var2 (newHeap (alloc var0 (O_node var1)))) (= var3 (newAddr (alloc var0 (O_node var1)))))))) (inv_main7 var2 var3 1))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Int) (var7 Int) (var8 Int) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Heap) (var13 Int) (var14 Int)) (or (not (and (inv_main40 var1 var0 var3 var4 var6 var14 var7) (and (not (= var10 nullAddr)) (and (and (and (and (and (and (and (= var12 var1) (= var5 var0)) (= var9 var3)) (= var11 var4)) (= var13 var6)) (= var8 var14)) (= var2 var7)) (= var10 (n (getnode (read var1 var4)))))))) (inv_main35 var12 var5 var9 var10 var13 var8 var2))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Int) (var9 Addr)) (or (not (and (inv_main29 var2 var1 var5 var6 var8) (and (not (= var4 nullAddr)) (and (and (and (and (= var7 (write var2 var6 (O_node (node (h (getnode (read var2 var6))) 0)))) (= var4 var1)) (= var3 var5)) (= var9 var6)) (= var0 var8))))) (inv_main35 var7 var4 var3 var4 var0 0 0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Int) (var7 Int) (var8 Int) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Heap) (var13 Int) (var14 Int)) (or (not (and (inv_main40 var1 var0 var3 var4 var6 var14 var7) (and (and (or (= var2 0) (= var8 0)) (= var10 nullAddr)) (and (and (and (and (and (and (and (= var12 var1) (= var5 var0)) (= var9 var3)) (= var11 var4)) (= var13 var6)) (= var8 var14)) (= var2 var7)) (= var10 (n (getnode (read var1 var4)))))))) (inv_main46 var12 var5 var9 var10 var13 var8 var2))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Int) (var9 Addr)) (or (not (and (inv_main29 var2 var1 var5 var6 var8) (and (= var4 nullAddr) (and (and (and (and (= var7 (write var2 var6 (O_node (node (h (getnode (read var2 var6))) 0)))) (= var4 var1)) (= var3 var5)) (= var9 var6)) (= var0 var8))))) (inv_main46 var7 var4 var3 var4 var0 0 0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Int) (var4 Heap) (var5 Heap) (var6 Addr) (var7 Int) (var8 Addr) (var9 Addr) (var10 Int) (var11 Int) (var12 Addr) (var13 Addr) (var14 Int)) (or (not (and (inv_main36 var4 var0 var8 var9 var10 var14 var11) (and (= var2 6) (and (and (and (and (and (and (and (= var5 var4) (= var12 var0)) (= var6 var8)) (= var13 var9)) (= var1 var10)) (= var3 var14)) (= var7 var11)) (= var2 (h (getnode (read var4 var9)))))))) (inv_main40 var5 var12 var6 var13 var1 var3 1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Int) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Int) (var9 Int) (var10 Heap) (var11 Int) (var12 Addr) (var13 Int) (var14 Int)) (or (not (and (inv_main36 var2 var1 var4 var5 var8 var14 var9) (and (not (= var13 6)) (and (and (and (and (and (and (and (= var10 var2) (= var12 var1)) (= var7 var4)) (= var6 var5)) (= var3 var8)) (= var0 var14)) (= var11 var9)) (= var13 (h (getnode (read var2 var5)))))))) (inv_main40 var10 var12 var7 var6 var3 var0 var11))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap) (var4 Int) (var5 Int) (var6 Addr) (var7 Addr) (var8 Int) (var9 Int) (var10 Addr) (var11 Int) (var12 Heap) (var13 Addr) (var14 Int)) (or (not (and (inv_main35 var3 var1 var6 var7 var8 var14 var9) (and (= var5 2) (and (and (and (and (and (and (and (= var12 var3) (= var10 var1)) (= var0 var6)) (= var13 var7)) (= var11 var8)) (= var2 var14)) (= var4 var9)) (= var5 (h (getnode (read var3 var7)))))))) (inv_main36 var12 var10 var0 var13 var11 1 var4))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Int) (var6 Addr) (var7 Int) (var8 Int) (var9 Int) (var10 Int) (var11 Addr) (var12 Int) (var13 Heap) (var14 Int)) (or (not (and (inv_main35 var1 var0 var2 var3 var7 var14 var8) (and (not (= var9 2)) (and (and (and (and (and (and (and (= var13 var1) (= var4 var0)) (= var11 var2)) (= var6 var3)) (= var5 var7)) (= var10 var14)) (= var12 var8)) (= var9 (h (getnode (read var1 var3)))))))) (inv_main36 var13 var4 var11 var6 var5 var10 var12))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Int)) (or (not (and (inv_main12 var1 var0 var2 var3 var4) (<= 0 (+ (+ 10 (* (- 1) var4)) (- 1))))) (inv_main14 var1 var0 var2 var3 var4))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Addr) (var4 Addr) (var5 Int)) (or (not (and (inv_main12 var1 var0 var3 var4 var5) (and (not (= var2 0)) (not (<= 0 (+ (+ 10 (* (- 1) var5)) (- 1))))))) (inv_main14 var1 var0 var3 var4 var5))))
(assert (forall ((var0 Addr) (var1 node) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Int) (var10 Heap) (var11 Heap) (var12 Int) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr)) (or (not (and (inv_main14 var5 var3 var7 var8 var12) (and (not (= var2 nullAddr)) (and (and (and (and (and (and (= var11 (newHeap (alloc var10 (O_node var1)))) (= var16 var6)) (= var15 var13)) (= var14 var0)) (= var4 var9)) (= var2 (newAddr (alloc var10 (O_node var1))))) (and (and (and (and (= var10 (write var5 var8 (O_node (node var12 (n (getnode (read var5 var8))))))) (= var6 var3)) (= var13 var7)) (= var0 var8)) (= var9 var12)))))) (inv_main20 var11 var16 var2 var14 var4))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Addr) (var4 Addr) (var5 Int)) (or (not (inv_main23 var1 var0 var3 var4 var5 var2)) (inv_main23 var1 var0 var3 var4 var5 var2))))
(assert (forall ((var0 Addr) (var1 node) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Int) (var10 Heap) (var11 Heap) (var12 Int) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr)) (or (not (and (inv_main14 var5 var3 var7 var8 var12) (and (= var2 nullAddr) (and (and (and (and (and (and (= var11 (newHeap (alloc var10 (O_node var1)))) (= var16 var6)) (= var15 var13)) (= var14 var0)) (= var4 var9)) (= var2 (newAddr (alloc var10 (O_node var1))))) (and (and (and (and (= var10 (write var5 var8 (O_node (node var12 (n (getnode (read var5 var8))))))) (= var6 var3)) (= var13 var7)) (= var0 var8)) (= var9 var12)))))) (inv_main23 var11 var16 var2 var14 var4 1))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Int)) (not (and (inv_main14 var1 var0 var2 var3 var4) (not (is-O_node (read var1 var3)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Int)) (not (and (inv_main20 var1 var0 var2 var3 var4) (not (is-O_node (read var1 var3)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Int)) (not (and (inv_main26 var1 var0 var2 var3 var4) (not (is-O_node (read var1 var3)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Int)) (not (and (inv_main13 var1 var0 var2 var3 var4) (not (is-O_node (read var1 var3)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Int)) (not (and (inv_main29 var1 var0 var2 var3 var4) (not (is-O_node (read var1 var3)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Int) (var5 Int) (var6 Int)) (not (and (inv_main35 var1 var0 var2 var3 var4 var6 var5) (not (is-O_node (read var1 var3)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Int) (var5 Int) (var6 Int)) (not (and (inv_main36 var1 var0 var2 var3 var4 var6 var5) (not (is-O_node (read var1 var3)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Int) (var5 Int) (var6 Int)) (not (and (inv_main40 var1 var0 var2 var3 var4 var6 var5) (not (is-O_node (read var1 var3)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Int) (var5 Int) (var6 Int)) (not (inv_main46 var1 var0 var2 var3 var4 var6 var5))))
(check-sat)