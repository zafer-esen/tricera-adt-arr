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
   (node (data Int) (next Addr) (prev Addr))
  )
))
(declare-fun inv_main12 (Heap Int Int Int Int Addr Addr) Bool)
(declare-fun inv_main15 (Heap Int Int Int Int Addr Addr Int) Bool)
(declare-fun inv_main18 (Heap Int Int Int Int Addr Addr) Bool)
(declare-fun inv_main19 (Heap Int Int Int Int Addr Addr) Bool)
(declare-fun inv_main22 (Heap Int Int Int Int Addr Addr) Bool)
(declare-fun inv_main28 (Heap Int Int Addr Int) Bool)
(declare-fun inv_main35 (Heap Int Int Addr Int Int Addr Int Int) Bool)
(declare-fun inv_main36 (Heap Int Int Addr Int Int Addr Int Int) Bool)
(declare-fun inv_main4 (Heap Int Int) Bool)
(declare-fun inv_main40 (Heap Int Int Addr Int) Bool)
(declare-fun inv_main49 (Heap Int Int Addr Int Int Addr Int) Bool)
(declare-fun inv_main50 (Heap Int Int Addr Int Int Addr Int) Bool)
(declare-fun inv_main57 (Heap Int Int Addr Int Addr) Bool)
(declare-fun inv_main60 (Heap Int Int Addr Int) Bool)
(declare-fun inv_main8 (Heap Int Int Int Int Addr) Bool)
(assert (forall ((var0 Heap)) (or (not (= var0 emptyHeap)) (inv_main4 var0 2 1))))
(assert (forall ((var0 Int) (var1 Heap) (var2 Int) (var3 Addr) (var4 Int)) (or (not (and (inv_main28 var1 var0 var4 var3 var2) (not (<= 0 var2)))) (inv_main40 var1 var0 var4 var3 (+ var0 (- 1))))))
(assert (forall ((var0 Int) (var1 Int) (var2 Heap) (var3 Heap) (var4 Int) (var5 Int) (var6 Addr) (var7 Int) (var8 Int) (var9 Addr) (var10 Int) (var11 Int) (var12 Addr) (var13 Int) (var14 Int)) (or (not (and (inv_main49 var3 var8 var13 var6 var11 var1 var12 var14) (and (= var10 var0) (and (and (and (and (and (and (= var2 var3) (= var5 var8)) (= var7 var13)) (= var9 var6)) (= var4 var11)) (= var10 var1)) (= var0 (data (getnode (read var3 var12)))))))) (inv_main40 var2 var5 var7 var9 (+ var4 (- 1))))))
(assert (forall ((var0 Int) (var1 Heap) (var2 Int) (var3 Addr) (var4 Addr) (var5 Int) (var6 Int)) (or (not (inv_main12 var1 var0 var5 var6 var2 var4 var3)) (inv_main18 (write var1 var3 (O_node (node var2 (next (getnode (read var1 var3))) (prev (getnode (read var1 var3)))))) var0 var5 var6 var2 var4 var3))))
(assert (forall ((var0 Int) (var1 node) (var2 Int) (var3 Heap) (var4 Int) (var5 Addr) (var6 Int) (var7 Int) (var8 Addr) (var9 Int) (var10 Int) (var11 Heap) (var12 Addr) (var13 Int)) (or (not (and (inv_main8 var3 var9 var13 var6 var4 var5) (and (and (not (= nullAddr var8)) (and (and (and (and (and (and (= var11 (newHeap (alloc var3 (O_node var1)))) (= var2 var9)) (= var7 var13)) (= var10 var6)) (= var0 var4)) (= var12 var5)) (= var8 (newAddr (alloc var3 (O_node var1)))))) (<= 0 (+ var6 (- 1)))))) (inv_main12 var11 var2 var7 var10 var0 var12 var8))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap) (var4 Addr) (var5 Int) (var6 Addr) (var7 Addr) (var8 Int) (var9 Int) (var10 Int) (var11 Addr) (var12 Addr) (var13 Int) (var14 Int) (var15 Int) (var16 Addr) (var17 Int) (var18 Heap) (var19 Heap)) (or (not (and (inv_main57 var3 var13 var17 var7 var15 var4) (and (not (= var12 nullAddr)) (and (and (and (and (and (and (and (= var18 var3) (= var10 var13)) (= var2 var17)) (= var16 var7)) (= var14 var15)) (= var11 var4)) (= var0 (next (getnode (read var3 var4))))) (and (and (and (and (and (and (= var19 (write var18 var11 defObj)) (= var9 var10)) (= var5 var2)) (= var1 var16)) (= var8 var14)) (= var6 var11)) (= var12 var0)))))) (inv_main57 var19 var9 var5 var1 var8 var12))))
(assert (forall ((var0 Int) (var1 Heap) (var2 Int) (var3 Addr) (var4 Int)) (or (not (and (inv_main40 var1 var0 var4 var3 var2) (and (not (= var3 nullAddr)) (not (<= 0 (* (- 1) var2)))))) (inv_main57 var1 var0 var4 var3 var2 var3))))
(assert (forall ((var0 Int) (var1 Heap) (var2 Int) (var3 Addr) (var4 Addr) (var5 Int) (var6 Int)) (or (not (inv_main18 var1 var0 var5 var6 var2 var4 var3)) (inv_main19 (write var1 var3 (O_node (node (data (getnode (read var1 var3))) var4 (prev (getnode (read var1 var3)))))) var0 var5 var6 var2 var4 var3))))
(assert (forall ((var0 Int) (var1 Heap) (var2 Int) (var3 Addr) (var4 Addr) (var5 Int) (var6 Int) (var7 Int)) (or (not (inv_main15 var1 var0 var5 var7 var2 var4 var3 var6)) (inv_main15 var1 var0 var5 var7 var2 var4 var3 var6))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Int) (var3 Heap) (var4 Int) (var5 Addr) (var6 Int) (var7 Int) (var8 Addr) (var9 Int) (var10 node) (var11 Int) (var12 Int) (var13 Int)) (or (not (and (inv_main8 var3 var11 var13 var7 var4 var5) (and (and (= nullAddr var8) (and (and (and (and (and (and (= var0 (newHeap (alloc var3 (O_node var10)))) (= var2 var11)) (= var9 var13)) (= var12 var7)) (= var6 var4)) (= var1 var5)) (= var8 (newAddr (alloc var3 (O_node var10)))))) (<= 0 (+ var7 (- 1)))))) (inv_main15 var0 var2 var9 var12 var6 var1 var8 1))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr) (var7 Int) (var8 Heap) (var9 Int) (var10 Int) (var11 Addr) (var12 Int) (var13 Int) (var14 Addr) (var15 Int) (var16 Int)) (or (not (and (inv_main50 var3 var9 var15 var6 var12 var1 var14 var16) (and (not (<= 0 (+ (+ var4 (- 1)) (- 1)))) (and (and (and (and (and (and (and (and (= var8 var3) (= var10 var9)) (= var0 var15)) (= var2 var6)) (= var13 var12)) (= var7 var1)) (= var11 var14)) (= var4 var16)) (= var5 (next (getnode (read var3 var14)))))))) (inv_main49 var8 var10 var0 var2 var13 var7 var5 (+ var4 (- 1))))))
(assert (forall ((var0 Int) (var1 Heap) (var2 Int) (var3 Addr) (var4 Int)) (or (not (and (inv_main40 var1 var0 var4 var3 var2) (and (not (<= 0 (+ var2 (- 1)))) (<= 0 (* (- 1) var2))))) (inv_main49 var1 var0 var4 var3 var2 (+ var2 var0) var3 var2))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Int) (var3 Addr) (var4 Int) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Int) (var10 Int) (var11 Int) (var12 Int) (var13 Int) (var14 Int) (var15 Int) (var16 Int) (var17 Addr) (var18 Int)) (or (not (and (inv_main36 var0 var14 var18 var3 var16 var13 var5 var1 var11) (and (not (<= 0 (+ (+ var2 (- 1)) (- 1)))) (and (and (and (and (and (and (and (and (and (= var7 var0) (= var10 var14)) (= var9 var18)) (= var17 var3)) (= var15 var16)) (= var12 var13)) (= var8 var5)) (= var4 var1)) (= var2 var11)) (= var6 (next (getnode (read var0 var5)))))))) (inv_main35 var7 var10 var9 var17 var15 var12 var6 var4 (+ var2 (- 1))))))
(assert (forall ((var0 Int) (var1 Heap) (var2 Int) (var3 Addr) (var4 Int)) (or (not (and (inv_main28 var1 var0 var4 var3 var2) (and (not (<= 0 (+ var2 (- 1)))) (<= 0 var2)))) (inv_main35 var1 var0 var4 var3 var2 (+ var2 var0) var3 (+ var2 var0) var2))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Addr) (var4 Addr) (var5 Int) (var6 Heap) (var7 Int) (var8 Addr) (var9 Int) (var10 Int) (var11 Int) (var12 Int) (var13 Int)) (or (not (and (inv_main19 var1 var11 var13 var7 var2 var4 var3) (and (not (= var8 nullAddr)) (and (and (and (and (and (and (= var6 (write var1 var3 (O_node (node (data (getnode (read var1 var3))) (next (getnode (read var1 var3))) nullAddr)))) (= var10 var11)) (= var5 var13)) (= var9 var7)) (= var12 var2)) (= var8 var4)) (= var0 var3))))) (inv_main22 var6 var10 var5 var9 var12 var8 var0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Heap) (var3 Int) (var4 Int) (var5 Addr) (var6 Addr) (var7 Int) (var8 Addr) (var9 Int) (var10 Int) (var11 Int) (var12 Int) (var13 Int)) (or (not (and (inv_main22 var2 var9 var13 var7 var3 var6 var5) (and (and (and (and (and (and (= var1 (write var2 var6 (O_node (node (data (getnode (read var2 var6))) (next (getnode (read var2 var6))) var5)))) (= var4 var9)) (= var12 var13)) (= var10 var7)) (= var11 var3)) (= var0 var6)) (= var8 var5)))) (inv_main8 var1 var4 var12 (+ var10 (- 1)) var11 var8))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Heap) (var3 Int) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Int) (var8 Int) (var9 Int) (var10 Int) (var11 Int) (var12 Int) (var13 Int)) (or (not (and (inv_main19 var2 var9 var12 var8 var3 var6 var5) (and (= var4 nullAddr) (and (and (and (and (and (and (= var0 (write var2 var5 (O_node (node (data (getnode (read var2 var5))) (next (getnode (read var2 var5))) nullAddr)))) (= var13 var9)) (= var10 var12)) (= var11 var8)) (= var7 var3)) (= var4 var6)) (= var1 var5))))) (inv_main8 var0 var13 var10 (+ var11 (- 1)) var7 var1))))
(assert (forall ((var0 Int) (var1 Heap) (var2 Int)) (or (not (inv_main4 var1 var0 var2)) (inv_main8 var1 var0 var2 var0 var2 nullAddr))))
(assert (forall ((var0 Int) (var1 Int) (var2 Heap) (var3 Int) (var4 Addr) (var5 Int) (var6 Addr) (var7 Int) (var8 Int) (var9 Int) (var10 Int) (var11 Addr) (var12 Int) (var13 Heap) (var14 Int)) (or (not (and (inv_main49 var2 var9 var12 var4 var10 var1 var11 var14) (and (not (= var7 var8)) (and (and (and (and (and (and (= var13 var2) (= var0 var9)) (= var3 var12)) (= var6 var4)) (= var5 var10)) (= var7 var1)) (= var8 (data (getnode (read var2 var11)))))))) (inv_main60 var13 var0 var3 var6 var5))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Addr) (var3 Int) (var4 Addr) (var5 Addr) (var6 Int) (var7 Int) (var8 Int) (var9 Int) (var10 Int) (var11 Int) (var12 Int) (var13 Int) (var14 Heap) (var15 Int) (var16 Int) (var17 Addr)) (or (not (and (inv_main35 var0 var8 var15 var2 var13 var7 var4 var1 var6) (and (and (and (and (and (and (and (and (= var14 (write var0 var4 (O_node (node var1 (next (getnode (read var0 var4))) (prev (getnode (read var0 var4))))))) (= var11 var8)) (= var9 var15)) (= var5 var2)) (= var16 var13)) (= var10 var7)) (= var17 var4)) (= var3 var1)) (= var12 var6)))) (inv_main28 var14 var11 var9 var5 (+ var16 (- 1))))))
(assert (forall ((var0 Int) (var1 Heap) (var2 Int) (var3 Addr) (var4 Int) (var5 Int)) (or (not (and (inv_main8 var1 var0 var4 var5 var2 var3) (not (<= 0 (+ var5 (- 1)))))) (inv_main28 var1 var0 var4 var3 (+ var0 (- 1))))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr) (var7 Int) (var8 Heap) (var9 Int) (var10 Int) (var11 Addr) (var12 Int) (var13 Int) (var14 Addr) (var15 Int) (var16 Int)) (or (not (and (inv_main50 var3 var9 var15 var6 var12 var1 var14 var16) (and (<= 0 (+ (+ var4 (- 1)) (- 1))) (and (and (and (and (and (and (and (and (= var8 var3) (= var10 var9)) (= var0 var15)) (= var2 var6)) (= var13 var12)) (= var7 var1)) (= var11 var14)) (= var4 var16)) (= var5 (next (getnode (read var3 var14)))))))) (inv_main50 var8 var10 var0 var2 var13 var7 var5 (+ var4 (- 1))))))
(assert (forall ((var0 Int) (var1 Heap) (var2 Int) (var3 Addr) (var4 Int)) (or (not (and (inv_main40 var1 var0 var4 var3 var2) (and (<= 0 (+ var2 (- 1))) (<= 0 (* (- 1) var2))))) (inv_main50 var1 var0 var4 var3 var2 (+ var2 var0) var3 var2))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Int) (var3 Addr) (var4 Int) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Int) (var10 Int) (var11 Int) (var12 Int) (var13 Int) (var14 Int) (var15 Int) (var16 Int) (var17 Addr) (var18 Int)) (or (not (and (inv_main36 var0 var14 var18 var3 var16 var13 var5 var1 var11) (and (<= 0 (+ (+ var2 (- 1)) (- 1))) (and (and (and (and (and (and (and (and (and (= var7 var0) (= var10 var14)) (= var9 var18)) (= var17 var3)) (= var15 var16)) (= var12 var13)) (= var8 var5)) (= var4 var1)) (= var2 var11)) (= var6 (next (getnode (read var0 var5)))))))) (inv_main36 var7 var10 var9 var17 var15 var12 var6 var4 (+ var2 (- 1))))))
(assert (forall ((var0 Int) (var1 Heap) (var2 Int) (var3 Addr) (var4 Int)) (or (not (and (inv_main28 var1 var0 var4 var3 var2) (and (<= 0 (+ var2 (- 1))) (<= 0 var2)))) (inv_main36 var1 var0 var4 var3 var2 (+ var2 var0) var3 (+ var2 var0) var2))))
(assert (forall ((var0 Int) (var1 Heap) (var2 Int) (var3 Addr) (var4 Addr) (var5 Int) (var6 Int)) (not (and (inv_main12 var1 var0 var5 var6 var2 var4 var3) (not (is-O_node (read var1 var3)))))))
(assert (forall ((var0 Int) (var1 Heap) (var2 Int) (var3 Addr) (var4 Addr) (var5 Int) (var6 Int)) (not (and (inv_main18 var1 var0 var5 var6 var2 var4 var3) (not (is-O_node (read var1 var3)))))))
(assert (forall ((var0 Int) (var1 Heap) (var2 Int) (var3 Addr) (var4 Addr) (var5 Int) (var6 Int)) (not (and (inv_main19 var1 var0 var5 var6 var2 var4 var3) (not (is-O_node (read var1 var3)))))))
(assert (forall ((var0 Int) (var1 Heap) (var2 Int) (var3 Addr) (var4 Addr) (var5 Int) (var6 Int)) (not (and (inv_main22 var1 var0 var5 var6 var2 var4 var3) (not (is-O_node (read var1 var4)))))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Heap) (var4 Int) (var5 Int) (var6 Addr) (var7 Int) (var8 Addr)) (not (and (inv_main36 var3 var2 var7 var6 var5 var1 var8 var4 var0) (not (is-O_node (read var3 var8)))))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Heap) (var4 Int) (var5 Int) (var6 Addr) (var7 Int) (var8 Addr)) (not (and (inv_main35 var3 var2 var7 var6 var5 var1 var8 var4 var0) (not (is-O_node (read var3 var8)))))))
(assert (forall ((var0 Int) (var1 Int) (var2 Heap) (var3 Int) (var4 Addr) (var5 Addr) (var6 Int) (var7 Int)) (not (and (inv_main50 var2 var1 var6 var5 var3 var0 var4 var7) (not (is-O_node (read var2 var4)))))))
(assert (forall ((var0 Int) (var1 Int) (var2 Heap) (var3 Int) (var4 Addr) (var5 Addr) (var6 Int) (var7 Int)) (not (and (inv_main49 var2 var1 var6 var5 var3 var0 var4 var7) (not (is-O_node (read var2 var4)))))))
(assert (forall ((var0 Int) (var1 Heap) (var2 Addr) (var3 Int) (var4 Addr) (var5 Int)) (not (and (inv_main57 var1 var0 var5 var4 var3 var2) (not (is-O_node (read var1 var2)))))))
(assert (forall ((var0 Int) (var1 Heap) (var2 Int) (var3 Addr) (var4 Int)) (not (inv_main60 var1 var0 var4 var3 var2))))
(check-sat)