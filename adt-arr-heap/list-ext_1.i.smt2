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
   (O_UInt (getUInt Int))
   (O_Addr (getAddr Addr))
   (O_node (getnode node))
   (defObj)
  )
  (
   (node (h Int) (n Addr))
  )
))
(declare-fun inv_main13 (Heap Int Int Addr Addr Addr) Bool)
(declare-fun inv_main14 (Heap Int Int Addr Addr Addr) Bool)
(declare-fun inv_main18 (Heap Int Int Addr Addr Addr) Bool)
(declare-fun inv_main22 (Heap Int Int Addr Addr Addr) Bool)
(declare-fun inv_main25 (Heap Int Int Addr Addr Addr Int) Bool)
(declare-fun inv_main28 (Heap Int Int Addr Addr Addr) Bool)
(declare-fun inv_main30 (Heap Int Int Addr Addr Addr) Bool)
(declare-fun inv_main34 (Heap Int Int Addr Addr Addr) Bool)
(declare-fun inv_main38 (Heap Int Int Addr Addr Addr) Bool)
(declare-fun inv_main4 (Heap Int Int) Bool)
(declare-fun inv_main41 (Heap Int Int Addr Addr Addr Int) Bool)
(declare-fun inv_main44 (Heap Int Int Addr Addr Addr) Bool)
(declare-fun inv_main46 (Heap Int Int Addr Addr Addr) Bool)
(declare-fun inv_main50 (Heap Int Int Addr Addr Addr) Bool)
(declare-fun inv_main51 (Heap Int Int Addr Addr Addr) Bool)
(declare-fun inv_main54 (Heap Int Int Addr Addr Addr) Bool)
(declare-fun inv_main56 (Heap Int Int Addr Addr Addr) Bool)
(declare-fun inv_main59 (Heap Int Int Addr Addr Addr) Bool)
(declare-fun inv_main62 (Heap Int Int Addr Addr Addr) Bool)
(declare-fun inv_main66 (Heap Int Int Addr Addr Addr) Bool)
(declare-fun inv_main68 (Heap Int Int Addr Addr Addr) Bool)
(declare-fun inv_main9 (Heap Int Int Addr Int) Bool)
(assert (forall ((var0 Heap)) (or (not (= var0 emptyHeap)) (inv_main4 var0 0 0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Heap)) (or (not (and (inv_main14 var5 var4 var3 var2 var1 var0) (not (<= 0 (+ (+ 10 (* (- 1) var3)) (- 1)))))) (inv_main30 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Int) (var6 Heap)) (or (not (and (inv_main14 var6 var5 var4 var3 var2 var1) (and (= var0 0) (<= 0 (+ (+ 10 (* (- 1) var4)) (- 1)))))) (inv_main30 var6 var5 var4 var3 var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Heap)) (or (not (and (inv_main38 var5 var4 var3 var2 var1 var0) (is-O_node (read var5 var0)))) (inv_main44 (write var5 var0 (O_node (node (h (getnode (read var5 var0))) var1))) var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Int) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Int) (var11 Int) (var12 Heap)) (or (not (and (inv_main54 var12 var11 var10 var9 var8 var7) (and (is-O_node (read var12 var7)) (and (and (and (and (and (and (= var6 var12) (= var5 var11)) (= var4 var10)) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var0 (n (getnode (read var12 var7)))))))) (inv_main50 var6 var5 var4 var3 var2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Int) (var10 Int) (var11 Heap)) (or (not (and (inv_main46 var11 var10 var9 var8 var7 var6) (and (is-O_node (read var11 var6)) (and (and (and (and (and (= var5 (write var11 var6 (O_node (node (h (getnode (read var11 var6))) 0)))) (= var4 var10)) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var0 var6))))) (inv_main50 var5 0 0 var2 var1 var2))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Int) (var6 Heap)) (or (not (inv_main41 var6 var5 var4 var3 var2 var1 var0)) (inv_main41 var6 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Int) (var7 Int) (var8 Int) (var9 Int) (var10 node) (var11 Heap) (var12 Heap) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Int) (var18 Int) (var19 Heap)) (or (not (and (inv_main34 var19 var18 var17 var16 var15 var14) (and (= var13 nullAddr) (and (and (and (and (and (and (and (and (= var12 (newHeap (alloc var11 (O_node var10)))) (= var9 var8)) (= var7 var6)) (= var5 var4)) (= var3 var2)) (= var1 var0)) (= var13 (newAddr (alloc var11 (O_node var10))))) (is-O_node (read var19 var14))) (and (and (and (and (and (= var11 (write var19 var14 (O_node (node 2 (n (getnode (read var19 var14))))))) (= var8 var18)) (= var6 var17)) (= var4 var16)) (= var2 var15)) (= var0 var14)))))) (inv_main41 var12 var9 var7 var5 var13 var1 1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Int) (var6 Int) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Int) (var11 Int) (var12 Heap)) (or (not (and (inv_main56 var12 var11 var10 var9 var8 var7) (and (and (or (not (= var6 3)) (<= 0 (+ (+ (+ var5 var4) (- 20)) (- 1)))) (is-O_node (read var12 var7))) (and (and (and (and (and (and (= var3 var12) (= var5 var11)) (= var4 var10)) (= var2 var9)) (= var1 var8)) (= var0 var7)) (= var6 (h (getnode (read var12 var7)))))))) (inv_main62 var3 var5 var4 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Heap)) (or (not (inv_main9 var4 var3 var2 var1 var0)) (inv_main9 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 node) (var3 Heap) (var4 Addr) (var5 Int) (var6 Int) (var7 Heap)) (or (not (and (inv_main4 var7 var6 var5) (and (= var4 nullAddr) (and (and (and (= var3 (newHeap (alloc var7 (O_node var2)))) (= var1 var6)) (= var0 var5)) (= var4 (newAddr (alloc var7 (O_node var2)))))))) (inv_main9 var3 var1 var0 var4 1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Heap)) (or (not (and (inv_main30 var5 var4 var3 var2 var1 var0) (is-O_node (read var5 var0)))) (inv_main46 (write var5 var0 (O_node (node 3 (n (getnode (read var5 var0)))))) var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Int) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Int) (var11 Int) (var12 Heap)) (or (not (and (inv_main44 var12 var11 var10 var9 var8 var7) (and (is-O_node (read var12 var7)) (and (and (and (and (and (and (= var6 var12) (= var5 var11)) (= var4 var10)) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var0 (n (getnode (read var12 var7)))))))) (inv_main14 var6 var5 var4 var3 var2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Heap)) (or (not (and (inv_main13 var5 var4 var3 var2 var1 var0) (not (<= 0 (+ (+ 10 (* (- 1) var4)) (- 1)))))) (inv_main14 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Int) (var6 Heap)) (or (not (and (inv_main13 var6 var5 var4 var3 var2 var1) (and (= var0 0) (<= 0 (+ (+ 10 (* (- 1) var5)) (- 1)))))) (inv_main14 var6 var5 var4 var3 var2 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Int) (var6 Heap)) (or (not (and (inv_main13 var6 var5 var4 var3 var2 var1) (and (not (= var0 0)) (<= 0 (+ (+ 10 (* (- 1) var5)) (- 1)))))) (inv_main18 var6 (+ var5 1) var4 var3 var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Int) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Int) (var11 Int) (var12 Heap)) (or (not (and (inv_main28 var12 var11 var10 var9 var8 var7) (and (is-O_node (read var12 var7)) (and (and (and (and (and (and (= var6 var12) (= var5 var11)) (= var4 var10)) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var0 (n (getnode (read var12 var7)))))))) (inv_main13 var6 var5 var4 var3 var2 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 node) (var4 Heap) (var5 Addr) (var6 Int) (var7 Int) (var8 Heap)) (or (not (and (inv_main4 var8 var7 var6) (and (not (= var5 nullAddr)) (and (and (and (= var4 (newHeap (alloc var8 (O_node var3)))) (= var2 var7)) (= var1 var6)) (= var5 (newAddr (alloc var8 (O_node var3)))))))) (inv_main13 var4 var2 var1 var5 var0 var5))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Heap)) (or (not (and (inv_main22 var5 var4 var3 var2 var1 var0) (is-O_node (read var5 var0)))) (inv_main28 (write var5 var0 (O_node (node (h (getnode (read var5 var0))) var1))) var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Int) (var6 Heap)) (or (not (and (inv_main14 var6 var5 var4 var3 var2 var1) (and (not (= var0 0)) (<= 0 (+ (+ 10 (* (- 1) var4)) (- 1)))))) (inv_main34 var6 var5 (+ var4 1) var3 var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Int) (var7 Int) (var8 Int) (var9 Int) (var10 node) (var11 Heap) (var12 Heap) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Int) (var18 Int) (var19 Heap)) (or (not (and (inv_main34 var19 var18 var17 var16 var15 var14) (and (not (= var13 nullAddr)) (and (and (and (and (and (and (and (and (= var12 (newHeap (alloc var11 (O_node var10)))) (= var9 var8)) (= var7 var6)) (= var5 var4)) (= var3 var2)) (= var1 var0)) (= var13 (newAddr (alloc var11 (O_node var10))))) (is-O_node (read var19 var14))) (and (and (and (and (and (= var11 (write var19 var14 (O_node (node 2 (n (getnode (read var19 var14))))))) (= var8 var18)) (= var6 var17)) (= var4 var16)) (= var2 var15)) (= var0 var14)))))) (inv_main38 var12 var9 var7 var5 var13 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Heap) (var6 Int) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Int) (var11 Int) (var12 Heap)) (or (not (and (inv_main51 var12 var11 var10 var9 var8 var7) (and (and (= var6 2) (is-O_node (read var12 var7))) (and (and (and (and (and (and (= var5 var12) (= var4 var11)) (= var3 var10)) (= var2 var9)) (= var1 var8)) (= var0 var7)) (= var6 (h (getnode (read var12 var7)))))))) (inv_main59 var5 var4 (+ var3 1) var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Heap) (var6 Int) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Int) (var11 Int) (var12 Heap)) (or (not (and (inv_main51 var12 var11 var10 var9 var8 var7) (and (and (not (= var6 2)) (is-O_node (read var12 var7))) (and (and (and (and (and (and (= var5 var12) (= var4 var11)) (= var3 var10)) (= var2 var9)) (= var1 var8)) (= var0 var7)) (= var6 (h (getnode (read var12 var7)))))))) (inv_main56 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Int) (var6 Int) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Int) (var11 Int) (var12 Heap)) (or (not (and (inv_main56 var12 var11 var10 var9 var8 var7) (and (and (and (= var6 3) (not (<= 0 (+ (+ (+ var5 var4) (- 20)) (- 1))))) (is-O_node (read var12 var7))) (and (and (and (and (and (and (= var3 var12) (= var5 var11)) (= var4 var10)) (= var2 var9)) (= var1 var8)) (= var0 var7)) (= var6 (h (getnode (read var12 var7)))))))) (inv_main66 var3 var5 var4 var2 var1 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Int) (var11 Int) (var12 Heap) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Int) (var17 Int) (var18 Heap)) (or (not (and (inv_main68 var18 var17 var16 var15 var14 var13) (and (and (is-O_node (read var18 var13)) (and (and (and (and (and (and (= var12 var18) (= var11 var17)) (= var10 var16)) (= var9 var15)) (= var8 var14)) (= var7 var13)) (= var6 (n (getnode (read var18 var13)))))) (and (and (and (and (and (= var5 (write var12 var7 defObj)) (= var4 var11)) (= var3 var10)) (= var2 var9)) (= var1 var6)) (= var0 var7))))) (inv_main66 var5 var4 var3 var2 var1 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Int) (var11 Int) (var12 Heap)) (or (not (and (inv_main66 var12 var11 var10 var9 var8 var7) (and (and (not (= var6 nullAddr)) (is-O_node (read var12 var7))) (and (and (and (and (and (and (= var5 var12) (= var4 var11)) (= var3 var10)) (= var2 var9)) (= var1 var8)) (= var0 var7)) (= var6 (n (getnode (read var12 var7)))))))) (inv_main68 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Int) (var7 Int) (var8 Int) (var9 Int) (var10 node) (var11 Heap) (var12 Heap) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Int) (var18 Int) (var19 Heap)) (or (not (and (inv_main18 var19 var18 var17 var16 var15 var14) (and (not (= var13 nullAddr)) (and (and (and (and (and (and (and (and (= var12 (newHeap (alloc var11 (O_node var10)))) (= var9 var8)) (= var7 var6)) (= var5 var4)) (= var3 var2)) (= var1 var0)) (= var13 (newAddr (alloc var11 (O_node var10))))) (is-O_node (read var19 var14))) (and (and (and (and (and (= var11 (write var19 var14 (O_node (node 1 (n (getnode (read var19 var14))))))) (= var8 var18)) (= var6 var17)) (= var4 var16)) (= var2 var15)) (= var0 var14)))))) (inv_main22 var12 var9 var7 var5 var13 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Heap) (var6 Int) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Int) (var11 Int) (var12 Heap)) (or (not (and (inv_main50 var12 var11 var10 var9 var8 var7) (and (and (not (= var6 1)) (is-O_node (read var12 var7))) (and (and (and (and (and (and (= var5 var12) (= var4 var11)) (= var3 var10)) (= var2 var9)) (= var1 var8)) (= var0 var7)) (= var6 (h (getnode (read var12 var7)))))))) (inv_main51 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Int) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Int) (var11 Int) (var12 Heap)) (or (not (and (inv_main59 var12 var11 var10 var9 var8 var7) (and (is-O_node (read var12 var7)) (and (and (and (and (and (and (= var6 var12) (= var5 var11)) (= var4 var10)) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var0 (n (getnode (read var12 var7)))))))) (inv_main51 var6 var5 var4 var3 var2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Heap) (var6 Int) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Int) (var11 Int) (var12 Heap)) (or (not (and (inv_main50 var12 var11 var10 var9 var8 var7) (and (and (= var6 1) (is-O_node (read var12 var7))) (and (and (and (and (and (and (= var5 var12) (= var4 var11)) (= var3 var10)) (= var2 var9)) (= var1 var8)) (= var0 var7)) (= var6 (h (getnode (read var12 var7)))))))) (inv_main54 var5 (+ var4 1) var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Int) (var6 Heap)) (or (not (inv_main25 var6 var5 var4 var3 var2 var1 var0)) (inv_main25 var6 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Int) (var7 Int) (var8 Int) (var9 Int) (var10 node) (var11 Heap) (var12 Heap) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Int) (var18 Int) (var19 Heap)) (or (not (and (inv_main18 var19 var18 var17 var16 var15 var14) (and (= var13 nullAddr) (and (and (and (and (and (and (and (and (= var12 (newHeap (alloc var11 (O_node var10)))) (= var9 var8)) (= var7 var6)) (= var5 var4)) (= var3 var2)) (= var1 var0)) (= var13 (newAddr (alloc var11 (O_node var10))))) (is-O_node (read var19 var14))) (and (and (and (and (and (= var11 (write var19 var14 (O_node (node 1 (n (getnode (read var19 var14))))))) (= var8 var18)) (= var6 var17)) (= var4 var16)) (= var2 var15)) (= var0 var14)))))) (inv_main25 var12 var9 var7 var5 var13 var1 1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Heap)) (not (and (inv_main18 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var5 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Heap)) (not (and (inv_main22 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var5 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Heap)) (not (and (inv_main28 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var5 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Heap)) (not (and (inv_main34 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var5 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Heap)) (not (and (inv_main38 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var5 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Heap)) (not (and (inv_main44 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var5 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Heap)) (not (and (inv_main30 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var5 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Heap)) (not (and (inv_main46 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var5 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Heap)) (not (and (inv_main50 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var5 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Heap)) (not (and (inv_main54 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var5 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Heap)) (not (and (inv_main51 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var5 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Heap)) (not (and (inv_main59 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var5 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Heap)) (not (and (inv_main56 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var5 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Heap)) (not (inv_main62 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Heap)) (not (and (inv_main66 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var5 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Heap)) (not (and (inv_main68 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var5 var0)))))))
(check-sat)
