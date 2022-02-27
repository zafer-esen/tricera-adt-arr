(set-logic HORN)
(set-info :source |
    Benchmark: C_VC
    Output by Princess (http://www.philipp.ruemmer.org/princess.shtml)
|)
(set-info :status unsat)
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
   (node (next Addr))
  )
))
(declare-fun inv_main11 (Heap Int Int Addr) Bool)
(declare-fun inv_main15 (Heap Int Int Addr Addr) Bool)
(declare-fun inv_main18 (Heap Int Int Addr Addr Int) Bool)
(declare-fun inv_main3 (Heap Int) Bool)
(declare-fun inv_main33 (Heap Int Addr Addr Int) Bool)
(declare-fun inv_main39 (Heap Int Addr Addr) Bool)
(declare-fun inv_main42 (Heap Int Addr) Bool)
(assert (forall ((var0 Heap)) (or (not (= var0 emptyHeap)) (inv_main3 var0 2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Int) (var5 Int) (var6 Addr) (var7 Heap) (var8 Int) (var9 Int)) (or (not (and (inv_main15 var2 var8 var9 var6 var3) (and (and (and (and (= var7 (write var2 var3 (O_node (node var6)))) (= var4 var8)) (= var5 var9)) (= var1 var6)) (= var0 var3)))) (inv_main11 var7 var4 (+ var5 (- 1)) var0))))
(assert (forall ((var0 Heap) (var1 Int)) (or (not (and (inv_main3 var0 var1) (not (<= 0 (+ (+ 32 (* (- 1) var1)) (- 1)))))) (inv_main11 var0 var1 (+ var1 1) nullAddr))))
(assert (forall ((var0 Int) (var1 Heap) (var2 Int)) (or (not (and (inv_main3 var1 var2) (and (= var0 0) (<= 0 (+ (+ 32 (* (- 1) var2)) (- 1)))))) (inv_main11 var1 var2 (+ var2 1) nullAddr))))
(assert (forall ((var0 Int) (var1 Heap) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Int) (var6 Int) (var7 Addr) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr)) (or (not (and (inv_main39 var1 var6 var3 var9) (and (not (= var13 nullAddr)) (and (and (and (and (and (= var8 var1) (= var5 var6)) (= var12 var3)) (= var4 var9)) (= var11 (next (getnode (read var1 var9))))) (and (and (and (and (= var2 (write var8 var4 defObj)) (= var0 var5)) (= var10 var12)) (= var7 var4)) (= var13 var11)))))) (inv_main39 var2 var0 var10 var13))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Heap) (var5 Heap) (var6 Addr) (var7 Int) (var8 Addr) (var9 Int) (var10 Int)) (or (not (and (inv_main33 var4 var10 var6 var8 var9) (and (not (= var1 nullAddr)) (and (= var2 var7) (and (= var3 nullAddr) (and (and (and (and (and (= var5 var4) (= var2 var10)) (= var1 var6)) (= var0 var8)) (= var7 var9)) (= var3 (next (getnode (read var4 var8)))))))))) (inv_main39 var5 var2 var1 var1))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Int) (var3 Int)) (or (not (and (inv_main11 var0 var2 var3 var1) (and (not (= var1 nullAddr)) (and (and (= var2 0) (= var1 nullAddr)) (not (<= 0 (+ var3 (- 1)))))))) (inv_main39 var0 var2 var1 var1))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Int)) (or (not (and (inv_main3 var0 var2) (and (not (= var1 0)) (<= 0 (+ (+ 32 (* (- 1) var2)) (- 1)))))) (inv_main3 var0 (+ var2 1)))))
(assert (forall ((var0 Int) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Int) (var5 Int)) (or (not (inv_main18 var1 var4 var5 var3 var2 var0)) (inv_main18 var1 var4 var5 var3 var2 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Heap) (var4 Heap) (var5 node) (var6 Addr) (var7 Int) (var8 Int) (var9 Addr)) (or (not (and (inv_main11 var3 var7 var8 var6) (and (and (= nullAddr var2) (and (and (and (and (= var4 (newHeap (alloc var3 (O_node var5)))) (= var0 var7)) (= var1 var8)) (= var9 var6)) (= var2 (newAddr (alloc var3 (O_node var5)))))) (<= 0 (+ var8 (- 1)))))) (inv_main18 var4 var0 var1 var9 var2 1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Heap) (var5 Heap) (var6 Addr) (var7 Int) (var8 Addr) (var9 Int) (var10 Int)) (or (not (and (inv_main33 var4 var10 var6 var8 var9) (and (not (= var3 nullAddr)) (and (and (and (and (and (= var5 var4) (= var2 var10)) (= var1 var6)) (= var0 var8)) (= var7 var9)) (= var3 (next (getnode (read var4 var8)))))))) (inv_main33 var5 var2 var1 var3 (+ var7 1)))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Int) (var3 Int)) (or (not (and (inv_main11 var0 var2 var3 var1) (and (not (= var1 nullAddr)) (not (<= 0 (+ var3 (- 1))))))) (inv_main33 var0 var2 var1 var1 1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Heap) (var4 Int) (var5 Addr) (var6 node) (var7 Int) (var8 Int) (var9 Int)) (or (not (and (inv_main11 var3 var7 var8 var5) (and (and (not (= nullAddr var0)) (and (and (and (and (= var2 (newHeap (alloc var3 (O_node var6)))) (= var9 var7)) (= var4 var8)) (= var1 var5)) (= var0 (newAddr (alloc var3 (O_node var6)))))) (<= 0 (+ var8 (- 1)))))) (inv_main15 var2 var9 var4 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Heap) (var5 Heap) (var6 Addr) (var7 Int) (var8 Addr) (var9 Int) (var10 Int)) (or (not (and (inv_main33 var4 var10 var6 var8 var9) (and (not (= var2 var7)) (and (= var3 nullAddr) (and (and (and (and (and (= var5 var4) (= var2 var10)) (= var1 var6)) (= var0 var8)) (= var7 var9)) (= var3 (next (getnode (read var4 var8))))))))) (inv_main42 var5 var2 var1))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Int) (var3 Int)) (or (not (and (inv_main11 var0 var2 var3 var1) (and (and (not (= var2 0)) (= var1 nullAddr)) (not (<= 0 (+ var3 (- 1))))))) (inv_main42 var0 var2 var1))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int)) (not (and (inv_main15 var0 var3 var4 var2 var1) (not (is-O_node (read var0 var1)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int)) (not (and (inv_main33 var0 var4 var1 var2 var3) (not (is-O_node (read var0 var2)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Int)) (not (and (inv_main39 var0 var3 var2 var1) (not (is-O_node (read var0 var1)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Int)) (not (inv_main42 var0 var2 var1))))
(check-sat)
