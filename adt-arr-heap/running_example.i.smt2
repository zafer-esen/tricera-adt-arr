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
   (node (val Int) (next Addr))
  )
))
(declare-fun inv_main15 (Heap Addr Addr Addr Int) Bool)
(declare-fun inv_main17 (Heap Addr Addr Addr Int) Bool)
(declare-fun inv_main18 (Heap Addr Addr Addr Int) Bool)
(declare-fun inv_main2 (Heap) Bool)
(declare-fun inv_main21 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main22 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main23 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main24 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main25 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main27 (Heap Addr Addr Addr Int) Bool)
(declare-fun inv_main30 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main31 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main4 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main5 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main6 (Heap Addr Addr Addr) Bool)
(assert (inv_main2 emptyHeap))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main5 var3 var2 var1 var0) (is-O_node (read var3 var1)))) (inv_main6 (write var3 var1 (O_node (node 10 (next (getnode (read var3 var1)))))) var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Int) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main18 var9 var8 var7 var6 var5) (and (is-O_node (read var9 var8)) (and (and (and (and (= var4 (write var9 var8 (O_node (node var5 (next (getnode (read var9 var8))))))) (= var3 var8)) (= var2 var7)) (= var1 var6)) (= var0 var5))))) (inv_main6 var4 var3 var2 var3))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main6 var5 var4 var3 var2) (and (or (<= 0 (+ (+ 10 (* (- 1) var1)) (- 1))) (<= 0 (+ (+ var1 (- 20)) (- 1)))) (not (= var0 0))))) (inv_main6 var5 var4 var3 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main4 var3 var2 var1 var0) (is-O_node (read var3 var1)))) (inv_main5 (write var3 var1 (O_node (node (val (getnode (read var3 var1))) nullAddr))) var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main23 var8 var7 var6 var5) (and (is-O_node (read var8 var7)) (and (and (and (and (= var4 var8) (= var3 var7)) (= var2 var6)) (= var1 var5)) (= var0 (next (getnode (read var8 var7)))))))) (inv_main21 var4 var0 var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main21 var3 var2 var1 var0) (= var2 nullAddr))) (inv_main21 var3 var1 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main6 var4 var3 var2 var1) (= var0 0))) (inv_main21 var4 var2 var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main22 var3 var2 var1 var0) (is-O_node (read var3 var2)))) (inv_main27 var3 var2 var1 var0 (val (getnode (read var3 var2)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main24 var8 var7 var6 var5) (and (and (not (<= 0 (+ (+ 20 (* (- 1) var4)) (- 1)))) (is-O_node (read var8 var7))) (and (and (and (and (= var3 var8) (= var2 var7)) (= var1 var6)) (= var0 var5)) (= var4 (val (getnode (read var8 var7)))))))) (inv_main31 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (inv_main25 var3 var2 var1 var0)) (inv_main24 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap) (var9 Int) (var10 Int) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Heap)) (or (not (and (inv_main27 var14 var13 var12 var11 var10) (and (and (not (= var9 0)) (and (and (<= 0 (+ 20 (* (- 1) var10))) (is-O_node (read var14 var13))) (and (and (and (and (= var8 var14) (= var7 var13)) (= var6 var12)) (= var5 var11)) (= var4 (val (getnode (read var14 var13))))))) (and (and (and (and (= var3 var8) (= var2 var7)) (= var1 var6)) (= var0 var5)) (or (and (<= 0 (+ var4 (- 10))) (= var9 1)) (and (not (<= 0 (+ var4 (- 10)))) (= var9 0))))))) (inv_main24 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Addr) (var5 Addr) (var6 Addr) (var7 node) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Heap)) (or (not (and (inv_main6 var12 var11 var10 var9) (and (and (and (and (and (and (and (= var8 (newHeap (alloc var12 (O_node var7)))) (= var6 var11)) (= var5 var10)) (= var4 var9)) (= var3 var2)) (= var1 (newAddr (alloc var12 (O_node var7))))) (and (not (<= 0 (+ (+ 10 (* (- 1) var2)) (- 1)))) (not (<= 0 (+ (+ var2 (- 20)) (- 1)))))) (not (= var0 0))))) (inv_main15 var8 var1 var5 var4 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main21 var3 var2 var1 var0) (not (= var2 nullAddr)))) (inv_main22 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main30 var8 var7 var6 var5) (and (is-O_node (read var8 var7)) (and (and (and (and (= var4 var8) (= var3 var7)) (= var2 var6)) (= var1 var5)) (= var0 (val (getnode (read var8 var7)))))))) (inv_main23 (write var4 var3 (O_node (node (+ var0 1) (next (getnode (read var4 var3)))))) var3 var2 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap) (var9 Int)) (or (not (and (inv_main31 var8 var7 var6 var5) (and (is-O_node (read var8 var7)) (and (and (and (and (= var4 var8) (= var3 var7)) (= var2 var6)) (= var1 var5)) (= var0 (val (getnode (read var8 var7)))))))) (or (not (and (and (and (<= 0 (+ (+ 2 (* (- 1) (+ var0 (* (- 2) var9)))) (- 1))) (<= 0 (+ (+ 2 (* 1 (+ var0 (* (- 2) var9)))) (- 1)))) (or (not (<= 0 (+ (+ var0 (* (- 2) var9)) (- 1)))) (<= 0 (+ var0 (- 1))))) (or (not (<= 0 (+ (* (- 1) (+ var0 (* (- 2) var9))) (- 1)))) (<= 0 (+ (* (- 1) var0) (- 1)))))) (inv_main23 (write var4 var3 (O_node (node var9 (next (getnode (read var4 var3)))))) var3 var2 var1)))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main17 var4 var3 var2 var1 var0) (is-O_node (read var4 var3)))) (inv_main18 (write var4 var3 (O_node (node (val (getnode (read var4 var3))) nullAddr))) var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main15 var4 var3 var2 var1 var0) (is-O_node (read var4 var1)))) (inv_main17 (write var4 var1 (O_node (node (val (getnode (read var4 var1))) var3))) var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 node) (var4 Heap) (var5 Heap)) (or (not (and (inv_main2 var5) (and (and (= var4 (newHeap (alloc var5 (O_node var3)))) (= var2 var1)) (= var0 (newAddr (alloc var5 (O_node var3))))))) (inv_main4 var4 var2 var0 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main24 var8 var7 var6 var5) (and (and (<= 0 (+ (+ 20 (* (- 1) var4)) (- 1))) (is-O_node (read var8 var7))) (and (and (and (and (= var3 var8) (= var2 var7)) (= var1 var6)) (= var0 var5)) (= var4 (val (getnode (read var8 var7)))))))) (inv_main30 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main27 var4 var3 var2 var1 var0) (not (<= 0 (+ 20 (* (- 1) var0)))))) (inv_main25 var4 var3 var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap) (var9 Int) (var10 Int) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Heap)) (or (not (and (inv_main27 var14 var13 var12 var11 var10) (and (and (= var9 0) (and (and (<= 0 (+ 20 (* (- 1) var10))) (is-O_node (read var14 var13))) (and (and (and (and (= var8 var14) (= var7 var13)) (= var6 var12)) (= var5 var11)) (= var4 (val (getnode (read var14 var13))))))) (and (and (and (and (= var3 var8) (= var2 var7)) (= var1 var6)) (= var0 var5)) (or (and (<= 0 (+ var4 (- 10))) (= var9 1)) (and (not (<= 0 (+ var4 (- 10)))) (= var9 0))))))) (inv_main25 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main4 var3 var2 var1 var0) (not (is-O_node (read var3 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main5 var3 var2 var1 var0) (not (is-O_node (read var3 var1)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main15 var4 var3 var2 var1 var0) (not (is-O_node (read var4 var1)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main17 var4 var3 var2 var1 var0) (not (is-O_node (read var4 var3)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main18 var4 var3 var2 var1 var0) (not (is-O_node (read var4 var3)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main22 var3 var2 var1 var0) (not (is-O_node (read var3 var2)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main27 var4 var3 var2 var1 var0) (and (<= 0 (+ 20 (* (- 1) var0))) (not (is-O_node (read var4 var3))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (inv_main25 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main24 var3 var2 var1 var0) (not (is-O_node (read var3 var2)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main30 var3 var2 var1 var0) (not (is-O_node (read var3 var2)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main31 var3 var2 var1 var0) (not (is-O_node (read var3 var2)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main23 var3 var2 var1 var0) (not (is-O_node (read var3 var2)))))))
(check-sat)
