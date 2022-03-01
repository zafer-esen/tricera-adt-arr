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
   (O_UInt (getUInt Int))
   (O_Addr (getAddr Addr))
   (O_node (getnode node))
   (defObj)
  )
  (
   (node (h Int) (n Addr))
  )
))
(declare-fun inv_main11 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main13 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main14 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main19 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main2 (Heap) Bool)
(declare-fun inv_main22 (Heap Addr Addr Addr Int) Bool)
(declare-fun inv_main25 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main27 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main31 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main32 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main33 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main7 (Heap Addr Int) Bool)
(assert (inv_main2 emptyHeap))
(assert (forall ((var0 Addr) (var1 node) (var2 Heap) (var3 Addr) (var4 Heap)) (or (not (and (inv_main2 var4) (and (not (= var3 nullAddr)) (and (= var2 (newHeap (alloc var4 (O_node var1)))) (= var3 (newAddr (alloc var4 (O_node var1)))))))) (inv_main11 var2 var3 var0 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main13 var3 var2 var1 var0) (is-O_node (read var3 var0)))) (inv_main27 (write var3 var0 (O_node (node 2 (n (getnode (read var3 var0)))))) var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 node) (var7 Heap) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Heap)) (or (not (and (inv_main14 var13 var12 var11 var10) (and (not (= var9 nullAddr)) (and (and (and (and (and (and (= var8 (newHeap (alloc var7 (O_node var6)))) (= var5 var4)) (= var3 var2)) (= var1 var0)) (= var9 (newAddr (alloc var7 (O_node var6))))) (is-O_node (read var13 var10))) (and (and (and (= var7 (write var13 var10 (O_node (node 1 (n (getnode (read var13 var10))))))) (= var4 var12)) (= var2 var11)) (= var0 var10)))))) (inv_main19 var8 var5 var9 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main31 var8 var7 var6 var5) (and (and (not (= var4 2)) (is-O_node (read var8 var5))) (and (and (and (and (= var3 var8) (= var2 var7)) (= var1 var6)) (= var0 var5)) (= var4 (h (getnode (read var8 var5)))))))) (inv_main33 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main19 var3 var2 var1 var0) (is-O_node (read var3 var0)))) (inv_main25 (write var3 var0 (O_node (node (h (getnode (read var3 var0))) var1))) var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main11 var8 var7 var6 var5) (and (and (= var4 0) (is-O_node (read var8 var7))) (and (and (and (= var3 (write var8 var7 (O_node (node 2 (n (getnode (read var8 var7))))))) (= var2 var7)) (= var1 var6)) (= var0 var5))))) (inv_main13 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Int) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main25 var9 var8 var7 var6) (and (= var5 0) (and (is-O_node (read var9 var6)) (and (and (and (and (= var4 var9) (= var3 var8)) (= var2 var7)) (= var1 var6)) (= var0 (n (getnode (read var9 var6))))))))) (inv_main13 var4 var3 var2 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap)) (or (not (inv_main7 var2 var1 var0)) (inv_main7 var2 var1 var0))))
(assert (forall ((var0 node) (var1 Heap) (var2 Addr) (var3 Heap)) (or (not (and (inv_main2 var3) (and (= var2 nullAddr) (and (= var1 (newHeap (alloc var3 (O_node var0)))) (= var2 (newAddr (alloc var3 (O_node var0)))))))) (inv_main7 var1 var2 1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main11 var8 var7 var6 var5) (and (and (not (= var4 0)) (is-O_node (read var8 var7))) (and (and (and (= var3 (write var8 var7 (O_node (node 2 (n (getnode (read var8 var7))))))) (= var2 var7)) (= var1 var6)) (= var0 var5))))) (inv_main14 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Int) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main25 var9 var8 var7 var6) (and (not (= var5 0)) (and (is-O_node (read var9 var6)) (and (and (and (and (= var4 var9) (= var3 var8)) (= var2 var7)) (= var1 var6)) (= var0 (n (getnode (read var9 var6))))))))) (inv_main14 var4 var3 var2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main31 var8 var7 var6 var5) (and (and (= var4 2) (is-O_node (read var8 var5))) (and (and (and (and (= var3 var8) (= var2 var7)) (= var1 var6)) (= var0 var5)) (= var4 (h (getnode (read var8 var5)))))))) (inv_main32 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (inv_main22 var4 var3 var2 var1 var0)) (inv_main22 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 node) (var7 Heap) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Heap)) (or (not (and (inv_main14 var13 var12 var11 var10) (and (= var9 nullAddr) (and (and (and (and (and (and (= var8 (newHeap (alloc var7 (O_node var6)))) (= var5 var4)) (= var3 var2)) (= var1 var0)) (= var9 (newAddr (alloc var7 (O_node var6))))) (is-O_node (read var13 var10))) (and (and (and (= var7 (write var13 var10 (O_node (node 1 (n (getnode (read var13 var10))))))) (= var4 var12)) (= var2 var11)) (= var0 var10)))))) (inv_main22 var8 var5 var9 var1 1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main32 var8 var7 var6 var5) (and (not (= var4 nullAddr)) (and (is-O_node (read var8 var5)) (and (and (and (and (= var3 var8) (= var2 var7)) (= var1 var6)) (= var0 var5)) (= var4 (n (getnode (read var8 var5))))))))) (inv_main31 var3 var2 var1 var4))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main27 var7 var6 var5 var4) (and (not (= var3 nullAddr)) (and (is-O_node (read var7 var4)) (and (and (and (= var2 (write var7 var4 (O_node (node (h (getnode (read var7 var4))) 0)))) (= var3 var6)) (= var1 var5)) (= var0 var4)))))) (inv_main31 var2 var3 var1 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main11 var3 var2 var1 var0) (not (is-O_node (read var3 var2)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main14 var3 var2 var1 var0) (not (is-O_node (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main19 var3 var2 var1 var0) (not (is-O_node (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main25 var3 var2 var1 var0) (not (is-O_node (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main13 var3 var2 var1 var0) (not (is-O_node (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main27 var3 var2 var1 var0) (not (is-O_node (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main31 var3 var2 var1 var0) (not (is-O_node (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (inv_main33 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main32 var3 var2 var1 var0) (not (is-O_node (read var3 var0)))))))
(check-sat)
