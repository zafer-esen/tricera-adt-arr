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
   (O_AddrRange (getAddrRange AddrRange))
   (O_node (getnode node))
   (defObj)
  )
  (
   (node (|node::h| Int) (|node::n| Addr))
  )
))
(declare-fun inv_main532_3 (Heap) Bool)
(declare-fun inv_main533_15 (Heap Addr Int) Bool)
(declare-fun inv_main535_3_4 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main539_17 (Heap Addr Addr Addr Int) Bool)
(declare-fun inv_main_11 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main_12 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main_16 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main_17 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main_3 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main_7 (Heap Addr Addr Addr) Bool)
(assert (forall ((var0 Heap)) (or (not (= var0 emptyHeap)) (inv_main532_3 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Int) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main_11 var9 var8 var7 var6) (and (= var5 0) (and (is-O_node (read var9 var6)) (and (and (and (and (= var4 var9) (= var3 var8)) (= var2 var7)) (= var1 var6)) (= var0 (|node::n| (getnode (read var9 var6))))))))) (inv_main_3 var4 var3 var2 var0))))
(assert (forall ((var0 Addr) (var1 node) (var2 Heap) (var3 Addr) (var4 Int) (var5 Heap)) (or (not (and (inv_main532_3 var5) (and (= var4 0) (and (not (= var3 nullAddr)) (and (= var2 (newHeap (alloc var5 (O_node var1)))) (= var3 (newAddr (alloc var5 (O_node var1))))))))) (inv_main_3 var2 var3 var0 var3))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (inv_main539_17 var4 var3 var2 var1 var0)) (inv_main539_17 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 node) (var8 Heap) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Heap)) (or (not (and (inv_main535_3_4 var14 var13 var12 var11) (and (and (= var10 nullAddr) (and (and (and (and (and (and (= var9 (newHeap (alloc var8 (O_node var7)))) (= var6 var5)) (= var4 var3)) (= var2 var1)) (= var10 (newAddr (alloc var8 (O_node var7))))) (and (is-O_node (read var14 var11)) (is-O_node (read var14 var11)))) (and (and (and (= var8 (write var14 var11 (O_node (node 1 (|node::n| (getnode (read var14 var11))))))) (= var5 var13)) (= var3 var12)) (= var1 var11)))) (= var0 1)))) (inv_main539_17 var9 var6 var10 var2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 node) (var7 Heap) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Heap)) (or (not (and (inv_main535_3_4 var13 var12 var11 var10) (and (not (= var9 nullAddr)) (and (and (and (and (and (and (= var8 (newHeap (alloc var7 (O_node var6)))) (= var5 var4)) (= var3 var2)) (= var1 var0)) (= var9 (newAddr (alloc var7 (O_node var6))))) (and (is-O_node (read var13 var10)) (is-O_node (read var13 var10)))) (and (and (and (= var7 (write var13 var10 (O_node (node 1 (|node::n| (getnode (read var13 var10))))))) (= var4 var12)) (= var2 var11)) (= var0 var10)))))) (inv_main_7 var8 var5 var9 var1))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main_7 var4 var3 var2 var1) (and (and (is-O_node (read var4 var1)) (is-O_node (read var4 var1))) (= var0 (write var4 var1 (O_node (node (|node::h| (getnode (read var4 var1))) var2))))))) (inv_main_11 var0 var3 var2 var1))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main_3 var4 var3 var2 var1) (and (and (is-O_node (read var4 var1)) (is-O_node (read var4 var1))) (= var0 (write var4 var1 (O_node (node 1 (|node::n| (getnode (read var4 var1)))))))))) (inv_main_12 var0 var3 var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main_16 var8 var7 var6 var5) (and (and (= var4 1) (is-O_node (read var8 var5))) (and (and (and (and (= var3 var8) (= var2 var7)) (= var1 var6)) (= var0 var5)) (= var4 (|node::h| (getnode (read var8 var5)))))))) (inv_main_17 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main_17 var8 var7 var6 var5) (and (not (= var4 nullAddr)) (and (is-O_node (read var8 var5)) (and (and (and (and (= var3 var8) (= var2 var7)) (= var1 var6)) (= var0 var5)) (= var4 (|node::n| (getnode (read var8 var5))))))))) (inv_main_16 var3 var2 var1 var4))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main_12 var7 var6 var5 var4) (and (not (= var3 nullAddr)) (and (and (is-O_node (read var7 var4)) (is-O_node (read var7 var4))) (and (and (and (= var2 (write var7 var4 (O_node (node (|node::h| (getnode (read var7 var4))) 0)))) (= var3 var6)) (= var1 var5)) (= var0 var4)))))) (inv_main_16 var2 var3 var1 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Int) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main_11 var9 var8 var7 var6) (and (not (= var5 0)) (and (is-O_node (read var9 var6)) (and (and (and (and (= var4 var9) (= var3 var8)) (= var2 var7)) (= var1 var6)) (= var0 (|node::n| (getnode (read var9 var6))))))))) (inv_main535_3_4 var4 var3 var2 var0))))
(assert (forall ((var0 Addr) (var1 node) (var2 Heap) (var3 Addr) (var4 Int) (var5 Heap)) (or (not (and (inv_main532_3 var5) (and (not (= var4 0)) (and (not (= var3 nullAddr)) (and (= var2 (newHeap (alloc var5 (O_node var1)))) (= var3 (newAddr (alloc var5 (O_node var1))))))))) (inv_main535_3_4 var2 var3 var0 var3))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap)) (or (not (inv_main533_15 var2 var1 var0)) (inv_main533_15 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 node) (var2 Heap) (var3 Addr) (var4 Heap)) (or (not (and (inv_main532_3 var4) (and (and (= var3 nullAddr) (and (= var2 (newHeap (alloc var4 (O_node var1)))) (= var3 (newAddr (alloc var4 (O_node var1)))))) (= var0 1)))) (inv_main533_15 var2 var3 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main535_3_4 var3 var2 var1 var0) (not (is-O_node (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main535_3_4 var3 var2 var1 var0) (and (is-O_node (read var3 var0)) (not (is-O_node (read var3 var0))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_7 var3 var2 var1 var0) (not (is-O_node (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_7 var3 var2 var1 var0) (and (is-O_node (read var3 var0)) (not (is-O_node (read var3 var0))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_11 var3 var2 var1 var0) (not (is-O_node (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_3 var3 var2 var1 var0) (not (is-O_node (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_3 var3 var2 var1 var0) (and (is-O_node (read var3 var0)) (not (is-O_node (read var3 var0))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_12 var3 var2 var1 var0) (not (is-O_node (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_12 var3 var2 var1 var0) (and (is-O_node (read var3 var0)) (not (is-O_node (read var3 var0))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_16 var3 var2 var1 var0) (not (is-O_node (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_17 var3 var2 var1 var0) (not (is-O_node (read var3 var0)))))))
(check-sat)