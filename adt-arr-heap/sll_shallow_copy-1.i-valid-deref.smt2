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
   (node (|node::next| Addr))
  )
))
(declare-fun inv_main561_1_4 (Heap Addr Addr) Bool)
(declare-fun inv_main564_5 (Heap Addr Int) Bool)
(declare-fun inv_main564_5_9 (Heap Addr Addr Int) Bool)
(declare-fun inv_main569_3 (Heap) Bool)
(declare-fun inv_main571_3 (Heap Addr node) Bool)
(declare-fun inv_main_12 (Heap Addr) Bool)
(declare-fun inv_main_3 (Heap Addr) Bool)
(assert (forall ((var0 Heap)) (or (not (= var0 emptyHeap)) (inv_main569_3 var0))))
(assert (forall ((var0 node) (var1 Addr) (var2 Heap)) (or (not (and (inv_main_3 var2 var1) (and (is-O_node (read var2 var1)) (= var0 (getnode (read var2 var1)))))) (inv_main571_3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (inv_main564_5_9 var3 var2 var1 var0)) (inv_main564_5_9 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 node) (var2 Addr) (var3 Addr) (var4 node) (var5 Heap) (var6 Heap) (var7 Addr) (var8 Heap)) (or (not (and (inv_main569_3 var8) (and (and (and (= nullAddr var7) (and (and (= var6 (newHeap (alloc var5 (O_node var4)))) (= var3 var2)) (= var7 (newAddr (alloc var5 (O_node var4)))))) (and (not (= nullAddr var2)) (and (= var5 (newHeap (alloc var8 (O_node var1)))) (= var2 (newAddr (alloc var8 (O_node var1))))))) (= var0 1)))) (inv_main564_5_9 var6 var3 var7 var0))))
(assert (forall ((var0 Heap) (var1 node) (var2 Addr) (var3 Heap)) (or (not (and (inv_main571_3 var3 var2 var1) (and (and (is-O_node (read var3 var2)) (is-O_node (read var3 var2))) (= var0 (write var3 var2 (O_node var1)))))) (inv_main_12 var0 var2))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main561_1_4 var3 var2 var1) (and (and (is-O_node (read var3 var2)) (is-O_node (read var3 var2))) (= var0 (write var3 var2 (O_node (node var1))))))) (inv_main_3 var0 var2))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap)) (or (not (inv_main564_5 var2 var1 var0)) (inv_main564_5 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 node) (var2 Heap) (var3 Addr) (var4 Heap)) (or (not (and (inv_main569_3 var4) (and (and (= nullAddr var3) (and (= var2 (newHeap (alloc var4 (O_node var1)))) (= var3 (newAddr (alloc var4 (O_node var1)))))) (= var0 1)))) (inv_main564_5 var2 var3 var0))))
(assert (forall ((var0 node) (var1 Addr) (var2 Addr) (var3 node) (var4 Heap) (var5 Heap) (var6 Addr) (var7 Heap)) (or (not (and (inv_main569_3 var7) (and (and (not (= nullAddr var6)) (and (and (= var5 (newHeap (alloc var4 (O_node var3)))) (= var2 var1)) (= var6 (newAddr (alloc var4 (O_node var3)))))) (and (not (= nullAddr var1)) (and (= var4 (newHeap (alloc var7 (O_node var0)))) (= var1 (newAddr (alloc var7 (O_node var0))))))))) (inv_main561_1_4 var5 var2 var6))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main561_1_4 var2 var1 var0) (not (is-O_node (read var2 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main561_1_4 var2 var1 var0) (and (is-O_node (read var2 var1)) (not (is-O_node (read var2 var1))))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main_3 var1 var0) (not (is-O_node (read var1 var0)))))))
(assert (forall ((var0 node) (var1 Addr) (var2 Heap)) (not (and (inv_main571_3 var2 var1 var0) (not (is-O_node (read var2 var1)))))))
(assert (forall ((var0 node) (var1 Addr) (var2 Heap)) (not (and (inv_main571_3 var2 var1 var0) (and (is-O_node (read var2 var1)) (not (is-O_node (read var2 var1))))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main_12 var1 var0) (not (is-O_node (read var1 var0)))))))
(check-sat)
