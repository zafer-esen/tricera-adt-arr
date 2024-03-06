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
(declare-fun inv_main564_5 (Heap Addr Int) Bool)
(declare-fun inv_main564_5_9 (Heap Addr Addr Int) Bool)
(declare-fun inv_main569_3 (Heap) Bool)
(declare-fun inv_main572_3 (Heap Addr Addr) Bool)
(declare-fun inv_main_13 (Heap Addr Addr) Bool)
(assert (forall ((var0 Heap)) (or (not (= var0 emptyHeap)) (inv_main569_3 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap)) (or (not (inv_main564_5 var2 var1 var0)) (inv_main564_5 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 node) (var2 Heap) (var3 Addr) (var4 Heap)) (or (not (and (inv_main569_3 var4) (and (and (= nullAddr var3) (and (= var2 (newHeap (alloc var4 (O_node var1)))) (= var3 (newAddr (alloc var4 (O_node var1)))))) (= var0 1)))) (inv_main564_5 var2 var3 var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main572_3 var3 var2 var1) (= var0 (write var3 var2 defObj)))) (inv_main_13 var0 var2 var1))))
(assert (forall ((var0 Addr) (var1 node) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 node) (var7 Heap) (var8 Heap) (var9 Addr) (var10 node) (var11 Addr) (var12 Addr) (var13 Heap) (var14 Heap) (var15 Heap)) (or (not (and (inv_main569_3 var15) (and (and (and (and (and (and (and (= var14 var13) (= var12 var11)) (= var10 (getnode (read var13 var11)))) (and (not (= nullAddr var9)) (and (and (= var8 (newHeap (alloc var7 (O_node var6)))) (= var5 var4)) (= var9 (newAddr (alloc var7 (O_node var6))))))) (and (= var13 (write var8 var5 (O_node (node var9)))) (= var11 var5))) (and (= var3 (write var14 var12 (O_node var10))) (= var2 var12))) (and (not (= nullAddr var4)) (and (= var7 (newHeap (alloc var15 (O_node var1)))) (= var4 (newAddr (alloc var15 (O_node var1))))))) (= var0 (|node::next| (getnode (read var3 var2))))))) (inv_main572_3 var3 var2 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (inv_main564_5_9 var3 var2 var1 var0)) (inv_main564_5_9 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 node) (var2 Addr) (var3 Addr) (var4 node) (var5 Heap) (var6 Heap) (var7 Addr) (var8 Heap)) (or (not (and (inv_main569_3 var8) (and (and (and (= nullAddr var7) (and (and (= var6 (newHeap (alloc var5 (O_node var4)))) (= var3 var2)) (= var7 (newAddr (alloc var5 (O_node var4)))))) (and (not (= nullAddr var2)) (and (= var5 (newHeap (alloc var8 (O_node var1)))) (= var2 (newAddr (alloc var8 (O_node var1))))))) (= var0 1)))) (inv_main564_5_9 var6 var3 var7 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main572_3 var2 var1 var0) (and (not (= var1 nullAddr)) (= (read var2 var1) defObj))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_13 var2 var1 var0) (and (not (= var0 nullAddr)) (= (read var2 var0) defObj))))))
(check-sat)
