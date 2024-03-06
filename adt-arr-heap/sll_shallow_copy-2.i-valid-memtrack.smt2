(set-logic HORN)
(set-info :source |
    Benchmark: C_VC
    Output by Princess (http://www.philipp.ruemmer.org/princess.shtml)
|)
(set-info :status unsat)
(declare-datatype bool (
  (true)
  (false)
))
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
(declare-fun inv_main564_5 (Heap Addr Addr Int) Bool)
(declare-fun inv_main564_5_9 (Heap Addr Addr Addr Int) Bool)
(declare-fun inv_main569_3 (Heap Addr) Bool)
(declare-fun inv_main573_10 (Heap Addr Int) Bool)
(assert (forall ((var0 Addr) (var1 Heap)) (or (not (and (= var1 emptyHeap) (= var0 nullAddr))) (inv_main569_3 var1 var0))))
(assert (forall ((var0 Int) (var1 Bool) (var2 node) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Bool) (var13 Addr) (var14 node) (var15 Heap) (var16 Heap) (var17 Addr) (var18 node) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Heap) (var24 Heap) (var25 Addr) (var26 Heap)) (or (not (and (inv_main569_3 var26 var25) (and (and (and (and (and (and (and (and (and (= var24 var23) (= var22 var21)) (= var20 var19)) (= var18 (getnode (read var23 (|node::next| (getnode (read var23 var19))))))) (and (not (= nullAddr var17)) (and (and (and (= var16 (newHeap (alloc var15 (O_node var14)))) (or (and var12 (= var13 (newAddr (alloc var15 (O_node var14))))) (and (not var12) (= var13 var11)))) (= var10 var9)) (= var17 (newAddr (alloc var15 (O_node var14))))))) (and (and (= var23 (write var16 var10 (O_node (node var17)))) (= var21 var13)) (= var19 var10))) (and (and (= var8 (write var24 var20 (O_node var18))) (= var7 var22)) (= var6 var20))) (and (and (= var5 (write var8 var6 defObj)) (or (and (= var7 var6) (= var4 nullAddr)) (and (not (= var7 var6)) (= var4 var7)))) (= var3 var6))) (and (not (= nullAddr var9)) (and (and (= var15 (newHeap (alloc var26 (O_node var2)))) (or (and var1 (= var11 (newAddr (alloc var26 (O_node var2))))) (and (not var1) (= var11 var25)))) (= var9 (newAddr (alloc var26 (O_node var2))))))) (= var0 0)))) (inv_main573_10 var5 var4 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (inv_main564_5_9 var4 var3 var2 var1 var0)) (inv_main564_5_9 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Bool) (var2 node) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Bool) (var7 Addr) (var8 node) (var9 Heap) (var10 Heap) (var11 Addr) (var12 Addr) (var13 Heap)) (or (not (and (inv_main569_3 var13 var12) (and (and (and (= nullAddr var11) (and (and (and (= var10 (newHeap (alloc var9 (O_node var8)))) (or (and var6 (= var7 (newAddr (alloc var9 (O_node var8))))) (and (not var6) (= var7 var5)))) (= var4 var3)) (= var11 (newAddr (alloc var9 (O_node var8)))))) (and (not (= nullAddr var3)) (and (and (= var9 (newHeap (alloc var13 (O_node var2)))) (or (and var1 (= var5 (newAddr (alloc var13 (O_node var2))))) (and (not var1) (= var5 var12)))) (= var3 (newAddr (alloc var13 (O_node var2))))))) (= var0 1)))) (inv_main564_5_9 var10 var7 var4 var11 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (inv_main564_5 var3 var2 var1 var0)) (inv_main564_5 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Bool) (var2 Addr) (var3 node) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main569_3 var7 var6) (and (and (= nullAddr var5) (and (and (= var4 (newHeap (alloc var7 (O_node var3)))) (or (and var1 (= var2 (newAddr (alloc var7 (O_node var3))))) (and (not var1) (= var2 var6)))) (= var5 (newAddr (alloc var7 (O_node var3)))))) (= var0 1)))) (inv_main564_5 var4 var2 var5 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap)) (not (and (inv_main573_10 var2 var1 var0) (not (= var1 nullAddr))))))
(check-sat)
