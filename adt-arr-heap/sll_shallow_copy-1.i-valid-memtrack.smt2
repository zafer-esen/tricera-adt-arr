(set-logic HORN)
(set-info :source |
    Benchmark: C_VC
    Output by Princess (http://www.philipp.ruemmer.org/princess.shtml)
|)
(set-info :status unknown)
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
(declare-fun inv_main575_10 (Heap Addr Int) Bool)
(assert (forall ((var0 Addr) (var1 Heap)) (or (not (and (= var1 emptyHeap) (= var0 nullAddr))) (inv_main569_3 var1 var0))))
(assert (forall ((var0 Int) (var1 Bool) (var2 node) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Bool) (var7 Addr) (var8 node) (var9 Heap) (var10 Heap) (var11 Addr) (var12 node) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Heap) (var18 Heap) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Heap) (var23 Addr) (var24 Addr) (var25 Addr) (var26 Heap) (var27 Addr) (var28 Addr) (var29 Addr) (var30 Addr) (var31 Addr) (var32 Heap) (var33 Heap) (var34 Addr) (var35 Heap)) (or (not (and (inv_main569_3 var35 var34) (and (and (and (and (and (and (and (and (and (= var33 var32) (= var31 var30)) (= var29 var28)) (= var27 (|node::next| (getnode (read var32 var28))))) (and (and (and (= var26 (write var33 var29 defObj)) (or (and (= var31 var29) (= var25 nullAddr)) (and (not (= var31 var29)) (= var25 var31)))) (= var24 var29)) (= var23 var27))) (and (and (and (= var22 (write var26 var23 defObj)) (or (and (= var25 var23) (= var21 nullAddr)) (and (not (= var25 var23)) (= var21 var25)))) (= var20 var24)) (= var19 var23))) (and (and (and (and (and (= var18 var17) (= var16 var15)) (= var14 var13)) (= var12 (getnode (read var17 var13)))) (and (not (= nullAddr var11)) (and (and (and (= var10 (newHeap (alloc var9 (O_node var8)))) (or (and var6 (= var7 (newAddr (alloc var9 (O_node var8))))) (and (not var6) (= var7 var5)))) (= var4 var3)) (= var11 (newAddr (alloc var9 (O_node var8))))))) (and (and (= var17 (write var10 var4 (O_node (node var11)))) (= var15 var7)) (= var13 var4)))) (and (and (= var32 (write var18 var14 (O_node var12))) (= var30 var16)) (= var28 var14))) (and (not (= nullAddr var3)) (and (and (= var9 (newHeap (alloc var35 (O_node var2)))) (or (and var1 (= var5 (newAddr (alloc var35 (O_node var2))))) (and (not var1) (= var5 var34)))) (= var3 (newAddr (alloc var35 (O_node var2))))))) (= var0 0)))) (inv_main575_10 var22 var21 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (inv_main564_5 var3 var2 var1 var0)) (inv_main564_5 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Bool) (var2 Addr) (var3 node) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main569_3 var7 var6) (and (and (= nullAddr var5) (and (and (= var4 (newHeap (alloc var7 (O_node var3)))) (or (and var1 (= var2 (newAddr (alloc var7 (O_node var3))))) (and (not var1) (= var2 var6)))) (= var5 (newAddr (alloc var7 (O_node var3)))))) (= var0 1)))) (inv_main564_5 var4 var2 var5 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (inv_main564_5_9 var4 var3 var2 var1 var0)) (inv_main564_5_9 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Bool) (var2 node) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Bool) (var7 Addr) (var8 node) (var9 Heap) (var10 Heap) (var11 Addr) (var12 Addr) (var13 Heap)) (or (not (and (inv_main569_3 var13 var12) (and (and (and (= nullAddr var11) (and (and (and (= var10 (newHeap (alloc var9 (O_node var8)))) (or (and var6 (= var7 (newAddr (alloc var9 (O_node var8))))) (and (not var6) (= var7 var5)))) (= var4 var3)) (= var11 (newAddr (alloc var9 (O_node var8)))))) (and (not (= nullAddr var3)) (and (and (= var9 (newHeap (alloc var13 (O_node var2)))) (or (and var1 (= var5 (newAddr (alloc var13 (O_node var2))))) (and (not var1) (= var5 var12)))) (= var3 (newAddr (alloc var13 (O_node var2))))))) (= var0 1)))) (inv_main564_5_9 var10 var7 var4 var11 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap)) (not (and (inv_main575_10 var2 var1 var0) (not (= var1 nullAddr))))))
(check-sat)
