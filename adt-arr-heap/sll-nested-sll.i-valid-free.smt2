(set-logic HORN)
(set-info :source |
    Benchmark: C_VC
    Output by Princess (http://www.philipp.ruemmer.org/princess.shtml)
|)
(set-info :status sat)
(declare-heap Heap Addr HeapObject
 defObj
 ((HeapObject 0) (node 0) (internal_node 0)) (
  (
   (O_Int (getInt Int))
   (O_UInt (getUInt Int))
   (O_Addr (getAddr Addr))
   (O_AddrRange (getAddrRange AddrRange))
   (O_node (getnode node))
   (O_internal_node (getinternal_node internal_node))
   (defObj)
  )
  (
   (node (|node::next| Addr) (|node::nested_node| Addr))
  )
  (
   (internal_node (|internal_node::next| Addr))
  )
))
(declare-fun inv_main2414_5 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main2414_5_24 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main2442_9 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main2449_9 (Heap Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main2465_5 (Heap) Bool)
(declare-fun inv_main2467_5 (Heap Addr Addr) Bool)
(declare-fun inv_main_41 (Heap Addr Addr Addr) Bool)
(assert (forall ((var0 Heap)) (or (not (= var0 emptyHeap)) (inv_main2465_5 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Heap)) (or (not (and (inv_main2449_9 var11 var10 var9 var8 var7 var6) (and (= var5 nullAddr) (and (and (and (and (and (= var4 (write var11 var7 defObj)) (= var3 var10)) (= var2 var9)) (= var1 var8)) (= var0 var7)) (= var5 var6))))) (inv_main_41 var4 var3 var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Heap)) (or (not (and (inv_main2467_5 var11 var10 var9) (and (and (and (= var8 nullAddr) (and (and (and (and (= var7 var6) (= var5 var4)) (= var3 var2)) (= var1 var0)) (= var8 (|node::nested_node| (getnode (read var6 var2)))))) (and (and (and (= var6 var11) (= var4 var10)) (= var2 var9)) (= var0 (|node::next| (getnode (read var11 var9)))))) (not (= var9 nullAddr))))) (inv_main_41 var7 var5 var3 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main2442_9 var8 var7 var6 var5) (and (and (and (and (and (= var4 var8) (= var3 var7)) (= var2 var6)) (= var1 var5)) (= var0 (|internal_node::next| (getinternal_node (read var8 var5))))) (not (= var5 nullAddr))))) (inv_main2442_9 var4 var3 var2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main2442_9 var8 var7 var6 var5) (and (and (not (= var4 nullAddr)) (and (and (and (and (= var3 var8) (= var2 var7)) (= var1 var6)) (= var4 (|node::next| (getnode (read var8 var6))))) (= var5 nullAddr))) (= var0 (|node::nested_node| (getnode (read var3 var4))))))) (inv_main2442_9 var3 var2 var4 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Int) (var4 Int) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main2414_5 var10 var9 var8 var7 var6) (and (and (not (= var5 nullAddr)) (and (and (= var4 0) (= var3 0)) (and (and (= var2 (write var10 var8 (O_node (node (|node::next| (getnode (read var10 var8))) var7)))) (= var5 var9)) (= var1 var8)))) (= var0 (|node::nested_node| (getnode (read var2 var5))))))) (inv_main2442_9 var2 var5 var5 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Heap) (var8 Int) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Heap)) (or (not (and (inv_main2414_5_24 var14 var13 var12 var11 var10) (and (and (not (= var9 nullAddr)) (and (= var8 0) (and (and (and (and (and (= var7 var6) (= var9 var5)) (= var4 var3)) (= var2 (|node::next| (getnode (read var6 var3))))) (= var1 0)) (and (and (= var6 (write var14 (|node::next| (getnode (read var14 var12))) (O_node (node (|node::next| (getnode (read var14 (|node::next| (getnode (read var14 var12)))))) var11)))) (= var5 var13)) (= var3 var12))))) (= var0 (|node::nested_node| (getnode (read var7 var9))))))) (inv_main2442_9 var7 var9 var9 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 internal_node) (var13 Heap) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Heap) (var24 Heap) (var25 Addr) (var26 Addr) (var27 Addr) (var28 Addr) (var29 Heap)) (or (not (and (inv_main2414_5 var29 var28 var27 var26 var25) (and (and (and (and (and (and (and (= var24 var23) (= var22 var21)) (= var20 var19)) (= var18 var17)) (= var16 var15)) (= var14 (|internal_node::next| (getinternal_node (read var23 var15))))) (and (and (and (and (and (and (and (= var13 (newHeap (alloc var29 (O_internal_node var12)))) (= var11 var28)) (= var10 var27)) (= var9 var26)) (= var8 var25)) (= var7 (newAddr (alloc var29 (O_internal_node var12))))) (and (and (and (and (and (= var6 (write var13 var7 (O_internal_node (internal_node nullAddr)))) (= var5 var11)) (= var4 var10)) (= var3 var9)) (= var2 var8)) (= var1 var7))) (not (= var0 0)))) (and (and (and (and (= var23 (write var6 var2 (O_internal_node (internal_node var1)))) (= var21 var5)) (= var19 var4)) (= var17 var3)) (= var15 var2))))) (inv_main2414_5 var24 var22 var20 var18 var14))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 node) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 internal_node) (var14 Heap) (var15 Heap) (var16 Heap)) (or (not (and (inv_main2465_5 var16) (and (and (and (and (and (= var15 (newHeap (alloc var14 (O_internal_node var13)))) (= var12 var11)) (= var10 var11)) (= var9 (newAddr (alloc var14 (O_internal_node var13))))) (and (and (and (= var8 (write var15 var9 (O_internal_node (internal_node nullAddr)))) (= var7 var12)) (= var6 var10)) (= var5 var9))) (and (and (and (= var4 (newHeap (alloc var16 (O_node var3)))) (= var2 (newAddr (alloc var16 (O_node var3))))) (and (= var1 (write var4 var2 (O_node (node nullAddr (|node::nested_node| (getnode (read var4 var2))))))) (= var0 var2))) (and (= var14 (write var1 var0 (O_node (node (|node::next| (getnode (read var1 var0))) nullAddr)))) (= var11 var0)))))) (inv_main2414_5 var8 var7 var6 var5 var5))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main_41 var7 var6 var5 var4) (and (and (and (= var3 (write var7 var5 defObj)) (= var2 var6)) (= var1 var5)) (= var0 var4)))) (inv_main2467_5 var3 var2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main2442_9 var7 var6 var5 var4) (and (= var3 nullAddr) (and (and (and (and (= var2 var7) (= var1 var6)) (= var0 var5)) (= var3 (|node::next| (getnode (read var7 var5))))) (= var4 nullAddr))))) (inv_main2467_5 var2 var1 var1))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Int) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main2414_5 var9 var8 var7 var6 var5) (and (= var4 nullAddr) (and (and (= var3 0) (= var2 0)) (and (and (= var1 (write var9 var7 (O_node (node (|node::next| (getnode (read var9 var7))) var6)))) (= var4 var8)) (= var0 var7)))))) (inv_main2467_5 var1 var4 var4))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Heap) (var7 Int) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Heap)) (or (not (and (inv_main2414_5_24 var13 var12 var11 var10 var9) (and (= var8 nullAddr) (and (= var7 0) (and (and (and (and (and (= var6 var5) (= var8 var4)) (= var3 var2)) (= var1 (|node::next| (getnode (read var5 var2))))) (= var0 0)) (and (and (= var5 (write var13 (|node::next| (getnode (read var13 var11))) (O_node (node (|node::next| (getnode (read var13 (|node::next| (getnode (read var13 var11)))))) var10)))) (= var4 var12)) (= var2 var11))))))) (inv_main2467_5 var6 var8 var8))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 internal_node) (var13 Heap) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Heap) (var24 Heap) (var25 Addr) (var26 Addr) (var27 Addr) (var28 Addr) (var29 Heap)) (or (not (and (inv_main2414_5_24 var29 var28 var27 var26 var25) (and (and (and (and (and (and (and (= var24 var23) (= var22 var21)) (= var20 var19)) (= var18 var17)) (= var16 var15)) (= var14 (|internal_node::next| (getinternal_node (read var23 var15))))) (and (and (and (and (and (and (and (= var13 (newHeap (alloc var29 (O_internal_node var12)))) (= var11 var28)) (= var10 var27)) (= var9 var26)) (= var8 var25)) (= var7 (newAddr (alloc var29 (O_internal_node var12))))) (and (and (and (and (and (= var6 (write var13 var7 (O_internal_node (internal_node nullAddr)))) (= var5 var11)) (= var4 var10)) (= var3 var9)) (= var2 var8)) (= var1 var7))) (not (= var0 0)))) (and (and (and (and (= var23 (write var6 var2 (O_internal_node (internal_node var1)))) (= var21 var5)) (= var19 var4)) (= var17 var3)) (= var15 var2))))) (inv_main2414_5_24 var24 var22 var20 var18 var14))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 node) (var16 Heap) (var17 Heap) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Heap) (var22 Addr) (var23 Addr) (var24 Addr) (var25 Addr) (var26 Addr) (var27 internal_node) (var28 Heap) (var29 Heap) (var30 Addr) (var31 Addr) (var32 Addr) (var33 Addr) (var34 Heap)) (or (not (and (inv_main2414_5 var34 var33 var32 var31 var30) (and (and (and (and (and (and (and (= var29 (newHeap (alloc var28 (O_internal_node var27)))) (= var26 var25)) (= var24 var23)) (= var22 (newAddr (alloc var28 (O_internal_node var27))))) (and (and (and (= var21 (write var29 var22 (O_internal_node (internal_node nullAddr)))) (= var20 var26)) (= var19 var24)) (= var18 var22))) (and (and (and (and (and (and (and (= var17 (newHeap (alloc var16 (O_node var15)))) (= var14 var13)) (= var12 var11)) (= var10 (newAddr (alloc var16 (O_node var15))))) (and (and (and (= var9 (write var17 var10 (O_node (node nullAddr (|node::nested_node| (getnode (read var17 var10))))))) (= var8 var14)) (= var7 var12)) (= var6 var10))) (and (and (and (= var5 (write var9 var6 (O_node (node (|node::next| (getnode (read var9 var6))) nullAddr)))) (= var4 var8)) (= var3 var7)) (= var2 var6))) (not (= var1 0))) (and (and (= var28 (write var5 var3 (O_node (node var2 (|node::nested_node| (getnode (read var5 var3))))))) (= var25 var4)) (= var23 var3)))) (= var0 0)) (and (and (= var16 (write var34 var32 (O_node (node (|node::next| (getnode (read var34 var32))) var31)))) (= var13 var33)) (= var11 var32))))) (inv_main2414_5_24 var21 var20 var19 var18 var18))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Int) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Heap) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr) (var19 node) (var20 Heap) (var21 Heap) (var22 Addr) (var23 Addr) (var24 Addr) (var25 Heap) (var26 Addr) (var27 Addr) (var28 Addr) (var29 Addr) (var30 Addr) (var31 internal_node) (var32 Heap) (var33 Heap) (var34 Addr) (var35 Addr) (var36 Addr) (var37 Addr) (var38 Heap)) (or (not (and (inv_main2414_5_24 var38 var37 var36 var35 var34) (and (and (and (and (and (and (= var33 (newHeap (alloc var32 (O_internal_node var31)))) (= var30 var29)) (= var28 var27)) (= var26 (newAddr (alloc var32 (O_internal_node var31))))) (and (and (and (= var25 (write var33 var26 (O_internal_node (internal_node nullAddr)))) (= var24 var30)) (= var23 var28)) (= var22 var26))) (and (and (and (and (and (and (and (= var21 (newHeap (alloc var20 (O_node var19)))) (= var18 var17)) (= var16 var15)) (= var14 (newAddr (alloc var20 (O_node var19))))) (and (and (and (= var13 (write var21 var14 (O_node (node nullAddr (|node::nested_node| (getnode (read var21 var14))))))) (= var12 var18)) (= var11 var16)) (= var10 var14))) (and (and (and (= var9 (write var13 var10 (O_node (node (|node::next| (getnode (read var13 var10))) nullAddr)))) (= var8 var12)) (= var7 var11)) (= var6 var10))) (not (= var5 0))) (and (and (= var32 (write var9 var7 (O_node (node var6 (|node::nested_node| (getnode (read var9 var7))))))) (= var29 var8)) (= var27 var7)))) (and (and (and (and (and (= var20 var4) (= var17 var3)) (= var2 var1)) (= var15 (|node::next| (getnode (read var4 var1))))) (= var0 0)) (and (and (= var4 (write var38 (|node::next| (getnode (read var38 var36))) (O_node (node (|node::next| (getnode (read var38 (|node::next| (getnode (read var38 var36)))))) var35)))) (= var3 var37)) (= var1 var36)))))) (inv_main2414_5_24 var25 var24 var23 var22 var22))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Heap)) (or (not (and (inv_main2449_9 var12 var11 var10 var9 var8 var7) (and (and (not (= var6 nullAddr)) (and (and (and (and (and (= var5 (write var12 var8 defObj)) (= var4 var11)) (= var3 var10)) (= var2 var9)) (= var1 var8)) (= var6 var7))) (= var0 (|internal_node::next| (getinternal_node (read var5 var6))))))) (inv_main2449_9 var5 var4 var3 var2 var6 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Heap)) (or (not (and (inv_main2467_5 var12 var11 var10) (and (and (and (and (not (= var9 nullAddr)) (and (and (and (and (= var8 var7) (= var6 var5)) (= var4 var3)) (= var2 var1)) (= var9 (|node::nested_node| (getnode (read var7 var3)))))) (and (and (and (= var7 var12) (= var5 var11)) (= var3 var10)) (= var1 (|node::next| (getnode (read var12 var10)))))) (not (= var10 nullAddr))) (= var0 (|internal_node::next| (getinternal_node (read var8 var9))))))) (inv_main2449_9 var8 var6 var4 var2 var9 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (not (and (inv_main2449_9 var5 var4 var3 var2 var1 var0) (and (not (= var1 nullAddr)) (= (read var5 var1) defObj))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_41 var3 var2 var1 var0) (and (not (= var1 nullAddr)) (= (read var3 var1) defObj))))))
(check-sat)