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
(declare-fun inv_main2414_5 (Heap Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main2414_5_24 (Heap Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main2442_9 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main2458_9 (Heap Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main2465_5 (Heap Addr) Bool)
(declare-fun inv_main2468_12 (Heap Addr Int) Bool)
(declare-fun inv_main_35 (Heap Addr Addr) Bool)
(assert (forall ((var0 Addr) (var1 Heap)) (or (not (and (= var1 emptyHeap) (= var0 nullAddr))) (inv_main2465_5 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main2442_9 var9 var8 var7 var6 var5) (and (= var4 nullAddr) (and (and (and (and (and (= var3 var9) (= var2 var8)) (= var1 var7)) (= var0 var6)) (= var4 (|node::next| (getnode (read var9 var6))))) (= var5 nullAddr))))) (inv_main_35 var3 var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Int) (var4 Int) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Heap)) (or (not (and (inv_main2414_5 var11 var10 var9 var8 var7 var6) (and (= var5 nullAddr) (and (and (= var4 0) (= var3 0)) (and (and (and (= var2 (write var11 var8 (O_node (node (|node::next| (getnode (read var11 var8))) var7)))) (= var1 var10)) (= var5 var9)) (= var0 var8)))))) (inv_main_35 var2 var1 var5))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Heap) (var9 Int) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Heap)) (or (not (and (inv_main2414_5_24 var16 var15 var14 var13 var12 var11) (and (= var10 nullAddr) (and (= var9 0) (and (and (and (and (and (and (= var8 var7) (= var6 var5)) (= var10 var4)) (= var3 var2)) (= var1 (|node::next| (getnode (read var7 var2))))) (= var0 0)) (and (and (and (= var7 (write var16 (|node::next| (getnode (read var16 var13))) (O_node (node (|node::next| (getnode (read var16 (|node::next| (getnode (read var16 var13)))))) var12)))) (= var5 var15)) (= var4 var14)) (= var2 var13))))))) (inv_main_35 var8 var6 var10))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Bool) (var14 Addr) (var15 internal_node) (var16 Heap) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Addr) (var25 Addr) (var26 Addr) (var27 Addr) (var28 Heap) (var29 Heap) (var30 Addr) (var31 Addr) (var32 Addr) (var33 Addr) (var34 Addr) (var35 Heap)) (or (not (and (inv_main2414_5 var35 var34 var33 var32 var31 var30) (and (and (and (and (and (and (and (and (= var29 var28) (= var27 var26)) (= var25 var24)) (= var23 var22)) (= var21 var20)) (= var19 var18)) (= var17 (|internal_node::next| (getinternal_node (read var28 var18))))) (and (and (and (and (and (and (and (and (= var16 (newHeap (alloc var35 (O_internal_node var15)))) (or (and var13 (= var14 (newAddr (alloc var35 (O_internal_node var15))))) (and (not var13) (= var14 var34)))) (= var12 var33)) (= var11 var32)) (= var10 var31)) (= var9 var30)) (= var8 (newAddr (alloc var35 (O_internal_node var15))))) (and (and (and (and (and (and (= var7 (write var16 var8 (O_internal_node (internal_node nullAddr)))) (= var6 var14)) (= var5 var12)) (= var4 var11)) (= var3 var10)) (= var2 var9)) (= var1 var8))) (not (= var0 0)))) (and (and (and (and (and (= var28 (write var7 var2 (O_internal_node (internal_node var1)))) (= var26 var6)) (= var24 var5)) (= var22 var4)) (= var20 var3)) (= var18 var2))))) (inv_main2414_5 var29 var27 var25 var23 var21 var17))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Bool) (var5 Addr) (var6 node) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Heap) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Bool) (var19 Addr) (var20 internal_node) (var21 Heap) (var22 Heap) (var23 Addr) (var24 Heap)) (or (not (and (inv_main2465_5 var24 var23) (and (and (and (and (and (and (= var22 (newHeap (alloc var21 (O_internal_node var20)))) (or (and var18 (= var19 (newAddr (alloc var21 (O_internal_node var20))))) (and (not var18) (= var19 var17)))) (= var16 var15)) (= var14 var15)) (= var13 (newAddr (alloc var21 (O_internal_node var20))))) (and (and (and (and (= var12 (write var22 var13 (O_internal_node (internal_node nullAddr)))) (= var11 var19)) (= var10 var16)) (= var9 var14)) (= var8 var13))) (and (and (and (and (= var7 (newHeap (alloc var24 (O_node var6)))) (or (and var4 (= var5 (newAddr (alloc var24 (O_node var6))))) (and (not var4) (= var5 var23)))) (= var3 (newAddr (alloc var24 (O_node var6))))) (and (and (= var2 (write var7 var3 (O_node (node nullAddr (|node::nested_node| (getnode (read var7 var3))))))) (= var1 var5)) (= var0 var3))) (and (and (= var21 (write var2 var0 (O_node (node (|node::next| (getnode (read var2 var0))) nullAddr)))) (= var17 var1)) (= var15 var0)))))) (inv_main2414_5 var12 var11 var10 var9 var8 var8))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Heap) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Heap)) (or (not (and (inv_main2458_9 var19 var18 var17 var16 var15 var14) (and (and (and (and (and (and (and (and (= var13 var19) (= var12 var18)) (= var11 var17)) (= var10 var16)) (= var9 var15)) (= var8 var14)) (= var7 (|internal_node::next| (getinternal_node (read var19 var14))))) (and (and (and (and (and (and (= var6 (write var13 var8 defObj)) (or (and (= var12 var8) (= var5 nullAddr)) (and (not (= var12 var8)) (= var5 var12)))) (= var4 var11)) (= var3 var10)) (= var2 var9)) (= var1 var8)) (= var0 var7))) (not (= var14 nullAddr))))) (inv_main2458_9 var6 var5 var4 var3 var2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main_35 var8 var7 var6) (and (and (and (and (and (and (= var5 var8) (= var4 var7)) (= var3 var6)) (= var2 var6)) (= var1 (|node::next| (getnode (read var8 var6))))) (not (= var6 nullAddr))) (= var0 (|node::nested_node| (getnode (read var5 var2))))))) (inv_main2458_9 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap) (var10 Heap) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Heap)) (or (not (and (inv_main2458_9 var16 var15 var14 var13 var12 var11) (and (and (and (and (and (and (and (= var10 var9) (= var8 var7)) (= var6 var5)) (= var4 var3)) (= var2 (|node::next| (getnode (read var9 var3))))) (not (= var3 nullAddr))) (and (= var11 nullAddr) (and (and (and (and (= var9 (write var16 var13 defObj)) (or (and (= var15 var13) (= var7 nullAddr)) (and (not (= var15 var13)) (= var7 var15)))) (= var5 var14)) (= var1 var13)) (= var3 var12)))) (= var0 (|node::nested_node| (getnode (read var10 var4))))))) (inv_main2458_9 var10 var8 var6 var4 var2 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Bool) (var14 Addr) (var15 internal_node) (var16 Heap) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Addr) (var25 Addr) (var26 Addr) (var27 Addr) (var28 Heap) (var29 Heap) (var30 Addr) (var31 Addr) (var32 Addr) (var33 Addr) (var34 Addr) (var35 Heap)) (or (not (and (inv_main2414_5_24 var35 var34 var33 var32 var31 var30) (and (and (and (and (and (and (and (and (= var29 var28) (= var27 var26)) (= var25 var24)) (= var23 var22)) (= var21 var20)) (= var19 var18)) (= var17 (|internal_node::next| (getinternal_node (read var28 var18))))) (and (and (and (and (and (and (and (and (= var16 (newHeap (alloc var35 (O_internal_node var15)))) (or (and var13 (= var14 (newAddr (alloc var35 (O_internal_node var15))))) (and (not var13) (= var14 var34)))) (= var12 var33)) (= var11 var32)) (= var10 var31)) (= var9 var30)) (= var8 (newAddr (alloc var35 (O_internal_node var15))))) (and (and (and (and (and (and (= var7 (write var16 var8 (O_internal_node (internal_node nullAddr)))) (= var6 var14)) (= var5 var12)) (= var4 var11)) (= var3 var10)) (= var2 var9)) (= var1 var8))) (not (= var0 0)))) (and (and (and (and (and (= var28 (write var7 var2 (O_internal_node (internal_node var1)))) (= var26 var6)) (= var24 var5)) (= var22 var4)) (= var20 var3)) (= var18 var2))))) (inv_main2414_5_24 var29 var27 var25 var23 var21 var17))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Heap) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Bool) (var19 Addr) (var20 node) (var21 Heap) (var22 Heap) (var23 Addr) (var24 Addr) (var25 Addr) (var26 Addr) (var27 Heap) (var28 Addr) (var29 Addr) (var30 Addr) (var31 Addr) (var32 Addr) (var33 Addr) (var34 Bool) (var35 Addr) (var36 internal_node) (var37 Heap) (var38 Heap) (var39 Addr) (var40 Addr) (var41 Addr) (var42 Addr) (var43 Addr) (var44 Heap)) (or (not (and (inv_main2414_5 var44 var43 var42 var41 var40 var39) (and (and (and (and (and (and (and (and (= var38 (newHeap (alloc var37 (O_internal_node var36)))) (or (and var34 (= var35 (newAddr (alloc var37 (O_internal_node var36))))) (and (not var34) (= var35 var33)))) (= var32 var31)) (= var30 var29)) (= var28 (newAddr (alloc var37 (O_internal_node var36))))) (and (and (and (and (= var27 (write var38 var28 (O_internal_node (internal_node nullAddr)))) (= var26 var35)) (= var25 var32)) (= var24 var30)) (= var23 var28))) (and (and (and (and (and (and (and (and (= var22 (newHeap (alloc var21 (O_node var20)))) (or (and var18 (= var19 (newAddr (alloc var21 (O_node var20))))) (and (not var18) (= var19 var17)))) (= var16 var15)) (= var14 var13)) (= var12 (newAddr (alloc var21 (O_node var20))))) (and (and (and (and (= var11 (write var22 var12 (O_node (node nullAddr (|node::nested_node| (getnode (read var22 var12))))))) (= var10 var19)) (= var9 var16)) (= var8 var14)) (= var7 var12))) (and (and (and (and (= var6 (write var11 var7 (O_node (node (|node::next| (getnode (read var11 var7))) nullAddr)))) (= var5 var10)) (= var4 var9)) (= var3 var8)) (= var2 var7))) (not (= var1 0))) (and (and (and (= var37 (write var6 var3 (O_node (node var2 (|node::nested_node| (getnode (read var6 var3))))))) (= var33 var5)) (= var31 var4)) (= var29 var3)))) (= var0 0)) (and (and (and (= var21 (write var44 var41 (O_node (node (|node::next| (getnode (read var44 var41))) var40)))) (= var17 var43)) (= var15 var42)) (= var13 var41))))) (inv_main2414_5_24 var27 var26 var25 var24 var23 var23))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Int) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Heap) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Heap) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Bool) (var24 Addr) (var25 node) (var26 Heap) (var27 Heap) (var28 Addr) (var29 Addr) (var30 Addr) (var31 Addr) (var32 Heap) (var33 Addr) (var34 Addr) (var35 Addr) (var36 Addr) (var37 Addr) (var38 Addr) (var39 Bool) (var40 Addr) (var41 internal_node) (var42 Heap) (var43 Heap) (var44 Addr) (var45 Addr) (var46 Addr) (var47 Addr) (var48 Addr) (var49 Heap)) (or (not (and (inv_main2414_5_24 var49 var48 var47 var46 var45 var44) (and (and (and (and (and (and (and (= var43 (newHeap (alloc var42 (O_internal_node var41)))) (or (and var39 (= var40 (newAddr (alloc var42 (O_internal_node var41))))) (and (not var39) (= var40 var38)))) (= var37 var36)) (= var35 var34)) (= var33 (newAddr (alloc var42 (O_internal_node var41))))) (and (and (and (and (= var32 (write var43 var33 (O_internal_node (internal_node nullAddr)))) (= var31 var40)) (= var30 var37)) (= var29 var35)) (= var28 var33))) (and (and (and (and (and (and (and (and (= var27 (newHeap (alloc var26 (O_node var25)))) (or (and var23 (= var24 (newAddr (alloc var26 (O_node var25))))) (and (not var23) (= var24 var22)))) (= var21 var20)) (= var19 var18)) (= var17 (newAddr (alloc var26 (O_node var25))))) (and (and (and (and (= var16 (write var27 var17 (O_node (node nullAddr (|node::nested_node| (getnode (read var27 var17))))))) (= var15 var24)) (= var14 var21)) (= var13 var19)) (= var12 var17))) (and (and (and (and (= var11 (write var16 var12 (O_node (node (|node::next| (getnode (read var16 var12))) nullAddr)))) (= var10 var15)) (= var9 var14)) (= var8 var13)) (= var7 var12))) (not (= var6 0))) (and (and (and (= var42 (write var11 var8 (O_node (node var7 (|node::nested_node| (getnode (read var11 var8))))))) (= var38 var10)) (= var36 var9)) (= var34 var8)))) (and (and (and (and (and (and (= var26 var5) (= var22 var4)) (= var20 var3)) (= var2 var1)) (= var18 (|node::next| (getnode (read var5 var1))))) (= var0 0)) (and (and (and (= var5 (write var49 (|node::next| (getnode (read var49 var46))) (O_node (node (|node::next| (getnode (read var49 (|node::next| (getnode (read var49 var46)))))) var45)))) (= var4 var48)) (= var3 var47)) (= var1 var46)))))) (inv_main2414_5_24 var32 var31 var30 var29 var28 var28))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main2442_9 var10 var9 var8 var7 var6) (and (and (and (and (and (and (= var5 var10) (= var4 var9)) (= var3 var8)) (= var2 var7)) (= var1 var6)) (= var0 (|internal_node::next| (getinternal_node (read var10 var6))))) (not (= var6 nullAddr))))) (inv_main2442_9 var5 var4 var3 var2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main2442_9 var10 var9 var8 var7 var6) (and (and (not (= var5 nullAddr)) (and (and (and (and (and (= var4 var10) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var5 (|node::next| (getnode (read var10 var7))))) (= var6 nullAddr))) (= var0 (|node::nested_node| (getnode (read var4 var5))))))) (inv_main2442_9 var4 var3 var2 var5 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Int) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Heap)) (or (not (and (inv_main2414_5 var12 var11 var10 var9 var8 var7) (and (and (not (= var6 nullAddr)) (and (and (= var5 0) (= var4 0)) (and (and (and (= var3 (write var12 var9 (O_node (node (|node::next| (getnode (read var12 var9))) var8)))) (= var2 var11)) (= var6 var10)) (= var1 var9)))) (= var0 (|node::nested_node| (getnode (read var3 var6))))))) (inv_main2442_9 var3 var2 var6 var6 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap) (var9 Heap) (var10 Int) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Heap)) (or (not (and (inv_main2414_5_24 var17 var16 var15 var14 var13 var12) (and (and (not (= var11 nullAddr)) (and (= var10 0) (and (and (and (and (and (and (= var9 var8) (= var7 var6)) (= var11 var5)) (= var4 var3)) (= var2 (|node::next| (getnode (read var8 var3))))) (= var1 0)) (and (and (and (= var8 (write var17 (|node::next| (getnode (read var17 var14))) (O_node (node (|node::next| (getnode (read var17 (|node::next| (getnode (read var17 var14)))))) var13)))) (= var6 var16)) (= var5 var15)) (= var3 var14))))) (= var0 (|node::nested_node| (getnode (read var9 var11))))))) (inv_main2442_9 var9 var7 var11 var11 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main_35 var3 var2 var1) (and (= var1 nullAddr) (= var0 0)))) (inv_main2468_12 var3 var2 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Heap)) (or (not (and (inv_main2458_9 var11 var10 var9 var8 var7 var6) (and (and (= var5 nullAddr) (and (= var6 nullAddr) (and (and (and (and (= var4 (write var11 var8 defObj)) (or (and (= var10 var8) (= var3 nullAddr)) (and (not (= var10 var8)) (= var3 var10)))) (= var2 var9)) (= var1 var8)) (= var5 var7)))) (= var0 0)))) (inv_main2468_12 var4 var3 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap)) (not (and (inv_main2468_12 var2 var1 var0) (not (= var1 nullAddr))))))
(check-sat)
