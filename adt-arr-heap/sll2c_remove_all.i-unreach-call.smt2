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
   (node (|node::next| Addr) (|node::data| Int))
  )
))
(declare-fun inv_main577_5 (Heap Int Int Int Int Int Addr Int) Bool)
(declare-fun inv_main577_5_11 (Heap Int Int Int Int Addr Addr Int Addr Int) Bool)
(declare-fun inv_main585_3 (Heap Int Int Int Int Addr Addr) Bool)
(declare-fun inv_main601_5 (Heap Int Int Addr Int Int Addr Addr) Bool)
(declare-fun inv_main613_3 (Heap Int Int) Bool)
(declare-fun inv_main614_3 (Heap Int Int Addr Int) Bool)
(declare-fun inv_main_30 (Heap Int Int Addr Int) Bool)
(assert (forall ((var0 Int) (var1 Int) (var2 Heap)) (or (not (and (and (= var2 emptyHeap) (= var1 2)) (= var0 1))) (inv_main613_3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Int) (var7 Int) (var8 Int) (var9 Int) (var10 Addr) (var11 Addr) (var12 Int) (var13 Int) (var14 Int) (var15 Int) (var16 Heap) (var17 Heap) (var18 Addr) (var19 Addr) (var20 Int) (var21 Int) (var22 Addr) (var23 Int) (var24 Int) (var25 Heap)) (or (not (and (inv_main601_5 var25 var24 var23 var22 var21 var20 var19 var18) (and (and (and (and (and (and (and (and (and (= var17 var16) (= var15 var14)) (= var13 var12)) (= var11 var10)) (= var9 var8)) (= var7 var6)) (= var5 var4)) (= var3 var2)) (= var1 (|node::next| (getnode (read var16 var2))))) (and (not (= var0 var10)) (and (and (and (and (and (and (and (and (= var16 var25) (= var14 var24)) (= var12 var23)) (= var10 var22)) (= var8 var21)) (= var6 var20)) (= var4 var19)) (= var2 var18)) (= var0 (|node::next| (getnode (read var25 var18))))))))) (inv_main601_5 var17 var15 var13 var11 var9 var7 var5 var1))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Int) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Int) (var8 Addr) (var9 Int) (var10 Int) (var11 Heap)) (or (not (and (inv_main614_3 var11 var10 var9 var8 var7) (and (and (not (= var6 var5)) (and (and (and (and (and (and (= var4 var11) (= var3 var10)) (= var2 var9)) (= var5 var8)) (= var1 var7)) (= var0 3)) (= var6 (|node::next| (getnode (read var11 var8)))))) (<= 0 (+ (+ var10 (* (- 1) var7)) (- 1)))))) (inv_main601_5 var4 var3 var2 var5 var1 var0 var6 var5))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Heap)) (or (not (inv_main577_5 var7 var6 var5 var4 var3 var2 var1 var0)) (inv_main577_5 var7 var6 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 node) (var7 Heap) (var8 Addr) (var9 Int) (var10 Int) (var11 Heap)) (or (not (and (inv_main613_3 var11 var10 var9) (and (and (= nullAddr var8) (and (and (and (and (and (and (= var7 (newHeap (alloc var11 (O_node var6)))) (= var5 var10)) (= var4 var9)) (= var3 var10)) (= var2 var9)) (= var1 var9)) (= var8 (newAddr (alloc var11 (O_node var6)))))) (= var0 1)))) (inv_main577_5 var7 var5 var4 var3 var2 var1 var8 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Int) (var6 Int) (var7 Int) (var8 Heap) (var9 node) (var10 Addr) (var11 Int) (var12 Addr) (var13 Addr) (var14 Int) (var15 Int) (var16 Int) (var17 Int) (var18 Heap) (var19 Addr) (var20 Int) (var21 Int) (var22 Addr) (var23 Addr) (var24 Addr) (var25 Addr) (var26 Int) (var27 Int) (var28 Int) (var29 Int) (var30 Int) (var31 Int) (var32 Int) (var33 Int) (var34 Addr) (var35 Heap) (var36 Heap) (var37 Addr) (var38 Addr) (var39 Int) (var40 Int) (var41 Int) (var42 Int) (var43 Heap)) (or (not (and (inv_main585_3 var43 var42 var41 var40 var39 var38 var37) (and (and (and (and (and (and (and (and (and (and (and (and (and (= var36 (write var35 var34 (O_node (node nullAddr (|node::data| (getnode (read var35 var34))))))) (= var33 var32)) (= var31 var30)) (= var29 var28)) (= var27 var26)) (= var25 var24)) (= var23 var22)) (= var21 var20)) (= var19 var34)) (and (and (and (and (and (and (and (and (= var18 (write var36 var19 (O_node (node (|node::next| (getnode (read var36 var19))) var21)))) (= var17 var33)) (= var16 var31)) (= var15 var29)) (= var14 var27)) (= var13 var25)) (= var12 var23)) (= var11 var21)) (= var10 var19))) (and (not (= nullAddr var34)) (and (and (and (and (and (and (and (and (= var35 (newHeap (alloc var43 (O_node var9)))) (= var32 var42)) (= var30 var41)) (= var28 var40)) (= var26 var39)) (= var24 var38)) (= var22 var37)) (= var20 var39)) (= var34 (newAddr (alloc var43 (O_node var9))))))) (and (and (and (and (and (and (and (= var8 (write var18 var10 (O_node (node var13 (|node::data| (getnode (read var18 var10))))))) (= var7 var17)) (= var6 var16)) (= var5 var15)) (= var4 var14)) (= var3 var13)) (= var2 var12)) (= var1 var10))) (<= 0 (+ (+ var40 (- 1)) (- 1)))) (= var0 (+ var5 (- 1)))))) (inv_main585_3 var8 var7 var6 var0 var4 var1 var2))))
(assert (forall ((var0 node) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Heap) (var8 Addr) (var9 Int) (var10 Int) (var11 Int) (var12 Int) (var13 Int) (var14 Int) (var15 Int) (var16 Int) (var17 Int) (var18 Int) (var19 Addr) (var20 Heap) (var21 Heap) (var22 Int) (var23 Int) (var24 Heap)) (or (not (and (inv_main613_3 var24 var23 var22) (and (and (and (and (and (and (and (and (= var21 (write var20 var19 (O_node (node nullAddr (|node::data| (getnode (read var20 var19))))))) (= var18 var17)) (= var16 var15)) (= var14 var13)) (= var12 var11)) (= var10 var9)) (= var8 var19)) (and (and (and (and (and (and (= var7 (write var21 var8 (O_node (node (|node::next| (getnode (read var21 var8))) var10)))) (= var6 var18)) (= var5 var16)) (= var4 var14)) (= var3 var12)) (= var2 var10)) (= var1 var8))) (and (not (= nullAddr var19)) (and (and (and (and (and (and (= var20 (newHeap (alloc var24 (O_node var0)))) (= var17 var23)) (= var15 var22)) (= var13 var23)) (= var11 var22)) (= var9 var22)) (= var19 (newAddr (alloc var24 (O_node var0))))))))) (inv_main585_3 var7 var6 var5 var4 var3 var1 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Int) (var6 Int) (var7 Int) (var8 Int) (var9 Heap)) (or (not (inv_main577_5_11 var9 var8 var7 var6 var5 var4 var3 var2 var1 var0)) (inv_main577_5_11 var9 var8 var7 var6 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Int) (var5 Int) (var6 Int) (var7 Int) (var8 node) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Int) (var14 Int) (var15 Int) (var16 Int) (var17 Heap)) (or (not (and (inv_main585_3 var17 var16 var15 var14 var13 var12 var11) (and (and (and (= nullAddr var10) (and (and (and (and (and (and (and (and (= var9 (newHeap (alloc var17 (O_node var8)))) (= var7 var16)) (= var6 var15)) (= var5 var14)) (= var4 var13)) (= var3 var12)) (= var2 var11)) (= var1 var13)) (= var10 (newAddr (alloc var17 (O_node var8)))))) (<= 0 (+ (+ var14 (- 1)) (- 1)))) (= var0 1)))) (inv_main577_5_11 var9 var7 var6 var5 var4 var3 var2 var1 var10 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Addr) (var6 Int) (var7 Int) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Int) (var12 Int) (var13 Addr) (var14 Int) (var15 Int) (var16 Heap) (var17 Addr) (var18 Addr) (var19 Int) (var20 Int) (var21 Int) (var22 Int) (var23 Heap) (var24 Addr) (var25 Addr) (var26 Addr) (var27 Addr) (var28 Int) (var29 Int) (var30 Addr) (var31 Int) (var32 Int) (var33 Heap)) (or (not (and (inv_main601_5 var33 var32 var31 var30 var29 var28 var27 var26) (and (and (and (and (= var25 var24) (and (and (and (and (and (and (and (and (= var23 var33) (= var22 var32)) (= var21 var31)) (= var24 var30)) (= var20 var29)) (= var19 var28)) (= var18 var27)) (= var17 var26)) (= var25 (|node::next| (getnode (read var33 var26)))))) (and (and (and (and (and (and (and (= var16 (write var23 var17 (O_node (node var18 (|node::data| (getnode (read var23 var17))))))) (= var15 var22)) (= var14 var21)) (= var13 var24)) (= var12 var20)) (= var11 var19)) (= var10 var18)) (= var9 var17))) (and (and (and (and (and (and (and (= var8 (write var16 var13 defObj)) (= var7 var15)) (= var6 var14)) (= var5 var13)) (= var4 var12)) (= var3 var11)) (= var2 var10)) (= var1 var9))) (= var0 (+ var4 1))))) (inv_main614_3 var8 var7 var6 var2 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Int) (var5 Int) (var6 Heap) (var7 Addr) (var8 Int) (var9 Int) (var10 Addr) (var11 Int) (var12 Int) (var13 Heap) (var14 Int) (var15 Int) (var16 Int) (var17 Int) (var18 Heap) (var19 Addr) (var20 Addr) (var21 Int) (var22 Addr) (var23 Int) (var24 Int) (var25 Heap)) (or (not (and (inv_main614_3 var25 var24 var23 var22 var21) (and (and (and (and (and (= var20 var19) (and (and (and (and (and (and (= var18 var25) (= var17 var24)) (= var16 var23)) (= var19 var22)) (= var15 var21)) (= var14 3)) (= var20 (|node::next| (getnode (read var25 var22)))))) (and (and (and (and (and (and (= var13 (write var18 var19 defObj)) (= var12 var17)) (= var11 var16)) (= var10 var19)) (= var9 var15)) (= var8 var14)) (= var7 var20))) (and (and (and (and (and (= var6 var13) (= var5 var12)) (= var4 var11)) (= var3 nullAddr)) (= var2 var9)) (= var1 var8))) (<= 0 (+ (+ var24 (* (- 1) var21)) (- 1)))) (= var0 (+ var2 1))))) (inv_main614_3 var6 var5 var4 var3 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Int) (var11 Int) (var12 Int) (var13 Int) (var14 Heap)) (or (not (and (inv_main585_3 var14 var13 var12 var11 var10 var9 var8) (and (and (not (<= 0 (+ (+ var11 (- 1)) (- 1)))) (and (and (and (and (and (and (= var7 (write var14 var8 (O_node (node var9 (|node::data| (getnode (read var14 var8))))))) (= var6 var13)) (= var5 var12)) (= var4 var11)) (= var3 var10)) (= var2 var9)) (= var1 var8))) (= var0 0)))) (inv_main614_3 var7 var6 var5 var2 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Heap)) (or (not (and (inv_main614_3 var4 var3 var2 var1 var0) (and (not (= nullAddr var1)) (not (<= 0 (+ (+ var3 (* (- 1) var0)) (- 1))))))) (inv_main_30 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Heap)) (not (inv_main_30 var4 var3 var2 var1 var0))))
(check-sat)
