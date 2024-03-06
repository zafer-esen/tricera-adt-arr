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
(declare-fun inv_main596_3 (Heap Int Int Addr Int Int Addr) Bool)
(declare-fun inv_main600_21 (Heap Int Int Addr Int Int Addr) Bool)
(declare-fun inv_main604_5 (Heap Int Int Addr Int Int Addr Addr) Bool)
(declare-fun inv_main615_3 (Heap Int Int) Bool)
(declare-fun inv_main_26 (Heap Int Int Addr Int Int Addr Addr) Bool)
(assert (forall ((var0 Int) (var1 Int) (var2 Heap)) (or (not (and (and (= var2 emptyHeap) (= var1 2)) (= var0 1))) (inv_main615_3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Addr) (var4 Int) (var5 Int) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Int) (var12 Int) (var13 Addr) (var14 Int) (var15 Int) (var16 Heap)) (or (not (and (inv_main604_5 var16 var15 var14 var13 var12 var11 var10 var9) (and (= var8 var7) (and (and (and (and (and (and (and (and (= var6 var16) (= var5 var15)) (= var4 var14)) (= var3 var13)) (= var2 var12)) (= var1 var11)) (= var7 var10)) (= var0 var9)) (= var8 (|node::next| (getnode (read var16 var9)))))))) (inv_main_26 var6 var5 var4 var3 var2 var1 var7 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Heap)) (or (not (inv_main577_5 var7 var6 var5 var4 var3 var2 var1 var0)) (inv_main577_5 var7 var6 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 node) (var7 Heap) (var8 Addr) (var9 Int) (var10 Int) (var11 Heap)) (or (not (and (inv_main615_3 var11 var10 var9) (and (and (= nullAddr var8) (and (and (and (and (and (and (= var7 (newHeap (alloc var11 (O_node var6)))) (= var5 var10)) (= var4 var9)) (= var3 var10)) (= var2 var9)) (= var1 var9)) (= var8 (newAddr (alloc var11 (O_node var6)))))) (= var0 1)))) (inv_main577_5 var7 var5 var4 var3 var2 var1 var8 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Int) (var6 Int) (var7 Int) (var8 Heap) (var9 node) (var10 Addr) (var11 Int) (var12 Addr) (var13 Addr) (var14 Int) (var15 Int) (var16 Int) (var17 Int) (var18 Heap) (var19 Addr) (var20 Int) (var21 Int) (var22 Addr) (var23 Addr) (var24 Addr) (var25 Addr) (var26 Int) (var27 Int) (var28 Int) (var29 Int) (var30 Int) (var31 Int) (var32 Int) (var33 Int) (var34 Addr) (var35 Heap) (var36 Heap) (var37 Addr) (var38 Addr) (var39 Int) (var40 Int) (var41 Int) (var42 Int) (var43 Heap)) (or (not (and (inv_main585_3 var43 var42 var41 var40 var39 var38 var37) (and (and (and (and (and (and (and (and (and (and (and (and (and (= var36 (write var35 var34 (O_node (node nullAddr (|node::data| (getnode (read var35 var34))))))) (= var33 var32)) (= var31 var30)) (= var29 var28)) (= var27 var26)) (= var25 var24)) (= var23 var22)) (= var21 var20)) (= var19 var34)) (and (and (and (and (and (and (and (and (= var18 (write var36 var19 (O_node (node (|node::next| (getnode (read var36 var19))) var21)))) (= var17 var33)) (= var16 var31)) (= var15 var29)) (= var14 var27)) (= var13 var25)) (= var12 var23)) (= var11 var21)) (= var10 var19))) (and (not (= nullAddr var34)) (and (and (and (and (and (and (and (and (= var35 (newHeap (alloc var43 (O_node var9)))) (= var32 var42)) (= var30 var41)) (= var28 var40)) (= var26 var39)) (= var24 var38)) (= var22 var37)) (= var20 var39)) (= var34 (newAddr (alloc var43 (O_node var9))))))) (and (and (and (and (and (and (and (= var8 (write var18 var10 (O_node (node var13 (|node::data| (getnode (read var18 var10))))))) (= var7 var17)) (= var6 var16)) (= var5 var15)) (= var4 var14)) (= var3 var13)) (= var2 var12)) (= var1 var10))) (<= 0 (+ (+ var40 (- 1)) (- 1)))) (= var0 (+ var5 (- 1)))))) (inv_main585_3 var8 var7 var6 var0 var4 var1 var2))))
(assert (forall ((var0 node) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Heap) (var8 Addr) (var9 Int) (var10 Int) (var11 Int) (var12 Int) (var13 Int) (var14 Int) (var15 Int) (var16 Int) (var17 Int) (var18 Int) (var19 Addr) (var20 Heap) (var21 Heap) (var22 Int) (var23 Int) (var24 Heap)) (or (not (and (inv_main615_3 var24 var23 var22) (and (and (and (and (and (and (and (and (= var21 (write var20 var19 (O_node (node nullAddr (|node::data| (getnode (read var20 var19))))))) (= var18 var17)) (= var16 var15)) (= var14 var13)) (= var12 var11)) (= var10 var9)) (= var8 var19)) (and (and (and (and (and (and (= var7 (write var21 var8 (O_node (node (|node::next| (getnode (read var21 var8))) var10)))) (= var6 var18)) (= var5 var16)) (= var4 var14)) (= var3 var12)) (= var2 var10)) (= var1 var8))) (and (not (= nullAddr var19)) (and (and (and (and (and (and (= var20 (newHeap (alloc var24 (O_node var0)))) (= var17 var23)) (= var15 var22)) (= var13 var23)) (= var11 var22)) (= var9 var22)) (= var19 (newAddr (alloc var24 (O_node var0))))))))) (inv_main585_3 var7 var6 var5 var4 var3 var1 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Int) (var6 Int) (var7 Int) (var8 Addr) (var9 Addr) (var10 Int) (var11 Int) (var12 Int) (var13 Int) (var14 Heap) (var15 Heap) (var16 Addr) (var17 Int) (var18 Int) (var19 Addr) (var20 Int) (var21 Int) (var22 Heap)) (or (not (and (inv_main596_3 var22 var21 var20 var19 var18 var17 var16) (and (and (and (and (and (and (and (and (= var15 var14) (= var13 var12)) (= var11 var10)) (= var9 var8)) (= var7 var6)) (= var5 var4)) (= var3 var2)) (= var1 (|node::next| (getnode (read var14 var2))))) (and (not (= var0 var8)) (and (and (and (and (and (and (and (= var14 var22) (= var12 var21)) (= var10 var20)) (= var8 var19)) (= var6 var18)) (= var4 var17)) (= var2 var16)) (= var0 (|node::next| (getnode (read var22 var16))))))))) (inv_main596_3 var15 var13 var11 var9 var7 var5 var1))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Int) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Int) (var9 Int) (var10 Addr) (var11 Int) (var12 Int) (var13 Heap) (var14 Int) (var15 Int) (var16 Addr) (var17 Addr) (var18 Int) (var19 Int) (var20 Addr) (var21 Int) (var22 Int) (var23 Heap)) (or (not (and (inv_main_26 var23 var22 var21 var20 var19 var18 var17 var16) (and (and (and (<= 0 (+ (+ var15 (* (- 1) (+ var14 1))) (- 1))) (and (and (and (and (and (and (and (and (= var13 (write var23 var17 defObj)) (= var12 var22)) (= var11 var21)) (= var10 var20)) (= var9 var19)) (= var8 var18)) (= var7 var17)) (= var6 var16)) (and (and (and (and (and (= var5 (write var13 var6 (O_node (node var10 (|node::data| (getnode (read var13 var6))))))) (= var15 var12)) (= var4 var11)) (= var3 var10)) (= var14 var9)) (= var2 var8)))) (= var1 (+ var14 1))) (= var0 3)))) (inv_main596_3 var5 var15 var4 var3 var1 var0 var3))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Int) (var5 Heap) (var6 Addr) (var7 Int) (var8 Int) (var9 Addr) (var10 Int) (var11 Int) (var12 Heap) (var13 Int) (var14 Int) (var15 Addr) (var16 Int) (var17 Int) (var18 Addr) (var19 Int) (var20 Int) (var21 Heap)) (or (not (and (inv_main600_21 var21 var20 var19 var18 var17 var16 var15) (and (and (and (<= 0 (+ (+ var14 (* (- 1) (+ var13 1))) (- 1))) (and (and (and (and (and (and (and (= var12 (write var21 var18 defObj)) (= var11 var20)) (= var10 var19)) (= var9 var18)) (= var8 var17)) (= var7 var16)) (= var6 var15)) (and (and (and (and (and (= var5 var12) (= var14 var11)) (= var4 var10)) (= var3 nullAddr)) (= var13 var8)) (= var2 var7)))) (= var1 (+ var13 1))) (= var0 3)))) (inv_main596_3 var5 var14 var4 var3 var1 var0 var3))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Int) (var5 Int) (var6 Int) (var7 Heap) (var8 Int) (var9 Addr) (var10 Addr) (var11 Int) (var12 Int) (var13 Int) (var14 Int) (var15 Heap)) (or (not (and (inv_main585_3 var15 var14 var13 var12 var11 var10 var9) (and (and (and (<= 0 (+ var8 (- 1))) (and (not (<= 0 (+ (+ var12 (- 1)) (- 1)))) (and (and (and (and (and (and (= var7 (write var15 var9 (O_node (node var10 (|node::data| (getnode (read var15 var9))))))) (= var8 var14)) (= var6 var13)) (= var5 var12)) (= var4 var11)) (= var3 var10)) (= var2 var9)))) (= var1 0)) (= var0 3)))) (inv_main596_3 var7 var8 var6 var3 var1 var0 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Int) (var7 Int) (var8 Int) (var9 Int) (var10 Addr) (var11 Addr) (var12 Int) (var13 Int) (var14 Int) (var15 Int) (var16 Heap) (var17 Heap) (var18 Addr) (var19 Addr) (var20 Int) (var21 Int) (var22 Addr) (var23 Int) (var24 Int) (var25 Heap)) (or (not (and (inv_main604_5 var25 var24 var23 var22 var21 var20 var19 var18) (and (and (and (and (and (and (and (and (and (= var17 var16) (= var15 var14)) (= var13 var12)) (= var11 var10)) (= var9 var8)) (= var7 var6)) (= var5 var4)) (= var3 var2)) (= var1 (|node::next| (getnode (read var16 var2))))) (and (not (= var0 var4)) (and (and (and (and (and (and (and (and (= var16 var25) (= var14 var24)) (= var12 var23)) (= var10 var22)) (= var8 var21)) (= var6 var20)) (= var4 var19)) (= var2 var18)) (= var0 (|node::next| (getnode (read var25 var18))))))))) (inv_main604_5 var17 var15 var13 var11 var9 var7 var5 var1))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Int) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Int) (var10 Int) (var11 Addr) (var12 Int) (var13 Int) (var14 Heap)) (or (not (and (inv_main596_3 var14 var13 var12 var11 var10 var9 var8) (and (not (= var7 var6)) (and (= var5 var6) (and (and (and (and (and (and (and (= var4 var14) (= var3 var13)) (= var2 var12)) (= var6 var11)) (= var1 var10)) (= var0 var9)) (= var7 var8)) (= var5 (|node::next| (getnode (read var14 var8))))))))) (inv_main604_5 var4 var3 var2 var6 var1 var0 var7 var6))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Int) (var6 Int) (var7 Int) (var8 Int) (var9 Heap)) (or (not (inv_main577_5_11 var9 var8 var7 var6 var5 var4 var3 var2 var1 var0)) (inv_main577_5_11 var9 var8 var7 var6 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Int) (var5 Int) (var6 Int) (var7 Int) (var8 node) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Int) (var14 Int) (var15 Int) (var16 Int) (var17 Heap)) (or (not (and (inv_main585_3 var17 var16 var15 var14 var13 var12 var11) (and (and (and (= nullAddr var10) (and (and (and (and (and (and (and (and (= var9 (newHeap (alloc var17 (O_node var8)))) (= var7 var16)) (= var6 var15)) (= var5 var14)) (= var4 var13)) (= var3 var12)) (= var2 var11)) (= var1 var13)) (= var10 (newAddr (alloc var17 (O_node var8)))))) (<= 0 (+ (+ var14 (- 1)) (- 1)))) (= var0 1)))) (inv_main577_5_11 var9 var7 var6 var5 var4 var3 var2 var1 var10 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Int) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Int) (var10 Int) (var11 Addr) (var12 Int) (var13 Int) (var14 Heap)) (or (not (and (inv_main596_3 var14 var13 var12 var11 var10 var9 var8) (and (= var7 var6) (and (= var5 var6) (and (and (and (and (and (and (and (= var4 var14) (= var3 var13)) (= var2 var12)) (= var6 var11)) (= var1 var10)) (= var0 var9)) (= var7 var8)) (= var5 (|node::next| (getnode (read var14 var8))))))))) (inv_main600_21 var4 var3 var2 var6 var1 var0 var7))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Addr) (var4 Int) (var5 Int) (var6 Heap)) (not (and (inv_main600_21 var6 var5 var4 var3 var2 var1 var0) (and (not (= var3 nullAddr)) (= (read var6 var3) defObj))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Addr) (var5 Int) (var6 Int) (var7 Heap)) (not (and (inv_main_26 var7 var6 var5 var4 var3 var2 var1 var0) (and (not (= var1 nullAddr)) (= (read var7 var1) defObj))))))
(check-sat)
