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
   (node (|node::h| Int) (|node::n| Addr))
  )
))
(declare-fun inv_exit (Heap Addr) Bool)
(declare-fun inv_main534_3 (Heap Addr Int Int) Bool)
(declare-fun inv_main535_15 (Heap Addr Int Int Addr Int) Bool)
(declare-fun inv_main537_3 (Heap Addr Int Int Addr Addr Addr) Bool)
(declare-fun inv_main542_17 (Heap Addr Int Int Addr Addr Addr Int) Bool)
(declare-fun inv_main550_17 (Heap Addr Int Int Addr Addr Addr Int) Bool)
(declare-fun inv_main576_10 (Heap Addr Int) Bool)
(declare-fun inv_main_27 (Heap Addr Int Int Addr Addr Addr) Bool)
(declare-fun inv_main_28 (Heap Addr Int Int Addr Addr Addr) Bool)
(declare-fun inv_main_3 (Heap Addr Int Int Addr Addr Addr) Bool)
(declare-fun inv_main_38 (Heap Addr Int Int Addr Addr Addr) Bool)
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Heap)) (or (not (and (and (and (= var3 emptyHeap) (= var2 nullAddr)) (= var1 0)) (= var0 0))) (inv_main534_3 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Int) (var6 Addr) (var7 Heap)) (or (not (inv_main542_17 var7 var6 var5 var4 var3 var2 var1 var0)) (inv_main542_17 var7 var6 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Int) (var9 Int) (var10 Int) (var11 Int) (var12 Addr) (var13 Bool) (var14 Addr) (var15 node) (var16 Heap) (var17 Heap) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Int) (var23 Int) (var24 Addr) (var25 Heap)) (or (not (and (inv_main537_3 var25 var24 var23 var22 var21 var20 var19) (and (and (= var18 nullAddr) (and (and (and (and (and (and (and (and (and (= var17 (newHeap (alloc var16 (O_node var15)))) (or (and var13 (= var14 (newAddr (alloc var16 (O_node var15))))) (and (not var13) (= var14 var12)))) (= var11 var10)) (= var9 var8)) (= var7 var6)) (= var5 var4)) (= var3 var2)) (= var18 (newAddr (alloc var16 (O_node var15))))) (and (not (= var1 0)) (<= 0 (+ (+ 10 (* (- 1) var23)) (- 1))))) (and (and (and (and (and (and (= var16 (write var25 var19 (O_node (node 1 (|node::n| (getnode (read var25 var19))))))) (= var12 var24)) (= var10 (+ var23 1))) (= var8 var22)) (= var6 var21)) (= var4 var20)) (= var2 var19)))) (= var0 1)))) (inv_main542_17 var17 var14 var11 var9 var7 var18 var3 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Int) (var6 Int) (var7 Addr) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Int) (var13 Int) (var14 Addr) (var15 Heap) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Int) (var20 Int) (var21 Addr) (var22 Heap)) (or (not (and (inv_main_3 var22 var21 var20 var19 var18 var17 var16) (and (and (and (and (not (<= 0 (+ (+ 10 (* (- 1) var19)) (- 1)))) (and (and (and (and (and (and (= var15 (write var22 var16 (O_node (node 3 (|node::n| (getnode (read var22 var16))))))) (= var14 var21)) (= var13 var20)) (= var12 var19)) (= var11 var18)) (= var10 var17)) (= var9 var16))) (and (and (and (and (and (and (= var8 (write var15 var9 (O_node (node (|node::h| (getnode (read var15 var9))) 0)))) (= var7 var14)) (= var6 var13)) (= var5 var12)) (= var4 var11)) (= var3 var10)) (= var2 var9))) (= var1 0)) (= var0 0)))) (inv_main_27 var8 var7 var1 var0 var4 var3 var4))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Int) (var6 Int) (var7 Addr) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Int) (var13 Int) (var14 Addr) (var15 Heap) (var16 Int) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Int) (var21 Int) (var22 Addr) (var23 Heap)) (or (not (and (inv_main_3 var23 var22 var21 var20 var19 var18 var17) (and (and (and (and (and (= var16 0) (<= 0 (+ (+ 10 (* (- 1) var20)) (- 1)))) (and (and (and (and (and (and (= var15 (write var23 var17 (O_node (node 3 (|node::n| (getnode (read var23 var17))))))) (= var14 var22)) (= var13 var21)) (= var12 var20)) (= var11 var19)) (= var10 var18)) (= var9 var17))) (and (and (and (and (and (and (= var8 (write var15 var9 (O_node (node (|node::h| (getnode (read var15 var9))) 0)))) (= var7 var14)) (= var6 var13)) (= var5 var12)) (= var4 var11)) (= var3 var10)) (= var2 var9))) (= var1 0)) (= var0 0)))) (inv_main_27 var8 var7 var1 var0 var4 var3 var4))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Int) (var9 Int) (var10 Int) (var11 Int) (var12 Addr) (var13 Addr) (var14 Heap) (var15 Heap) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Int) (var20 Int) (var21 Addr) (var22 Heap)) (or (not (and (inv_main_27 var22 var21 var20 var19 var18 var17 var16) (and (and (and (and (and (and (and (and (= var15 var14) (= var13 var12)) (= var11 (+ var10 1))) (= var9 var8)) (= var7 var6)) (= var5 var4)) (= var3 var2)) (= var1 (|node::n| (getnode (read var14 var2))))) (and (= var0 1) (and (and (and (and (and (and (and (= var14 var22) (= var12 var21)) (= var10 var20)) (= var8 var19)) (= var6 var18)) (= var4 var17)) (= var2 var16)) (= var0 (|node::h| (getnode (read var22 var16))))))))) (inv_main_27 var15 var13 var11 var9 var7 var5 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Int) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Int) (var12 Int) (var13 Addr) (var14 Heap) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Int) (var20 Int) (var21 Addr) (var22 Heap)) (or (not (and (inv_main_38 var22 var21 var20 var19 var18 var17 var16) (and (and (and (= var15 nullAddr) (and (and (and (and (and (and (and (= var14 var22) (= var13 var21)) (= var12 var20)) (= var11 var19)) (= var10 var18)) (= var9 var17)) (= var8 var16)) (= var15 (|node::n| (getnode (read var22 var16)))))) (and (and (and (and (and (and (= var7 (write var14 var8 defObj)) (or (and (= var13 var8) (= var6 nullAddr)) (and (not (= var13 var8)) (= var6 var13)))) (= var5 var12)) (= var4 var11)) (= var3 var10)) (= var2 var9)) (= var1 var8))) (= var0 0)))) (inv_main576_10 var7 var6 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Int) (var6 Int) (var7 Addr) (var8 Bool) (var9 node) (var10 Heap) (var11 Addr) (var12 Int) (var13 Int) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Heap) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Addr) (var25 Int) (var26 Int) (var27 Int) (var28 Int) (var29 Addr) (var30 Addr) (var31 Heap) (var32 Heap) (var33 Addr) (var34 Addr) (var35 Addr) (var36 Int) (var37 Int) (var38 Addr) (var39 Heap)) (or (not (and (inv_main537_3 var39 var38 var37 var36 var35 var34 var33) (and (and (and (and (and (and (and (and (and (= var32 var31) (= var30 var29)) (= var28 var27)) (= var26 var25)) (= var24 var23)) (= var22 var21)) (= var20 var19)) (= var18 (|node::n| (getnode (read var31 var19))))) (and (and (and (and (and (and (= var31 (write var17 var16 (O_node (node (|node::h| (getnode (read var17 var16))) var15)))) (= var29 var14)) (= var27 var13)) (= var25 var12)) (= var23 var11)) (= var21 var15)) (= var19 var16))) (and (not (= var15 nullAddr)) (and (and (and (and (and (and (and (and (and (= var17 (newHeap (alloc var10 (O_node var9)))) (or (and var8 (= var14 (newAddr (alloc var10 (O_node var9))))) (and (not var8) (= var14 var7)))) (= var13 var6)) (= var12 var5)) (= var11 var4)) (= var3 var2)) (= var16 var1)) (= var15 (newAddr (alloc var10 (O_node var9))))) (and (not (= var0 0)) (<= 0 (+ (+ 10 (* (- 1) var37)) (- 1))))) (and (and (and (and (and (and (= var10 (write var39 var33 (O_node (node 1 (|node::n| (getnode (read var39 var33))))))) (= var7 var38)) (= var6 (+ var37 1))) (= var5 var36)) (= var4 var35)) (= var2 var34)) (= var1 var33))))))) (inv_main537_3 var32 var30 var28 var26 var24 var22 var18))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Bool) (var4 Addr) (var5 node) (var6 Heap) (var7 Addr) (var8 Int) (var9 Int) (var10 Addr) (var11 Heap)) (or (not (and (inv_main534_3 var11 var10 var9 var8) (and (not (= var7 nullAddr)) (and (and (and (and (= var6 (newHeap (alloc var11 (O_node var5)))) (or (and var3 (= var4 (newAddr (alloc var11 (O_node var5))))) (and (not var3) (= var4 var10)))) (= var2 var9)) (= var1 var8)) (= var7 (newAddr (alloc var11 (O_node var5)))))))) (inv_main537_3 var6 var4 var2 var1 var7 var0 var7))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Int) (var8 Int) (var9 Addr) (var10 Addr) (var11 Heap) (var12 Heap) (var13 Int) (var14 Int) (var15 Int) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Int) (var20 Int) (var21 Addr) (var22 Heap)) (or (not (and (inv_main_28 var22 var21 var20 var19 var18 var17 var16) (and (and (or (not (= var15 3)) (<= 0 (+ (+ 20 (* (- 1) (+ var14 var13))) (- 1)))) (and (and (and (and (and (and (and (= var12 var11) (= var10 var9)) (= var14 var8)) (= var13 var7)) (= var6 var5)) (= var4 var3)) (= var2 var1)) (= var15 (|node::h| (getnode (read var11 var1)))))) (and (not (= var0 2)) (and (and (and (and (and (and (and (= var11 var22) (= var9 var21)) (= var8 var20)) (= var7 var19)) (= var5 var18)) (= var3 var17)) (= var1 var16)) (= var0 (|node::h| (getnode (read var22 var16))))))))) (inv_exit var12 var10))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Addr) (var6 Heap)) (or (not (and (inv_main537_3 var6 var5 var4 var3 var2 var1 var0) (not (<= 0 (+ (+ 10 (* (- 1) var4)) (- 1)))))) (inv_main_3 var6 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Int) (var6 Addr) (var7 Heap)) (or (not (and (inv_main537_3 var7 var6 var5 var4 var3 var2 var1) (and (= var0 0) (<= 0 (+ (+ 10 (* (- 1) var5)) (- 1)))))) (inv_main_3 var7 var6 var5 var4 var3 var2 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Int) (var6 Int) (var7 Addr) (var8 Bool) (var9 node) (var10 Heap) (var11 Addr) (var12 Int) (var13 Int) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Heap) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Addr) (var25 Int) (var26 Int) (var27 Int) (var28 Int) (var29 Addr) (var30 Addr) (var31 Heap) (var32 Heap) (var33 Addr) (var34 Addr) (var35 Addr) (var36 Int) (var37 Int) (var38 Addr) (var39 Heap)) (or (not (and (inv_main_3 var39 var38 var37 var36 var35 var34 var33) (and (and (and (and (and (and (and (and (and (= var32 var31) (= var30 var29)) (= var28 var27)) (= var26 var25)) (= var24 var23)) (= var22 var21)) (= var20 var19)) (= var18 (|node::n| (getnode (read var31 var19))))) (and (and (and (and (and (and (= var31 (write var17 var16 (O_node (node (|node::h| (getnode (read var17 var16))) var15)))) (= var29 var14)) (= var27 var13)) (= var25 var12)) (= var23 var11)) (= var21 var15)) (= var19 var16))) (and (not (= var15 nullAddr)) (and (and (and (and (and (and (and (and (and (= var17 (newHeap (alloc var10 (O_node var9)))) (or (and var8 (= var14 (newAddr (alloc var10 (O_node var9))))) (and (not var8) (= var14 var7)))) (= var13 var6)) (= var12 var5)) (= var11 var4)) (= var3 var2)) (= var16 var1)) (= var15 (newAddr (alloc var10 (O_node var9))))) (and (not (= var0 0)) (<= 0 (+ (+ 10 (* (- 1) var36)) (- 1))))) (and (and (and (and (and (and (= var10 (write var39 var33 (O_node (node 2 (|node::n| (getnode (read var39 var33))))))) (= var7 var38)) (= var6 var37)) (= var5 (+ var36 1))) (= var4 var35)) (= var2 var34)) (= var1 var33))))))) (inv_main_3 var32 var30 var28 var26 var24 var22 var18))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Addr) (var5 Heap)) (or (not (inv_main535_15 var5 var4 var3 var2 var1 var0)) (inv_main535_15 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Bool) (var4 Addr) (var5 node) (var6 Heap) (var7 Addr) (var8 Int) (var9 Int) (var10 Addr) (var11 Heap)) (or (not (and (inv_main534_3 var11 var10 var9 var8) (and (and (= var7 nullAddr) (and (and (and (and (= var6 (newHeap (alloc var11 (O_node var5)))) (or (and var3 (= var4 (newAddr (alloc var11 (O_node var5))))) (and (not var3) (= var4 var10)))) (= var2 var9)) (= var1 var8)) (= var7 (newAddr (alloc var11 (O_node var5)))))) (= var0 1)))) (inv_main535_15 var6 var4 var2 var1 var7 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Int) (var8 Int) (var9 Addr) (var10 Addr) (var11 Heap) (var12 Heap) (var13 Int) (var14 Int) (var15 Int) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Int) (var20 Int) (var21 Addr) (var22 Heap)) (or (not (and (inv_main_28 var22 var21 var20 var19 var18 var17 var16) (and (and (and (= var15 3) (not (<= 0 (+ (+ 20 (* (- 1) (+ var14 var13))) (- 1))))) (and (and (and (and (and (and (and (= var12 var11) (= var10 var9)) (= var14 var8)) (= var13 var7)) (= var6 var5)) (= var4 var3)) (= var2 var1)) (= var15 (|node::h| (getnode (read var11 var1)))))) (and (not (= var0 2)) (and (and (and (and (and (and (and (= var11 var22) (= var9 var21)) (= var8 var20)) (= var7 var19)) (= var5 var18)) (= var3 var17)) (= var1 var16)) (= var0 (|node::h| (getnode (read var22 var16))))))))) (inv_main_38 var12 var10 var14 var13 var6 var4 var6))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Int) (var16 Int) (var17 Int) (var18 Int) (var19 Addr) (var20 Addr) (var21 Heap) (var22 Heap) (var23 Addr) (var24 Addr) (var25 Addr) (var26 Int) (var27 Int) (var28 Addr) (var29 Heap)) (or (not (and (inv_main_38 var29 var28 var27 var26 var25 var24 var23) (and (and (and (and (and (and (and (and (and (= var22 var21) (= var20 var19)) (= var18 var17)) (= var16 var15)) (= var14 var13)) (= var12 var11)) (= var10 var9)) (= var8 (|node::n| (getnode (read var21 var9))))) (and (not (= var7 nullAddr)) (and (and (and (and (and (and (and (= var21 var29) (= var19 var28)) (= var17 var27)) (= var15 var26)) (= var13 var25)) (= var11 var24)) (= var9 var23)) (= var7 (|node::n| (getnode (read var29 var23))))))) (and (and (and (and (and (and (= var6 (write var22 var10 defObj)) (or (and (= var20 var10) (= var5 nullAddr)) (and (not (= var20 var10)) (= var5 var20)))) (= var4 var18)) (= var3 var16)) (= var2 var14)) (= var1 var8)) (= var0 var10))))) (inv_main_38 var6 var5 var4 var3 var2 var1 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Addr) (var6 Heap) (var7 Int) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Int) (var12 Int) (var13 Addr) (var14 Heap)) (or (not (and (inv_main_27 var14 var13 var12 var11 var10 var9 var8) (and (not (= var7 1)) (and (and (and (and (and (and (and (= var6 var14) (= var5 var13)) (= var4 var12)) (= var3 var11)) (= var2 var10)) (= var1 var9)) (= var0 var8)) (= var7 (|node::h| (getnode (read var14 var8)))))))) (inv_main_28 var6 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Int) (var9 Int) (var10 Int) (var11 Int) (var12 Addr) (var13 Addr) (var14 Heap) (var15 Heap) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Int) (var20 Int) (var21 Addr) (var22 Heap)) (or (not (and (inv_main_28 var22 var21 var20 var19 var18 var17 var16) (and (and (and (and (and (and (and (and (= var15 var14) (= var13 var12)) (= var11 var10)) (= var9 (+ var8 1))) (= var7 var6)) (= var5 var4)) (= var3 var2)) (= var1 (|node::n| (getnode (read var14 var2))))) (and (= var0 2) (and (and (and (and (and (and (and (= var14 var22) (= var12 var21)) (= var10 var20)) (= var8 var19)) (= var6 var18)) (= var4 var17)) (= var2 var16)) (= var0 (|node::h| (getnode (read var22 var16))))))))) (inv_main_28 var15 var13 var11 var9 var7 var5 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Int) (var6 Addr) (var7 Heap)) (or (not (inv_main550_17 var7 var6 var5 var4 var3 var2 var1 var0)) (inv_main550_17 var7 var6 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Int) (var9 Int) (var10 Int) (var11 Int) (var12 Addr) (var13 Bool) (var14 Addr) (var15 node) (var16 Heap) (var17 Heap) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Int) (var23 Int) (var24 Addr) (var25 Heap)) (or (not (and (inv_main_3 var25 var24 var23 var22 var21 var20 var19) (and (and (= var18 nullAddr) (and (and (and (and (and (and (and (and (and (= var17 (newHeap (alloc var16 (O_node var15)))) (or (and var13 (= var14 (newAddr (alloc var16 (O_node var15))))) (and (not var13) (= var14 var12)))) (= var11 var10)) (= var9 var8)) (= var7 var6)) (= var5 var4)) (= var3 var2)) (= var18 (newAddr (alloc var16 (O_node var15))))) (and (not (= var1 0)) (<= 0 (+ (+ 10 (* (- 1) var22)) (- 1))))) (and (and (and (and (and (and (= var16 (write var25 var19 (O_node (node 2 (|node::n| (getnode (read var25 var19))))))) (= var12 var24)) (= var10 var23)) (= var8 (+ var22 1))) (= var6 var21)) (= var4 var20)) (= var2 var19)))) (= var0 1)))) (inv_main550_17 var17 var14 var11 var9 var7 var18 var3 var0))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_exit var1 var0) (not (= var0 nullAddr))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap)) (not (and (inv_main576_10 var2 var1 var0) (not (= var1 nullAddr))))))
(check-sat)
