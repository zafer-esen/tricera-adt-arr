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
   (node (|node::h| Int) (|node::flag| Int) (|node::n| Addr))
  )
))
(declare-fun inv_exit (Heap Addr) Bool)
(declare-fun inv_main-1_-1 (Heap Addr Int) Bool)
(declare-fun inv_main534_3 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main535_15 (Heap Addr Addr Addr Addr Int) Bool)
(declare-fun inv_main537_3 (Heap Addr Addr Addr Addr Int) Bool)
(declare-fun inv_main547_17 (Heap Addr Addr Addr Addr Int Int) Bool)
(declare-fun inv_main_19 (Heap Addr Addr Addr Addr Int) Bool)
(declare-fun inv_main_31 (Heap Addr Addr Addr Addr Int) Bool)
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (= var4 emptyHeap) (= var3 nullAddr))) (inv_main534_3 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (inv_main547_17 var6 var5 var4 var3 var2 var1 var0)) (inv_main547_17 var6 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Int) (var6 Int) (var7 Addr) (var8 Heap) (var9 Int) (var10 Int) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Bool) (var19 Addr) (var20 node) (var21 Heap) (var22 Heap) (var23 Addr) (var24 Int) (var25 Addr) (var26 Addr) (var27 Addr) (var28 Addr) (var29 Heap)) (or (not (and (inv_main537_3 var29 var28 var27 var26 var25 var24) (and (and (and (and (= var23 nullAddr) (and (and (and (and (and (and (= var22 (newHeap (alloc var21 (O_node var20)))) (or (and var18 (= var19 (newAddr (alloc var21 (O_node var20))))) (and (not var18) (= var19 var17)))) (= var16 var15)) (= var14 var13)) (= var12 var11)) (= var10 var9)) (= var23 (newAddr (alloc var21 (O_node var20)))))) (and (and (not (= (|node::flag| (getnode (read var8 var7))) 0)) (and (not (= var6 0)) (<= 0 (+ (+ 20 (* (- 1) var24)) (- 1))))) (and (and (and (and (and (= var8 (write var29 var27 (O_node (node (|node::h| (getnode (read var29 var27))) var5 (|node::n| (getnode (read var29 var27))))))) (= var4 var28)) (= var7 var27)) (= var3 var26)) (= var2 var25)) (= var1 (+ var24 1))))) (and (and (and (and (and (= var21 (write var8 var7 (O_node (node 1 (|node::flag| (getnode (read var8 var7))) (|node::n| (getnode (read var8 var7))))))) (= var17 var4)) (= var15 var7)) (= var13 var3)) (= var11 var2)) (= var9 var1))) (= var0 1)))) (inv_main547_17 var22 var19 var16 var14 var23 var10 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Int) (var6 Int) (var7 Addr) (var8 Heap) (var9 Int) (var10 Int) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Bool) (var19 Addr) (var20 node) (var21 Heap) (var22 Heap) (var23 Addr) (var24 Int) (var25 Addr) (var26 Addr) (var27 Addr) (var28 Addr) (var29 Heap)) (or (not (and (inv_main537_3 var29 var28 var27 var26 var25 var24) (and (and (and (and (= var23 nullAddr) (and (and (and (and (and (and (= var22 (newHeap (alloc var21 (O_node var20)))) (or (and var18 (= var19 (newAddr (alloc var21 (O_node var20))))) (and (not var18) (= var19 var17)))) (= var16 var15)) (= var14 var13)) (= var12 var11)) (= var10 var9)) (= var23 (newAddr (alloc var21 (O_node var20)))))) (and (and (= (|node::flag| (getnode (read var8 var7))) 0) (and (not (= var6 0)) (<= 0 (+ (+ 20 (* (- 1) var24)) (- 1))))) (and (and (and (and (and (= var8 (write var29 var27 (O_node (node (|node::h| (getnode (read var29 var27))) var5 (|node::n| (getnode (read var29 var27))))))) (= var4 var28)) (= var7 var27)) (= var3 var26)) (= var2 var25)) (= var1 (+ var24 1))))) (and (and (and (and (and (= var21 (write var8 var7 (O_node (node 2 (|node::flag| (getnode (read var8 var7))) (|node::n| (getnode (read var8 var7))))))) (= var17 var4)) (= var15 var7)) (= var13 var3)) (= var11 var2)) (= var9 var1))) (= var0 1)))) (inv_main547_17 var22 var19 var16 var14 var23 var10 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Int) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Heap) (var13 Int) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Heap)) (or (not (and (inv_main537_3 var18 var17 var16 var15 var14 var13) (and (and (and (not (<= 0 (+ (+ 20 (* (- 1) var13)) (- 1)))) (and (and (and (and (and (= var12 (write var18 var16 (O_node (node 3 (|node::flag| (getnode (read var18 var16))) (|node::n| (getnode (read var18 var16))))))) (= var11 var17)) (= var10 var16)) (= var9 var15)) (= var8 var14)) (= var7 var13))) (and (and (and (and (and (= var6 (write var12 var10 (O_node (node (|node::h| (getnode (read var12 var10))) (|node::flag| (getnode (read var12 var10))) 0)))) (= var5 var11)) (= var4 var10)) (= var3 var9)) (= var2 var8)) (= var1 var7))) (= var0 0)))) (inv_main_19 var6 var5 var3 var3 var2 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Int) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Heap) (var13 Int) (var14 Int) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Heap)) (or (not (and (inv_main537_3 var19 var18 var17 var16 var15 var14) (and (and (and (and (= var13 0) (<= 0 (+ (+ 20 (* (- 1) var14)) (- 1)))) (and (and (and (and (and (= var12 (write var19 var17 (O_node (node 3 (|node::flag| (getnode (read var19 var17))) (|node::n| (getnode (read var19 var17))))))) (= var11 var18)) (= var10 var17)) (= var9 var16)) (= var8 var15)) (= var7 var14))) (and (and (and (and (and (= var6 (write var12 var10 (O_node (node (|node::h| (getnode (read var12 var10))) (|node::flag| (getnode (read var12 var10))) 0)))) (= var5 var11)) (= var4 var10)) (= var3 var9)) (= var2 var8)) (= var1 var7))) (= var0 0)))) (inv_main_19 var6 var5 var3 var3 var2 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Int) (var9 Addr) (var10 Int) (var11 Int) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Heap) (var21 Heap) (var22 Int) (var23 Addr) (var24 Addr) (var25 Addr) (var26 Addr) (var27 Heap)) (or (not (and (inv_main_19 var27 var26 var25 var24 var23 var22) (and (and (and (and (and (and (and (and (= var21 var20) (= var19 var18)) (= var17 var16)) (= var15 var14)) (= var13 var12)) (= var11 var10)) (= var9 (|node::n| (getnode (read var20 var16))))) (and (and (= var8 1) (and (and (and (and (and (and (= var20 var7) (= var18 var6)) (= var16 var5)) (= var14 var4)) (= var12 var3)) (= var10 var2)) (= var8 (|node::h| (getnode (read var7 var5)))))) (and (not (= (|node::flag| (getnode (read var7 var5))) 0)) (and (not (= var1 3)) (and (and (and (and (and (and (= var7 var27) (= var6 var26)) (= var5 var25)) (= var4 var24)) (= var3 var23)) (= var2 var22)) (= var1 (|node::h| (getnode (read var27 var25))))))))) (= var0 (+ var11 1))))) (inv_main_19 var21 var19 var9 var15 var13 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Int) (var9 Addr) (var10 Int) (var11 Int) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Heap) (var21 Heap) (var22 Int) (var23 Addr) (var24 Addr) (var25 Addr) (var26 Addr) (var27 Heap)) (or (not (and (inv_main_19 var27 var26 var25 var24 var23 var22) (and (and (and (and (and (and (and (and (= var21 var20) (= var19 var18)) (= var17 var16)) (= var15 var14)) (= var13 var12)) (= var11 var10)) (= var9 (|node::n| (getnode (read var20 var16))))) (and (and (= var8 2) (and (and (and (and (and (and (= var20 var7) (= var18 var6)) (= var16 var5)) (= var14 var4)) (= var12 var3)) (= var10 var2)) (= var8 (|node::h| (getnode (read var7 var5)))))) (and (= (|node::flag| (getnode (read var7 var5))) 0) (and (not (= var1 3)) (and (and (and (and (and (and (= var7 var27) (= var6 var26)) (= var5 var25)) (= var4 var24)) (= var3 var23)) (= var2 var22)) (= var1 (|node::h| (getnode (read var27 var25))))))))) (= var0 (+ var11 1))))) (inv_main_19 var21 var19 var9 var15 var13 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Heap) (var12 Heap) (var13 Int) (var14 Int) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Heap)) (or (not (and (inv_main_19 var19 var18 var17 var16 var15 var14) (and (and (not (= var13 1)) (and (and (and (and (and (and (= var12 var11) (= var10 var9)) (= var8 var7)) (= var6 var5)) (= var4 var3)) (= var2 var1)) (= var13 (|node::h| (getnode (read var11 var7)))))) (and (not (= (|node::flag| (getnode (read var11 var7))) 0)) (and (not (= var0 3)) (and (and (and (and (and (and (= var11 var19) (= var9 var18)) (= var7 var17)) (= var5 var16)) (= var3 var15)) (= var1 var14)) (= var0 (|node::h| (getnode (read var19 var17)))))))))) (inv_exit var12 var10))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Heap) (var12 Heap) (var13 Int) (var14 Int) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Heap)) (or (not (and (inv_main_19 var19 var18 var17 var16 var15 var14) (and (and (not (= var13 2)) (and (and (and (and (and (and (= var12 var11) (= var10 var9)) (= var8 var7)) (= var6 var5)) (= var4 var3)) (= var2 var1)) (= var13 (|node::h| (getnode (read var11 var7)))))) (and (= (|node::flag| (getnode (read var11 var7))) 0) (and (not (= var0 3)) (and (and (and (and (and (and (= var11 var19) (= var9 var18)) (= var7 var17)) (= var5 var16)) (= var3 var15)) (= var1 var14)) (= var0 (|node::h| (getnode (read var19 var17)))))))))) (inv_exit var12 var10))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap) (var11 Heap) (var12 Int) (var13 Int) (var14 Int) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Heap)) (or (not (and (inv_main_19 var19 var18 var17 var16 var15 var14) (and (and (or (not (= var13 3)) (<= 0 (+ (+ var12 (- 20)) (- 1)))) (and (and (and (and (and (and (= var11 var10) (= var9 var8)) (= var7 var6)) (= var5 var4)) (= var3 var2)) (= var12 var1)) (= var13 (|node::h| (getnode (read var10 var6)))))) (and (= var0 3) (and (and (and (and (and (and (= var10 var19) (= var8 var18)) (= var6 var17)) (= var4 var16)) (= var2 var15)) (= var1 var14)) (= var0 (|node::h| (getnode (read var19 var17))))))))) (inv_exit var11 var9))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap) (var11 Heap) (var12 Int) (var13 Int) (var14 Int) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Heap)) (or (not (and (inv_main_19 var19 var18 var17 var16 var15 var14) (and (and (and (= var13 3) (not (<= 0 (+ (+ var12 (- 20)) (- 1))))) (and (and (and (and (and (and (= var11 var10) (= var9 var8)) (= var7 var6)) (= var5 var4)) (= var3 var2)) (= var12 var1)) (= var13 (|node::h| (getnode (read var10 var6)))))) (and (= var0 3) (and (and (and (and (and (and (= var10 var19) (= var8 var18)) (= var6 var17)) (= var4 var16)) (= var2 var15)) (= var1 var14)) (= var0 (|node::h| (getnode (read var19 var17))))))))) (inv_main_31 var11 var9 var5 var5 var3 var12))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Int) (var9 Int) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Heap) (var19 Heap) (var20 Int) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Addr) (var25 Heap)) (or (not (and (inv_main_31 var25 var24 var23 var22 var21 var20) (and (and (and (and (and (and (and (and (= var19 var18) (= var17 var16)) (= var15 var14)) (= var13 var12)) (= var11 var10)) (= var9 var8)) (= var7 (|node::n| (getnode (read var18 var14))))) (and (not (= var6 nullAddr)) (and (and (and (and (and (and (= var18 var25) (= var16 var24)) (= var14 var23)) (= var12 var22)) (= var10 var21)) (= var8 var20)) (= var6 (|node::n| (getnode (read var25 var23))))))) (and (and (and (and (and (= var5 (write var19 var15 defObj)) (or (and (= var17 var15) (= var4 nullAddr)) (and (not (= var17 var15)) (= var4 var17)))) (= var3 var15)) (= var2 var13)) (= var1 var7)) (= var0 var9))))) (inv_main_31 var5 var4 var1 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Int) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Heap) (var13 Addr) (var14 Int) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Heap)) (or (not (and (inv_main_31 var19 var18 var17 var16 var15 var14) (and (and (and (= var13 nullAddr) (and (and (and (and (and (and (= var12 var19) (= var11 var18)) (= var10 var17)) (= var9 var16)) (= var8 var15)) (= var7 var14)) (= var13 (|node::n| (getnode (read var19 var17)))))) (and (and (and (and (and (= var6 (write var12 var10 defObj)) (or (and (= var11 var10) (= var5 nullAddr)) (and (not (= var11 var10)) (= var5 var11)))) (= var4 var10)) (= var3 var9)) (= var2 var8)) (= var1 var7))) (= var0 0)))) (inv_main-1_-1 var6 var5 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (inv_main535_15 var5 var4 var3 var2 var1 var0)) (inv_main535_15 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Bool) (var5 Addr) (var6 node) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Heap)) (or (not (and (inv_main534_3 var13 var12 var11 var10 var9) (and (and (= var8 nullAddr) (and (and (and (and (and (= var7 (newHeap (alloc var13 (O_node var6)))) (or (and var4 (= var5 (newAddr (alloc var13 (O_node var6))))) (and (not var4) (= var5 var12)))) (= var3 var11)) (= var2 var10)) (= var1 var9)) (= var8 (newAddr (alloc var13 (O_node var6)))))) (= var0 1)))) (inv_main535_15 var7 var5 var3 var8 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Int) (var6 Addr) (var7 Heap) (var8 Int) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Bool) (var15 node) (var16 Heap) (var17 Int) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Heap) (var23 Addr) (var24 Int) (var25 Int) (var26 Addr) (var27 Addr) (var28 Addr) (var29 Addr) (var30 Addr) (var31 Addr) (var32 Addr) (var33 Addr) (var34 Heap) (var35 Heap) (var36 Int) (var37 Addr) (var38 Addr) (var39 Addr) (var40 Addr) (var41 Heap)) (or (not (and (inv_main537_3 var41 var40 var39 var38 var37 var36) (and (and (and (and (and (and (and (and (= var35 var34) (= var33 var32)) (= var31 var30)) (= var29 var28)) (= var27 var26)) (= var25 var24)) (= var23 (|node::n| (getnode (read var34 var30))))) (and (and (and (and (and (= var34 (write var22 var21 (O_node (node (|node::h| (getnode (read var22 var21))) (|node::flag| (getnode (read var22 var21))) var20)))) (= var32 var19)) (= var30 var21)) (= var28 var18)) (= var26 var20)) (= var24 var17))) (and (and (and (not (= var20 nullAddr)) (and (and (and (and (and (and (= var22 (newHeap (alloc var16 (O_node var15)))) (or (and var14 (= var19 (newAddr (alloc var16 (O_node var15))))) (and (not var14) (= var19 var13)))) (= var21 var12)) (= var18 var11)) (= var10 var9)) (= var17 var8)) (= var20 (newAddr (alloc var16 (O_node var15)))))) (and (and (not (= (|node::flag| (getnode (read var7 var6))) 0)) (and (not (= var5 0)) (<= 0 (+ (+ 20 (* (- 1) var36)) (- 1))))) (and (and (and (and (and (= var7 (write var41 var39 (O_node (node (|node::h| (getnode (read var41 var39))) var4 (|node::n| (getnode (read var41 var39))))))) (= var3 var40)) (= var6 var39)) (= var2 var38)) (= var1 var37)) (= var0 (+ var36 1))))) (and (and (and (and (and (= var16 (write var7 var6 (O_node (node 1 (|node::flag| (getnode (read var7 var6))) (|node::n| (getnode (read var7 var6))))))) (= var13 var3)) (= var12 var6)) (= var11 var2)) (= var9 var1)) (= var8 var0)))))) (inv_main537_3 var35 var33 var23 var29 var27 var25))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Int) (var6 Addr) (var7 Heap) (var8 Int) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Bool) (var15 node) (var16 Heap) (var17 Int) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Heap) (var23 Addr) (var24 Int) (var25 Int) (var26 Addr) (var27 Addr) (var28 Addr) (var29 Addr) (var30 Addr) (var31 Addr) (var32 Addr) (var33 Addr) (var34 Heap) (var35 Heap) (var36 Int) (var37 Addr) (var38 Addr) (var39 Addr) (var40 Addr) (var41 Heap)) (or (not (and (inv_main537_3 var41 var40 var39 var38 var37 var36) (and (and (and (and (and (and (and (and (= var35 var34) (= var33 var32)) (= var31 var30)) (= var29 var28)) (= var27 var26)) (= var25 var24)) (= var23 (|node::n| (getnode (read var34 var30))))) (and (and (and (and (and (= var34 (write var22 var21 (O_node (node (|node::h| (getnode (read var22 var21))) (|node::flag| (getnode (read var22 var21))) var20)))) (= var32 var19)) (= var30 var21)) (= var28 var18)) (= var26 var20)) (= var24 var17))) (and (and (and (not (= var20 nullAddr)) (and (and (and (and (and (and (= var22 (newHeap (alloc var16 (O_node var15)))) (or (and var14 (= var19 (newAddr (alloc var16 (O_node var15))))) (and (not var14) (= var19 var13)))) (= var21 var12)) (= var18 var11)) (= var10 var9)) (= var17 var8)) (= var20 (newAddr (alloc var16 (O_node var15)))))) (and (and (= (|node::flag| (getnode (read var7 var6))) 0) (and (not (= var5 0)) (<= 0 (+ (+ 20 (* (- 1) var36)) (- 1))))) (and (and (and (and (and (= var7 (write var41 var39 (O_node (node (|node::h| (getnode (read var41 var39))) var4 (|node::n| (getnode (read var41 var39))))))) (= var3 var40)) (= var6 var39)) (= var2 var38)) (= var1 var37)) (= var0 (+ var36 1))))) (and (and (and (and (and (= var16 (write var7 var6 (O_node (node 2 (|node::flag| (getnode (read var7 var6))) (|node::n| (getnode (read var7 var6))))))) (= var13 var3)) (= var12 var6)) (= var11 var2)) (= var9 var1)) (= var8 var0)))))) (inv_main537_3 var35 var33 var23 var29 var27 var25))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Bool) (var5 Addr) (var6 node) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Heap)) (or (not (and (inv_main534_3 var13 var12 var11 var10 var9) (and (and (not (= var8 nullAddr)) (and (and (and (and (and (= var7 (newHeap (alloc var13 (O_node var6)))) (or (and var4 (= var5 (newAddr (alloc var13 (O_node var6))))) (and (not var4) (= var5 var12)))) (= var3 var11)) (= var2 var10)) (= var1 var9)) (= var8 (newAddr (alloc var13 (O_node var6)))))) (= var0 0)))) (inv_main537_3 var7 var5 var8 var8 var1 var0))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_exit var1 var0) (not (= var0 nullAddr))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap)) (not (and (inv_main-1_-1 var2 var1 var0) (not (= var1 nullAddr))))))
(check-sat)