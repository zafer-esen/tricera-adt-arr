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
   (node (|node::h| Int) (|node::flag| Int) (|node::n| Addr))
  )
))
(declare-fun inv_main534_3 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main535_15 (Heap Addr Addr Addr Int) Bool)
(declare-fun inv_main537_3 (Heap Addr Addr Addr Int) Bool)
(declare-fun inv_main547_17 (Heap Addr Addr Addr Int Int) Bool)
(declare-fun inv_main_19 (Heap Addr Addr Addr Int) Bool)
(declare-fun inv_main_32 (Heap Addr Addr Addr Int) Bool)
(declare-fun inv_main_34 (Heap Addr Addr Addr Int) Bool)
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (= var3 emptyHeap)) (inv_main534_3 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Int) (var8 Int) (var9 Int) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Heap) (var16 Heap) (var17 Addr) (var18 Int) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Heap)) (or (not (and (inv_main_19 var22 var21 var20 var19 var18) (and (and (= var17 nullAddr) (and (and (and (and (and (= var16 var15) (= var14 var13)) (= var12 var13)) (= var11 var10)) (= var9 var8)) (= var17 (|node::n| (getnode (read var15 var13)))))) (and (and (and (= var7 3) (not (<= 0 (+ (+ var8 (- 20)) (- 1))))) (and (and (and (and (and (= var15 var6) (= var5 var4)) (= var13 var3)) (= var10 var2)) (= var8 var1)) (= var7 (|node::h| (getnode (read var6 var4)))))) (and (= var0 3) (and (and (and (and (and (= var6 var22) (= var4 var21)) (= var3 var20)) (= var2 var19)) (= var1 var18)) (= var0 (|node::h| (getnode (read var22 var21)))))))))) (inv_main_32 var16 var14 var12 var11 var9))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap) (var9 Heap) (var10 Addr) (var11 Int) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Heap)) (or (not (and (inv_main_34 var15 var14 var13 var12 var11) (and (and (= var10 nullAddr) (and (and (and (and (and (= var9 var8) (= var7 var6)) (= var5 var4)) (= var3 var6)) (= var2 var1)) (= var10 (|node::n| (getnode (read var8 var6)))))) (and (and (and (and (= var8 (write var15 var14 defObj)) (= var0 var14)) (= var4 var13)) (= var6 var12)) (= var1 var11))))) (inv_main_32 var9 var7 var5 var3 var2))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Addr) (var6 Heap) (var7 Int) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 node) (var13 Heap) (var14 Int) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Heap) (var19 Addr) (var20 Int) (var21 Int) (var22 Addr) (var23 Addr) (var24 Addr) (var25 Addr) (var26 Addr) (var27 Addr) (var28 Heap) (var29 Heap) (var30 Int) (var31 Addr) (var32 Addr) (var33 Addr) (var34 Heap)) (or (not (and (inv_main537_3 var34 var33 var32 var31 var30) (and (and (and (and (and (and (and (= var29 var28) (= var27 var26)) (= var25 var24)) (= var23 var22)) (= var21 var20)) (= var19 (|node::n| (getnode (read var28 var26))))) (and (and (and (and (= var28 (write var18 var17 (O_node (node (|node::h| (getnode (read var18 var17))) (|node::flag| (getnode (read var18 var17))) var16)))) (= var26 var17)) (= var24 var15)) (= var22 var16)) (= var20 var14))) (and (and (and (not (= var16 nullAddr)) (and (and (and (and (and (= var18 (newHeap (alloc var13 (O_node var12)))) (= var17 var11)) (= var15 var10)) (= var9 var8)) (= var14 var7)) (= var16 (newAddr (alloc var13 (O_node var12)))))) (and (and (not (= (|node::flag| (getnode (read var6 var5))) 0)) (and (not (= var4 0)) (<= 0 (+ (+ 20 (* (- 1) var30)) (- 1))))) (and (and (and (and (= var6 (write var34 var33 (O_node (node (|node::h| (getnode (read var34 var33))) var3 (|node::n| (getnode (read var34 var33))))))) (= var5 var33)) (= var2 var32)) (= var1 var31)) (= var0 (+ var30 1))))) (and (and (and (and (= var13 (write var6 var5 (O_node (node 1 (|node::flag| (getnode (read var6 var5))) (|node::n| (getnode (read var6 var5))))))) (= var11 var5)) (= var10 var2)) (= var8 var1)) (= var7 var0)))))) (inv_main537_3 var29 var19 var25 var23 var21))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Addr) (var6 Heap) (var7 Int) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 node) (var13 Heap) (var14 Int) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Heap) (var19 Addr) (var20 Int) (var21 Int) (var22 Addr) (var23 Addr) (var24 Addr) (var25 Addr) (var26 Addr) (var27 Addr) (var28 Heap) (var29 Heap) (var30 Int) (var31 Addr) (var32 Addr) (var33 Addr) (var34 Heap)) (or (not (and (inv_main537_3 var34 var33 var32 var31 var30) (and (and (and (and (and (and (and (= var29 var28) (= var27 var26)) (= var25 var24)) (= var23 var22)) (= var21 var20)) (= var19 (|node::n| (getnode (read var28 var26))))) (and (and (and (and (= var28 (write var18 var17 (O_node (node (|node::h| (getnode (read var18 var17))) (|node::flag| (getnode (read var18 var17))) var16)))) (= var26 var17)) (= var24 var15)) (= var22 var16)) (= var20 var14))) (and (and (and (not (= var16 nullAddr)) (and (and (and (and (and (= var18 (newHeap (alloc var13 (O_node var12)))) (= var17 var11)) (= var15 var10)) (= var9 var8)) (= var14 var7)) (= var16 (newAddr (alloc var13 (O_node var12)))))) (and (and (= (|node::flag| (getnode (read var6 var5))) 0) (and (not (= var4 0)) (<= 0 (+ (+ 20 (* (- 1) var30)) (- 1))))) (and (and (and (and (= var6 (write var34 var33 (O_node (node (|node::h| (getnode (read var34 var33))) var3 (|node::n| (getnode (read var34 var33))))))) (= var5 var33)) (= var2 var32)) (= var1 var31)) (= var0 (+ var30 1))))) (and (and (and (and (= var13 (write var6 var5 (O_node (node 2 (|node::flag| (getnode (read var6 var5))) (|node::n| (getnode (read var6 var5))))))) (= var11 var5)) (= var10 var2)) (= var8 var1)) (= var7 var0)))))) (inv_main537_3 var29 var19 var25 var23 var21))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 node) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main534_3 var10 var9 var8 var7) (and (and (not (= var6 nullAddr)) (and (and (and (and (= var5 (newHeap (alloc var10 (O_node var4)))) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var6 (newAddr (alloc var10 (O_node var4)))))) (= var0 0)))) (inv_main537_3 var5 var6 var6 var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (inv_main547_17 var5 var4 var3 var2 var1 var0)) (inv_main547_17 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Int) (var5 Int) (var6 Addr) (var7 Heap) (var8 Int) (var9 Int) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 node) (var17 Heap) (var18 Heap) (var19 Addr) (var20 Int) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Heap)) (or (not (and (inv_main537_3 var24 var23 var22 var21 var20) (and (and (and (and (= var19 nullAddr) (and (and (and (and (and (= var18 (newHeap (alloc var17 (O_node var16)))) (= var15 var14)) (= var13 var12)) (= var11 var10)) (= var9 var8)) (= var19 (newAddr (alloc var17 (O_node var16)))))) (and (and (not (= (|node::flag| (getnode (read var7 var6))) 0)) (and (not (= var5 0)) (<= 0 (+ (+ 20 (* (- 1) var20)) (- 1))))) (and (and (and (and (= var7 (write var24 var23 (O_node (node (|node::h| (getnode (read var24 var23))) var4 (|node::n| (getnode (read var24 var23))))))) (= var6 var23)) (= var3 var22)) (= var2 var21)) (= var1 (+ var20 1))))) (and (and (and (and (= var17 (write var7 var6 (O_node (node 1 (|node::flag| (getnode (read var7 var6))) (|node::n| (getnode (read var7 var6))))))) (= var14 var6)) (= var12 var3)) (= var10 var2)) (= var8 var1))) (= var0 1)))) (inv_main547_17 var18 var15 var13 var19 var9 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Int) (var5 Int) (var6 Addr) (var7 Heap) (var8 Int) (var9 Int) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 node) (var17 Heap) (var18 Heap) (var19 Addr) (var20 Int) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Heap)) (or (not (and (inv_main537_3 var24 var23 var22 var21 var20) (and (and (and (and (= var19 nullAddr) (and (and (and (and (and (= var18 (newHeap (alloc var17 (O_node var16)))) (= var15 var14)) (= var13 var12)) (= var11 var10)) (= var9 var8)) (= var19 (newAddr (alloc var17 (O_node var16)))))) (and (and (= (|node::flag| (getnode (read var7 var6))) 0) (and (not (= var5 0)) (<= 0 (+ (+ 20 (* (- 1) var20)) (- 1))))) (and (and (and (and (= var7 (write var24 var23 (O_node (node (|node::h| (getnode (read var24 var23))) var4 (|node::n| (getnode (read var24 var23))))))) (= var6 var23)) (= var3 var22)) (= var2 var21)) (= var1 (+ var20 1))))) (and (and (and (and (= var17 (write var7 var6 (O_node (node 2 (|node::flag| (getnode (read var7 var6))) (|node::n| (getnode (read var7 var6))))))) (= var14 var6)) (= var12 var3)) (= var10 var2)) (= var8 var1))) (= var0 1)))) (inv_main547_17 var18 var15 var13 var19 var9 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (inv_main535_15 var4 var3 var2 var1 var0)) (inv_main535_15 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 node) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main534_3 var10 var9 var8 var7) (and (and (= var6 nullAddr) (and (and (and (and (= var5 (newHeap (alloc var10 (O_node var4)))) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var6 (newAddr (alloc var10 (O_node var4)))))) (= var0 1)))) (inv_main535_15 var5 var3 var6 var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Int) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap) (var11 Int) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Heap)) (or (not (and (inv_main537_3 var15 var14 var13 var12 var11) (and (and (and (not (<= 0 (+ (+ 20 (* (- 1) var11)) (- 1)))) (and (and (and (and (= var10 (write var15 var14 (O_node (node 3 (|node::flag| (getnode (read var15 var14))) (|node::n| (getnode (read var15 var14))))))) (= var9 var14)) (= var8 var13)) (= var7 var12)) (= var6 var11))) (and (and (and (and (= var5 (write var10 var9 (O_node (node (|node::h| (getnode (read var10 var9))) (|node::flag| (getnode (read var10 var9))) 0)))) (= var4 var9)) (= var3 var8)) (= var2 var7)) (= var1 var6))) (= var0 0)))) (inv_main_19 var5 var3 var3 var2 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Int) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap) (var11 Int) (var12 Int) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Heap)) (or (not (and (inv_main537_3 var16 var15 var14 var13 var12) (and (and (and (and (= var11 0) (<= 0 (+ (+ 20 (* (- 1) var12)) (- 1)))) (and (and (and (and (= var10 (write var16 var15 (O_node (node 3 (|node::flag| (getnode (read var16 var15))) (|node::n| (getnode (read var16 var15))))))) (= var9 var15)) (= var8 var14)) (= var7 var13)) (= var6 var12))) (and (and (and (and (= var5 (write var10 var9 (O_node (node (|node::h| (getnode (read var10 var9))) (|node::flag| (getnode (read var10 var9))) 0)))) (= var4 var9)) (= var3 var8)) (= var2 var7)) (= var1 var6))) (= var0 0)))) (inv_main_19 var5 var3 var3 var2 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Int) (var8 Addr) (var9 Int) (var10 Int) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Heap) (var18 Heap) (var19 Int) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Heap)) (or (not (and (inv_main_19 var23 var22 var21 var20 var19) (and (and (and (and (and (and (and (= var18 var17) (= var16 var15)) (= var14 var13)) (= var12 var11)) (= var10 var9)) (= var8 (|node::n| (getnode (read var17 var15))))) (and (and (= var7 1) (and (and (and (and (and (= var17 var6) (= var15 var5)) (= var13 var4)) (= var11 var3)) (= var9 var2)) (= var7 (|node::h| (getnode (read var6 var5)))))) (and (not (= (|node::flag| (getnode (read var6 var5))) 0)) (and (not (= var1 3)) (and (and (and (and (and (= var6 var23) (= var5 var22)) (= var4 var21)) (= var3 var20)) (= var2 var19)) (= var1 (|node::h| (getnode (read var23 var22))))))))) (= var0 (+ var10 1))))) (inv_main_19 var18 var8 var14 var12 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Int) (var8 Addr) (var9 Int) (var10 Int) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Heap) (var18 Heap) (var19 Int) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Heap)) (or (not (and (inv_main_19 var23 var22 var21 var20 var19) (and (and (and (and (and (and (and (= var18 var17) (= var16 var15)) (= var14 var13)) (= var12 var11)) (= var10 var9)) (= var8 (|node::n| (getnode (read var17 var15))))) (and (and (= var7 2) (and (and (and (and (and (= var17 var6) (= var15 var5)) (= var13 var4)) (= var11 var3)) (= var9 var2)) (= var7 (|node::h| (getnode (read var6 var5)))))) (and (= (|node::flag| (getnode (read var6 var5))) 0) (and (not (= var1 3)) (and (and (and (and (and (= var6 var23) (= var5 var22)) (= var4 var21)) (= var3 var20)) (= var2 var19)) (= var1 (|node::h| (getnode (read var23 var22))))))))) (= var0 (+ var10 1))))) (inv_main_19 var18 var8 var14 var12 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Int) (var8 Int) (var9 Addr) (var10 Addr) (var11 Heap) (var12 Addr) (var13 Addr) (var14 Int) (var15 Int) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Heap) (var23 Heap) (var24 Int) (var25 Addr) (var26 Addr) (var27 Addr) (var28 Heap)) (or (not (and (inv_main_19 var28 var27 var26 var25 var24) (and (and (and (and (and (and (and (= var23 var22) (= var21 var20)) (= var19 var18)) (= var17 var16)) (= var15 var14)) (= var13 (|node::n| (getnode (read var22 var20))))) (and (not (= var12 nullAddr)) (and (and (and (and (and (= var22 var11) (= var20 var10)) (= var18 var10)) (= var16 var9)) (= var14 var8)) (= var12 (|node::n| (getnode (read var11 var10))))))) (and (and (and (= var7 3) (not (<= 0 (+ (+ var8 (- 20)) (- 1))))) (and (and (and (and (and (= var11 var6) (= var5 var4)) (= var10 var3)) (= var9 var2)) (= var8 var1)) (= var7 (|node::h| (getnode (read var6 var4)))))) (and (= var0 3) (and (and (and (and (and (= var6 var28) (= var4 var27)) (= var3 var26)) (= var2 var25)) (= var1 var24)) (= var0 (|node::h| (getnode (read var28 var27)))))))))) (inv_main_34 var23 var21 var19 var13 var15))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Int) (var8 Int) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Heap) (var16 Heap) (var17 Int) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Heap)) (or (not (and (inv_main_34 var21 var20 var19 var18 var17) (and (and (and (and (and (and (and (= var16 var15) (= var14 var13)) (= var12 var11)) (= var10 var9)) (= var8 var7)) (= var6 (|node::n| (getnode (read var15 var13))))) (and (not (= var5 nullAddr)) (and (and (and (and (and (= var15 var4) (= var13 var3)) (= var11 var2)) (= var9 var3)) (= var7 var1)) (= var5 (|node::n| (getnode (read var4 var3))))))) (and (and (and (and (= var4 (write var21 var20 defObj)) (= var0 var20)) (= var2 var19)) (= var3 var18)) (= var1 var17))))) (inv_main_34 var16 var14 var12 var6 var8))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main_34 var4 var3 var2 var1 var0) (and (not (= var3 nullAddr)) (= (read var4 var3) defObj))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main_32 var4 var3 var2 var1 var0) (and (not (= var3 nullAddr)) (= (read var4 var3) defObj))))))
(check-sat)
