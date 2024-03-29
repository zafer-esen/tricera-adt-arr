(set-logic HORN)
(set-info :source |
    Benchmark: C_VC
    Output by Princess (http://www.philipp.ruemmer.org/princess.shtml)
|)
(set-info :status unsat)
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
(declare-fun inv_main532_3 (Heap) Bool)
(declare-fun inv_main533_15 (Heap Addr Int) Bool)
(declare-fun inv_main536_3 (Heap Addr Addr Addr Int) Bool)
(declare-fun inv_main540_17 (Heap Addr Addr Addr Int Int) Bool)
(declare-fun inv_main550_9_20 (Heap Addr Addr Addr Int) Bool)
(declare-fun inv_main_16 (Heap Addr Addr Addr Int) Bool)
(declare-fun inv_main_24 (Heap Addr Addr Addr Int) Bool)
(assert (forall ((var0 Heap)) (or (not (= var0 emptyHeap)) (inv_main532_3 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Int) (var6 Int) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main_16 var10 var9 var8 var7 var6) (and (and (not (= var5 1)) (and (and (and (and (and (= var4 var10) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var0 var6)) (= var5 (|node::h| (getnode (read var10 var7)))))) (not (= var7 nullAddr))))) (inv_main550_9_20 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap)) (or (not (inv_main533_15 var2 var1 var0)) (inv_main533_15 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 node) (var2 Heap) (var3 Addr) (var4 Heap)) (or (not (and (inv_main532_3 var4) (and (and (= var3 nullAddr) (and (= var2 (newHeap (alloc var4 (O_node var1)))) (= var3 (newAddr (alloc var4 (O_node var1)))))) (= var0 1)))) (inv_main533_15 var2 var3 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main_16 var4 var3 var2 var1 var0) (= var1 nullAddr))) (inv_main_24 var4 var3 var2 var3 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Int) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Heap) (var12 Int) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Heap)) (or (not (and (inv_main_24 var16 var15 var14 var13 var12) (and (and (and (and (and (and (and (= var11 var16) (= var10 var15)) (= var9 var14)) (= var8 var13)) (= var7 var12)) (= var6 (|node::n| (getnode (read var16 var13))))) (and (and (and (and (and (= var5 (write var11 var8 defObj)) (= var4 var10)) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var0 var6))) (not (= var13 nullAddr))))) (inv_main_24 var5 var4 var3 var0 var1))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 node) (var8 Heap) (var9 Int) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Heap) (var14 Addr) (var15 Int) (var16 Int) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Heap) (var24 Heap) (var25 Int) (var26 Addr) (var27 Addr) (var28 Addr) (var29 Heap)) (or (not (and (inv_main536_3 var29 var28 var27 var26 var25) (and (and (and (and (and (and (and (and (= var24 var23) (= var22 var21)) (= var20 var19)) (= var18 var17)) (= var16 var15)) (= var14 (|node::n| (getnode (read var23 var17))))) (and (and (and (and (= var23 (write var13 var12 (O_node (node (|node::h| (getnode (read var13 var12))) var11)))) (= var21 var10)) (= var19 var11)) (= var17 var12)) (= var15 var9))) (and (not (= var11 nullAddr)) (and (and (and (and (and (and (and (= var13 (newHeap (alloc var8 (O_node var7)))) (= var10 var6)) (= var5 var4)) (= var12 var3)) (= var9 var2)) (= var11 (newAddr (alloc var8 (O_node var7))))) (and (not (= var1 0)) (<= 0 (+ (+ 30 (* (- 1) var25)) (- 1))))) (and (and (and (and (= var8 (write var29 var26 (O_node (node var25 (|node::n| (getnode (read var29 var26))))))) (= var6 var28)) (= var4 var27)) (= var3 var26)) (= var2 var25))))) (= var0 (+ var16 1))))) (inv_main536_3 var24 var22 var20 var14 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 node) (var3 Heap) (var4 Addr) (var5 Heap)) (or (not (and (inv_main532_3 var5) (and (and (not (= var4 nullAddr)) (and (= var3 (newHeap (alloc var5 (O_node var2)))) (= var4 (newAddr (alloc var5 (O_node var2)))))) (= var1 0)))) (inv_main536_3 var3 var4 var0 var4 var1))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (inv_main540_17 var5 var4 var3 var2 var1 var0)) (inv_main540_17 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Int) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 node) (var11 Heap) (var12 Heap) (var13 Addr) (var14 Int) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Heap)) (or (not (and (inv_main536_3 var18 var17 var16 var15 var14) (and (and (= var13 nullAddr) (and (and (and (and (and (and (and (= var12 (newHeap (alloc var11 (O_node var10)))) (= var9 var8)) (= var7 var6)) (= var5 var4)) (= var3 var2)) (= var13 (newAddr (alloc var11 (O_node var10))))) (and (not (= var1 0)) (<= 0 (+ (+ 30 (* (- 1) var14)) (- 1))))) (and (and (and (and (= var11 (write var18 var15 (O_node (node var14 (|node::n| (getnode (read var18 var15))))))) (= var8 var17)) (= var6 var16)) (= var4 var15)) (= var2 var14)))) (= var0 1)))) (inv_main540_17 var12 var9 var13 var5 var3 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Int) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap) (var11 Int) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Heap)) (or (not (and (inv_main536_3 var15 var14 var13 var12 var11) (and (and (and (not (<= 0 (+ (+ 30 (* (- 1) var11)) (- 1)))) (and (and (and (and (= var10 (write var15 var12 (O_node (node var11 (|node::n| (getnode (read var15 var12))))))) (= var9 var14)) (= var8 var13)) (= var7 var12)) (= var6 var11))) (and (and (and (and (= var5 (write var10 var7 (O_node (node (|node::h| (getnode (read var10 var7))) 0)))) (= var4 var9)) (= var3 var8)) (= var2 var7)) (= var1 var6))) (= var0 0)))) (inv_main_16 var5 var4 var3 var4 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Int) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap) (var11 Int) (var12 Int) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Heap)) (or (not (and (inv_main536_3 var16 var15 var14 var13 var12) (and (and (and (and (= var11 0) (<= 0 (+ (+ 30 (* (- 1) var12)) (- 1)))) (and (and (and (and (= var10 (write var16 var13 (O_node (node var12 (|node::n| (getnode (read var16 var13))))))) (= var9 var15)) (= var8 var14)) (= var7 var13)) (= var6 var12))) (and (and (and (and (= var5 (write var10 var7 (O_node (node (|node::h| (getnode (read var10 var7))) 0)))) (= var4 var9)) (= var3 var8)) (= var2 var7)) (= var1 var6))) (= var0 0)))) (inv_main_16 var5 var4 var3 var4 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Int) (var4 Int) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Heap) (var12 Heap) (var13 Int) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Heap)) (or (not (and (inv_main_16 var17 var16 var15 var14 var13) (and (and (and (and (and (and (and (= var12 var11) (= var10 var9)) (= var8 var7)) (= var6 var5)) (= var4 var3)) (= var2 (|node::n| (getnode (read var11 var5))))) (and (and (= var1 1) (and (and (and (and (and (= var11 var17) (= var9 var16)) (= var7 var15)) (= var5 var14)) (= var3 var13)) (= var1 (|node::h| (getnode (read var17 var14)))))) (not (= var14 nullAddr)))) (= var0 (+ var4 1))))) (inv_main_16 var12 var10 var8 var2 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (not (inv_main550_9_20 var4 var3 var2 var1 var0))))
(check-sat)
