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
   (node (|node::hash| Int) (|node::next| Addr))
  )
))
(declare-fun inv_main (Heap Addr Int) Bool)
(declare-fun inv_main580_5 (Heap) Bool)
(declare-fun inv_main581_5 (Heap Addr Int) Bool)
(declare-fun inv_main591_13 (Heap Addr Int) Bool)
(assert (forall ((var0 Heap)) (or (not (= var0 emptyHeap)) (inv_main580_5 var0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Int) (var4 Int) (var5 Addr) (var6 Heap)) (or (not (and (inv_main var6 var5 var4) (and (and (not (<= 0 (+ var3 (* (- 1) var2)))) (and (and (and (= var1 var6) (= var0 var5)) (= var2 var4)) (= var3 (|node::hash| (getnode (read var6 var5)))))) (not (= var5 nullAddr))))) (inv_main591_13 var1 var0 var2))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Int) (var4 Int) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Heap) (var9 Int) (var10 Int) (var11 Int) (var12 Int) (var13 Addr) (var14 Heap)) (or (not (and (inv_main var14 var13 var12) (and (and (and (= var11 0) (and (and (<= 0 (+ var10 (* (- 1) var9))) (and (and (and (= var8 var14) (= var7 var13)) (= var9 var12)) (= var10 (|node::hash| (getnode (read var14 var13)))))) (and (and (and (= var6 var8) (= var5 var7)) (= var4 var9)) (= var3 (|node::hash| (getnode (read var8 var7))))))) (and (and (and (= var2 var6) (= var1 var5)) (= var0 var4)) (or (and (<= 0 (+ (+ (+ var4 100) (* (- 1) var3)) (- 1))) (= var11 1)) (and (not (<= 0 (+ (+ (+ var4 100) (* (- 1) var3)) (- 1)))) (= var11 0))))) (not (= var13 nullAddr))))) (inv_main591_13 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Heap)) (or (not (and (inv_main581_5 var3 var2 var1) (and (or (not (<= 0 var1)) (not (<= 0 (+ 1000000 (* (- 1) var1))))) (not (= var0 0))))) (inv_main581_5 var3 var2 var1))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Heap)) (or (not (and (inv_main581_5 var4 var3 var2) (and (or (not (<= 0 (+ (+ var1 (* (- 1) var2)) (- 1)))) (not (<= 0 (+ (+ (+ var2 100) (* (- 1) var1)) (- 1))))) (and (and (<= 0 var2) (<= 0 (+ 1000000 (* (- 1) var2)))) (not (= var0 0)))))) (inv_main581_5 var4 var3 var2))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Int) (var10 Int) (var11 Int) (var12 Int) (var13 Addr) (var14 Heap) (var15 Addr) (var16 Int) (var17 Int) (var18 Int) (var19 Int) (var20 Int) (var21 Addr) (var22 node) (var23 Heap) (var24 Int) (var25 Addr) (var26 Heap)) (or (not (and (inv_main581_5 var26 var25 var24) (and (and (and (and (and (and (and (and (and (and (= var23 (newHeap (alloc var26 (O_node var22)))) (= var21 var25)) (= var20 var24)) (= var19 var18)) (= var17 1)) (= var16 var18)) (= var15 (newAddr (alloc var26 (O_node var22))))) (and (and (and (and (and (and (= var14 (write var23 var15 (O_node (node (|node::hash| (getnode (read var23 var15))) var21)))) (= var13 var21)) (= var12 var20)) (= var11 var19)) (= var10 var17)) (= var9 var16)) (= var8 var15))) (and (and (and (and (and (and (= var7 (write var14 var8 (O_node (node var9 (|node::next| (getnode (read var14 var8))))))) (= var6 var13)) (= var5 var12)) (= var4 var11)) (= var3 var10)) (= var2 var9)) (= var1 var8))) (and (<= 0 (+ (+ var18 (* (- 1) var24)) (- 1))) (<= 0 (+ (+ (+ var24 100) (* (- 1) var18)) (- 1))))) (and (and (<= 0 var24) (<= 0 (+ 1000000 (* (- 1) var24)))) (not (= var0 0)))))) (inv_main581_5 var7 var1 var5))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Heap)) (or (not (and (inv_main580_5 var3) (and (= var2 var3) (= var1 nullAddr)))) (inv_main581_5 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Heap)) (or (not (and (inv_main581_5 var3 var2 var1) (= var0 0))) (inv_main var3 var2 var1))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Heap) (var4 Int) (var5 Addr) (var6 Heap)) (or (not (and (inv_main591_13 var6 var5 var4) (and (and (and (= var3 var6) (= var2 var5)) (= var1 var4)) (= var0 (|node::next| (getnode (read var6 var5))))))) (inv_main var3 var0 var1))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Heap) (var6 Int) (var7 Int) (var8 Int) (var9 Addr) (var10 Int) (var11 Int) (var12 Addr) (var13 Addr) (var14 Heap) (var15 Heap) (var16 Int) (var17 Addr) (var18 Heap)) (or (not (and (inv_main var18 var17 var16) (and (and (and (and (= var15 var14) (= var13 var12)) (= var11 var10)) (= var9 (|node::next| (getnode (read var14 var12))))) (and (and (and (not (= var8 0)) (and (and (<= 0 (+ var7 (* (- 1) var6))) (and (and (and (= var5 var18) (= var4 var17)) (= var6 var16)) (= var7 (|node::hash| (getnode (read var18 var17)))))) (and (and (and (= var3 var5) (= var2 var4)) (= var1 var6)) (= var0 (|node::hash| (getnode (read var5 var4))))))) (and (and (and (= var14 var3) (= var12 var2)) (= var10 var1)) (or (and (<= 0 (+ (+ (+ var1 100) (* (- 1) var0)) (- 1))) (= var8 1)) (and (not (<= 0 (+ (+ (+ var1 100) (* (- 1) var0)) (- 1)))) (= var8 0))))) (not (= var17 nullAddr)))))) (inv_main var15 var9 var11))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap)) (not (inv_main591_13 var2 var1 var0))))
(check-sat)
