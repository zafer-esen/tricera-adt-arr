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
   (node (|node::next| Addr) (|node::prev| Addr))
  )
))
(declare-fun inv_main566_5 (Heap Int Int Addr Int) Bool)
(declare-fun inv_main570_3 (Heap Int Int Addr Addr) Bool)
(declare-fun inv_main574_7 (Heap Int Int Addr Addr Addr Int) Bool)
(declare-fun inv_main588_31 (Heap Int Addr Addr Addr Addr) Bool)
(declare-fun inv_main590_33 (Heap Int Addr Addr Addr Addr) Bool)
(declare-fun inv_main593_12 (Heap Int Addr Addr Addr Addr) Bool)
(declare-fun inv_main597_38 (Heap Int Addr Addr Addr Addr) Bool)
(declare-fun inv_main599_33 (Heap Int Addr Addr Addr Addr) Bool)
(declare-fun inv_main602_12 (Heap Int Addr Addr Addr Addr) Bool)
(declare-fun inv_main606_10 (Heap Int Addr Addr Addr Addr) Bool)
(declare-fun inv_main608_33 (Heap Int Addr Addr Addr Addr) Bool)
(declare-fun inv_main611_12 (Heap Int Addr Addr Addr Addr) Bool)
(declare-fun inv_main619_3 (Heap Int) Bool)
(declare-fun inv_main_18 (Heap Int Addr Addr Addr Addr) Bool)
(declare-fun inv_main_19 (Heap Int Addr Addr Addr Addr) Bool)
(declare-fun inv_main_21 (Heap Int Addr Addr Addr Addr) Bool)
(declare-fun inv_main_22 (Heap Int Addr Addr Addr Addr) Bool)
(declare-fun inv_main_24 (Heap Int Addr Addr Addr Addr) Bool)
(declare-fun inv_main_25 (Heap Int Addr Addr Addr Addr) Bool)
(assert (forall ((var0 Int) (var1 Heap)) (or (not (and (= var1 emptyHeap) (= var0 3))) (inv_main619_3 var1 var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Int) (var6 Heap)) (or (not (and (inv_main608_33 var6 var5 var4 var3 var2 var1) (= var0 (write var6 var3 defObj)))) (inv_main_24 var0 var5 var4 var3 var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap) (var6 Int) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Int) (var12 Heap)) (or (not (and (inv_main606_10 var12 var11 var10 var9 var8 var7) (and (not (= var6 0)) (and (and (and (and (and (= var5 (write var12 var8 defObj)) (= var4 var11)) (= var3 var10)) (= var2 var9)) (= var1 var8)) (= var0 var7))))) (inv_main608_33 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Int) (var6 Heap)) (or (not (and (inv_main590_33 var6 var5 var4 var3 var2 var1) (= var0 (write var6 var1 defObj)))) (inv_main_18 var0 var5 var4 var3 var2 var1))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Int) (var6 Heap)) (or (not (and (inv_main611_12 var6 var5 var4 var3 var2 var1) (= var0 (write var6 var1 defObj)))) (inv_main_25 var0 var5 var4 var3 var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap) (var6 Int) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Int) (var12 Heap)) (or (not (and (inv_main588_31 var12 var11 var10 var9 var8 var7) (and (not (= var6 0)) (and (and (and (and (and (= var5 (write var12 var9 defObj)) (= var4 var11)) (= var3 var10)) (= var2 var9)) (= var1 var8)) (= var0 var7))))) (inv_main590_33 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Int) (var5 Int) (var6 Heap) (var7 Addr) (var8 Int) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Int) (var18 Int) (var19 Heap) (var20 Heap) (var21 Int) (var22 Int) (var23 Addr) (var24 Addr) (var25 Int) (var26 Int) (var27 Heap)) (or (not (and (inv_main570_3 var27 var26 var25 var24 var23) (and (and (and (= var22 0) (and (= var21 0) (and (and (and (and (and (= var20 var19) (= var18 var17)) (= var16 var15)) (= var14 var13)) (= var12 var11)) (= var10 (|node::next| (getnode (read var19 var13))))))) (and (and (and (and (= var19 var9) (= var17 var8)) (= var15 var7)) (= var13 var7)) (= var11 (|node::prev| (getnode (read var9 var7)))))) (and (and (not (<= 0 (+ (+ var25 (- 1)) (- 1)))) (and (and (and (and (= var6 (write var27 var24 (O_node (node var23 (|node::prev| (getnode (read var27 var24))))))) (= var5 var26)) (= var4 var25)) (= var3 var24)) (= var2 var23))) (and (and (and (and (= var9 (write var6 var2 (O_node (node (|node::next| (getnode (read var6 var2))) var3)))) (= var8 var5)) (= var1 var4)) (= var0 var3)) (= var7 var2)))))) (inv_main606_10 var20 var18 var16 var14 var12 var10))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap) (var6 Int) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Int) (var12 Heap)) (or (not (and (inv_main588_31 var12 var11 var10 var9 var8 var7) (and (= var6 0) (and (and (and (and (and (= var5 (write var12 var9 defObj)) (= var4 var11)) (= var3 var10)) (= var2 var9)) (= var1 var8)) (= var0 var7))))) (inv_main593_12 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Int) (var6 Heap)) (or (not (and (inv_main602_12 var6 var5 var4 var3 var2 var1) (= var0 (write var6 var2 defObj)))) (inv_main_22 var0 var5 var4 var3 var2 var1))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Int) (var6 Heap)) (or (not (and (inv_main593_12 var6 var5 var4 var3 var2 var1) (= var0 (write var6 var2 defObj)))) (inv_main_19 var0 var5 var4 var3 var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap) (var6 Int) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Int) (var12 Heap)) (or (not (and (inv_main597_38 var12 var11 var10 var9 var8 var7) (and (not (= var6 0)) (and (and (and (and (and (= var5 (write var12 var7 defObj)) (= var4 var11)) (= var3 var10)) (= var2 var9)) (= var1 var8)) (= var0 var7))))) (inv_main599_33 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Int) (var5 Int) (var6 Heap) (var7 Addr) (var8 Int) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Int) (var18 Int) (var19 Heap) (var20 Heap) (var21 Int) (var22 Int) (var23 Addr) (var24 Addr) (var25 Int) (var26 Int) (var27 Heap)) (or (not (and (inv_main570_3 var27 var26 var25 var24 var23) (and (and (and (not (= var22 0)) (and (= var21 0) (and (and (and (and (and (= var20 var19) (= var18 var17)) (= var16 var15)) (= var14 var13)) (= var12 var11)) (= var10 (|node::next| (getnode (read var19 var13))))))) (and (and (and (and (= var19 var9) (= var17 var8)) (= var15 var7)) (= var13 var7)) (= var11 (|node::prev| (getnode (read var9 var7)))))) (and (and (not (<= 0 (+ (+ var25 (- 1)) (- 1)))) (and (and (and (and (= var6 (write var27 var24 (O_node (node var23 (|node::prev| (getnode (read var27 var24))))))) (= var5 var26)) (= var4 var25)) (= var3 var24)) (= var2 var23))) (and (and (and (and (= var9 (write var6 var2 (O_node (node (|node::next| (getnode (read var6 var2))) var3)))) (= var8 var5)) (= var1 var4)) (= var0 var3)) (= var7 var2)))))) (inv_main597_38 var20 var18 var16 var14 var12 var10))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap) (var6 Int) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Int) (var12 Heap)) (or (not (and (inv_main597_38 var12 var11 var10 var9 var8 var7) (and (= var6 0) (and (and (and (and (and (= var5 (write var12 var7 defObj)) (= var4 var11)) (= var3 var10)) (= var2 var9)) (= var1 var8)) (= var0 var7))))) (inv_main602_12 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 node) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Int) (var6 Int) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Int) (var13 Int) (var14 Int) (var15 Int) (var16 Addr) (var17 Addr) (var18 Heap) (var19 Heap) (var20 Addr) (var21 Addr) (var22 Int) (var23 Int) (var24 Heap)) (or (not (and (inv_main570_3 var24 var23 var22 var21 var20) (and (and (and (and (and (and (and (and (and (= var19 (write var18 var17 (O_node (node var16 (|node::prev| (getnode (read var18 var17))))))) (= var15 var14)) (= var13 var12)) (= var11 var10)) (= var9 var16)) (= var8 var17)) (and (and (and (and (and (= var7 (write var19 var9 (O_node (node (|node::next| (getnode (read var19 var9))) var8)))) (= var6 var15)) (= var5 var13)) (= var4 var11)) (= var3 var9)) (= var2 var8))) (and (not (= nullAddr var17)) (and (and (and (and (and (= var18 (newHeap (alloc var24 (O_node var1)))) (= var14 var23)) (= var12 var22)) (= var10 var21)) (= var16 var20)) (= var17 (newAddr (alloc var24 (O_node var1))))))) (<= 0 (+ (+ var22 (- 1)) (- 1)))) (= var0 (+ var5 (- 1)))))) (inv_main570_3 var7 var6 var0 var4 var2))))
(assert (forall ((var0 node) (var1 Addr) (var2 Int) (var3 Int) (var4 Heap) (var5 Addr) (var6 Int) (var7 Int) (var8 Int) (var9 Int) (var10 Addr) (var11 Heap) (var12 Heap) (var13 Int) (var14 Heap)) (or (not (and (inv_main619_3 var14 var13) (and (and (and (and (and (= var12 (write var11 var10 (O_node (node var10 (|node::prev| (getnode (read var11 var10))))))) (= var9 var8)) (= var7 var6)) (= var5 var10)) (and (and (and (= var4 (write var12 var5 (O_node (node (|node::next| (getnode (read var12 var5))) var5)))) (= var3 var9)) (= var2 var7)) (= var1 var5))) (and (not (= nullAddr var10)) (and (and (and (= var11 (newHeap (alloc var14 (O_node var0)))) (= var8 var13)) (= var6 var13)) (= var10 (newAddr (alloc var14 (O_node var0))))))))) (inv_main570_3 var4 var3 var2 var1 var1))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Int) (var5 Int) (var6 Heap) (var7 Addr) (var8 Int) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Int) (var18 Int) (var19 Heap) (var20 Heap) (var21 Int) (var22 Addr) (var23 Addr) (var24 Int) (var25 Int) (var26 Heap)) (or (not (and (inv_main570_3 var26 var25 var24 var23 var22) (and (and (and (not (= var21 0)) (and (and (and (and (and (= var20 var19) (= var18 var17)) (= var16 var15)) (= var14 var13)) (= var12 var11)) (= var10 (|node::next| (getnode (read var19 var13)))))) (and (and (and (and (= var19 var9) (= var17 var8)) (= var15 var7)) (= var13 var7)) (= var11 (|node::prev| (getnode (read var9 var7)))))) (and (and (not (<= 0 (+ (+ var24 (- 1)) (- 1)))) (and (and (and (and (= var6 (write var26 var23 (O_node (node var22 (|node::prev| (getnode (read var26 var23))))))) (= var5 var25)) (= var4 var24)) (= var3 var23)) (= var2 var22))) (and (and (and (and (= var9 (write var6 var2 (O_node (node (|node::next| (getnode (read var6 var2))) var3)))) (= var8 var5)) (= var1 var4)) (= var0 var3)) (= var7 var2)))))) (inv_main588_31 var20 var18 var16 var14 var12 var10))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Int) (var6 Heap)) (or (not (inv_main574_7 var6 var5 var4 var3 var2 var1 var0)) (inv_main574_7 var6 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 node) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Int) (var11 Int) (var12 Heap)) (or (not (and (inv_main570_3 var12 var11 var10 var9 var8) (and (and (and (= nullAddr var7) (and (and (and (and (and (= var6 (newHeap (alloc var12 (O_node var5)))) (= var4 var11)) (= var3 var10)) (= var2 var9)) (= var1 var8)) (= var7 (newAddr (alloc var12 (O_node var5)))))) (<= 0 (+ (+ var10 (- 1)) (- 1)))) (= var0 1)))) (inv_main574_7 var6 var4 var3 var2 var1 var7 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Heap)) (or (not (inv_main566_5 var4 var3 var2 var1 var0)) (inv_main566_5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 node) (var4 Heap) (var5 Addr) (var6 Int) (var7 Heap)) (or (not (and (inv_main619_3 var7 var6) (and (and (= nullAddr var5) (and (and (and (= var4 (newHeap (alloc var7 (O_node var3)))) (= var2 var6)) (= var1 var6)) (= var5 (newAddr (alloc var7 (O_node var3)))))) (= var0 1)))) (inv_main566_5 var4 var2 var1 var5 var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Int) (var6 Heap)) (or (not (and (inv_main599_33 var6 var5 var4 var3 var2 var1) (= var0 (write var6 var3 defObj)))) (inv_main_21 var0 var5 var4 var3 var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap) (var6 Int) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Int) (var12 Heap)) (or (not (and (inv_main606_10 var12 var11 var10 var9 var8 var7) (and (= var6 0) (and (and (and (and (and (= var5 (write var12 var8 defObj)) (= var4 var11)) (= var3 var10)) (= var2 var9)) (= var1 var8)) (= var0 var7))))) (inv_main611_12 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap)) (not (and (inv_main588_31 var5 var4 var3 var2 var1 var0) (and (not (= var2 nullAddr)) (= (read var5 var2) defObj))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap)) (not (and (inv_main590_33 var5 var4 var3 var2 var1 var0) (and (not (= var0 nullAddr)) (= (read var5 var0) defObj))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap)) (not (and (inv_main_18 var5 var4 var3 var2 var1 var0) (and (not (= var1 nullAddr)) (= (read var5 var1) defObj))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap)) (not (and (inv_main593_12 var5 var4 var3 var2 var1 var0) (and (not (= var1 nullAddr)) (= (read var5 var1) defObj))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap)) (not (and (inv_main_19 var5 var4 var3 var2 var1 var0) (and (not (= var0 nullAddr)) (= (read var5 var0) defObj))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap)) (not (and (inv_main597_38 var5 var4 var3 var2 var1 var0) (and (not (= var0 nullAddr)) (= (read var5 var0) defObj))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap)) (not (and (inv_main599_33 var5 var4 var3 var2 var1 var0) (and (not (= var2 nullAddr)) (= (read var5 var2) defObj))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap)) (not (and (inv_main_21 var5 var4 var3 var2 var1 var0) (and (not (= var1 nullAddr)) (= (read var5 var1) defObj))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap)) (not (and (inv_main602_12 var5 var4 var3 var2 var1 var0) (and (not (= var1 nullAddr)) (= (read var5 var1) defObj))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap)) (not (and (inv_main_22 var5 var4 var3 var2 var1 var0) (and (not (= var2 nullAddr)) (= (read var5 var2) defObj))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap)) (not (and (inv_main606_10 var5 var4 var3 var2 var1 var0) (and (not (= var1 nullAddr)) (= (read var5 var1) defObj))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap)) (not (and (inv_main608_33 var5 var4 var3 var2 var1 var0) (and (not (= var2 nullAddr)) (= (read var5 var2) defObj))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap)) (not (and (inv_main_24 var5 var4 var3 var2 var1 var0) (and (not (= var0 nullAddr)) (= (read var5 var0) defObj))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap)) (not (and (inv_main611_12 var5 var4 var3 var2 var1 var0) (and (not (= var0 nullAddr)) (= (read var5 var0) defObj))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap)) (not (and (inv_main_25 var5 var4 var3 var2 var1 var0) (and (not (= var2 nullAddr)) (= (read var5 var2) defObj))))))
(check-sat)
