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
   (node (|node::data| Int) (|node::next| Addr) (|node::prev| Addr))
  )
))
(declare-fun inv_main (Heap Int Int Int Int Addr) Bool)
(declare-fun inv_main578_5 (Heap Int Int Int Int Addr Int) Bool)
(declare-fun inv_main583_3 (Heap Int Int Int Int Addr Addr) Bool)
(declare-fun inv_main587_7 (Heap Int Int Int Int Addr Addr Addr Int) Bool)
(declare-fun inv_main602_3 (Heap Int Int) Bool)
(declare-fun inv_main604_3 (Heap Int Int Addr Addr Int) Bool)
(declare-fun inv_main_11 (Heap Int Int Int Int Addr Addr Addr) Bool)
(declare-fun inv_main_12 (Heap Int Int Int Int Addr Addr Addr) Bool)
(declare-fun inv_main_15 (Heap Int Int Int Int Addr Addr) Bool)
(declare-fun inv_main_18 (Heap Int Int Addr Addr Int) Bool)
(declare-fun inv_main_19 (Heap Int Int Addr Addr Int) Bool)
(declare-fun inv_main_2 (Heap Int Int Int Int Addr) Bool)
(declare-fun inv_main_21 (Heap Int Int Addr Addr Int) Bool)
(declare-fun inv_main_26 (Heap Int Int Addr Addr Int) Bool)
(declare-fun inv_main_27 (Heap Int Int Addr Addr Int) Bool)
(declare-fun inv_main_3 (Heap Int Int Int Int Addr) Bool)
(declare-fun inv_main_5 (Heap Int Int Int Int Addr Addr) Bool)
(declare-fun inv_main_7 (Heap Int Int Int Int Addr Addr Addr) Bool)
(assert (forall ((var0 Int) (var1 Int) (var2 Heap)) (or (not (and (and (= var2 emptyHeap) (= var1 5)) (= var0 1))) (inv_main602_3 var2 var1 var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Heap)) (or (not (and (inv_main_5 var7 var6 var5 var4 var3 var2 var1) (and (and (is-O_node (read var7 var2)) (is-O_node (read var7 var2))) (= var0 (write var7 var2 (O_node (node (|node::data| (getnode (read var7 var2))) var1 (|node::prev| (getnode (read var7 var2)))))))))) (inv_main_15 var0 var6 var5 var4 var3 var2 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Int) (var6 Int) (var7 Int) (var8 Heap)) (or (not (inv_main587_7 var8 var7 var6 var5 var4 var3 var2 var1 var0)) (inv_main587_7 var8 var7 var6 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 node) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Int) (var13 Int) (var14 Int) (var15 Int) (var16 Heap)) (or (not (and (inv_main583_3 var16 var15 var14 var13 var12 var11 var10) (and (and (and (= nullAddr var9) (and (and (and (and (and (and (and (= var8 (newHeap (alloc var16 (O_node var7)))) (= var6 var15)) (= var5 var14)) (= var4 var13)) (= var3 var12)) (= var2 var11)) (= var1 var10)) (= var9 (newAddr (alloc var16 (O_node var7)))))) (<= 0 (+ (+ var13 (- 1)) (- 1)))) (= var0 1)))) (inv_main587_7 var8 var6 var5 var4 var3 var2 var1 var9 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Int) (var6 Int) (var7 Int) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Int) (var13 Int) (var14 Int) (var15 Int) (var16 Heap)) (or (not (and (inv_main_12 var16 var15 var14 var13 var12 var11 var10 var9) (and (and (and (is-O_node (read var16 var10)) (is-O_node (read var16 var10))) (and (and (and (and (and (and (and (= var8 (write var16 var10 (O_node (node (|node::data| (getnode (read var16 var10))) (|node::next| (getnode (read var16 var10))) var9)))) (= var7 var15)) (= var6 var14)) (= var5 var13)) (= var4 var12)) (= var3 var11)) (= var2 var10)) (= var1 var9))) (= var0 (+ var5 (- 1)))))) (inv_main583_3 var8 var7 var6 var0 var4 var3 var1))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Int) (var4 Int) (var5 Heap) (var6 Addr) (var7 Int) (var8 Int) (var9 Int) (var10 Int) (var11 Heap)) (or (not (and (inv_main_3 var11 var10 var9 var8 var7 var6) (and (and (is-O_node (read var11 var6)) (is-O_node (read var11 var6))) (and (and (and (and (and (= var5 (write var11 var6 (O_node (node var7 (|node::next| (getnode (read var11 var6))) (|node::prev| (getnode (read var11 var6))))))) (= var4 var10)) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var0 var6))))) (inv_main583_3 var5 var4 var3 var2 var1 var0 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Int) (var4 node) (var5 Heap) (var6 Addr) (var7 Int) (var8 Int) (var9 Heap)) (or (not (and (inv_main602_3 var9 var8 var7) (and (not (= nullAddr var6)) (and (and (and (and (and (= var5 (newHeap (alloc var9 (O_node var4)))) (= var3 var8)) (= var2 var7)) (= var1 var8)) (= var0 var7)) (= var6 (newAddr (alloc var9 (O_node var4)))))))) (inv_main var5 var3 var2 var1 var0 var6))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Heap)) (or (not (and (inv_main_26 var5 var4 var3 var2 var1 var0) (and (is-O_node (read var5 var1)) (= var0 (|node::data| (getnode (read var5 var1))))))) (inv_main_27 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Heap)) (or (not (inv_main578_5 var6 var5 var4 var3 var2 var1 var0)) (inv_main578_5 var6 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Int) (var4 Int) (var5 node) (var6 Heap) (var7 Addr) (var8 Int) (var9 Int) (var10 Heap)) (or (not (and (inv_main602_3 var10 var9 var8) (and (and (= nullAddr var7) (and (and (and (and (and (= var6 (newHeap (alloc var10 (O_node var5)))) (= var4 var9)) (= var3 var8)) (= var2 var9)) (= var1 var8)) (= var7 (newAddr (alloc var10 (O_node var5)))))) (= var0 1)))) (inv_main578_5 var6 var4 var3 var2 var1 var7 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 node) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Int) (var12 Int) (var13 Int) (var14 Int) (var15 Heap)) (or (not (and (inv_main583_3 var15 var14 var13 var12 var11 var10 var9) (and (and (not (= nullAddr var8)) (and (and (and (and (and (and (and (= var7 (newHeap (alloc var15 (O_node var6)))) (= var5 var14)) (= var4 var13)) (= var3 var12)) (= var2 var11)) (= var1 var10)) (= var0 var9)) (= var8 (newAddr (alloc var15 (O_node var6)))))) (<= 0 (+ (+ var12 (- 1)) (- 1)))))) (inv_main_7 var7 var5 var4 var3 var2 var1 var0 var8))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Heap)) (or (not (and (inv_main_2 var6 var5 var4 var3 var2 var1) (and (and (is-O_node (read var6 var1)) (is-O_node (read var6 var1))) (= var0 (write var6 var1 (O_node (node (|node::data| (getnode (read var6 var1))) (|node::next| (getnode (read var6 var1))) var1))))))) (inv_main_3 var0 var5 var4 var3 var2 var1))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Int) (var5 Int) (var6 Heap) (var7 Addr) (var8 Int) (var9 Addr) (var10 Addr) (var11 Int) (var12 Int) (var13 Heap) (var14 Int) (var15 Addr) (var16 Addr) (var17 Int) (var18 Int) (var19 Heap)) (or (not (and (inv_main_18 var19 var18 var17 var16 var15 var14) (and (and (and (is-O_node (read var19 var15)) (and (and (and (and (and (and (= var13 var19) (= var12 var18)) (= var11 var17)) (= var10 var16)) (= var9 var15)) (= var8 var14)) (= var7 (|node::prev| (getnode (read var19 var15)))))) (and (and (and (and (and (= var6 var13) (= var5 var12)) (= var4 var11)) (= var3 nullAddr)) (= var2 var7)) (= var1 var8))) (= var0 (+ var1 (- 1)))))) (inv_main_26 var6 var5 var4 var3 var2 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Int) (var5 Int) (var6 Heap) (var7 Addr) (var8 Int) (var9 Addr) (var10 Addr) (var11 Int) (var12 Int) (var13 Heap) (var14 Addr) (var15 Int) (var16 Addr) (var17 Addr) (var18 Int) (var19 Int) (var20 Heap)) (or (not (and (inv_main_27 var20 var19 var18 var17 var16 var15) (and (and (not (= var14 nullAddr)) (and (and (is-O_node (read var20 var16)) (and (and (and (and (and (and (= var13 var20) (= var12 var19)) (= var11 var18)) (= var10 var17)) (= var9 var16)) (= var8 var15)) (= var7 (|node::prev| (getnode (read var20 var16)))))) (and (and (and (and (and (and (= var6 (write var13 var9 defObj)) (= var5 var12)) (= var4 var11)) (= var3 var10)) (= var2 var9)) (= var1 var8)) (= var14 var7)))) (= var0 (+ var1 (- 1)))))) (inv_main_26 var6 var5 var4 var3 var14 var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Heap)) (or (not (and (inv_main var6 var5 var4 var3 var2 var1) (and (and (is-O_node (read var6 var1)) (is-O_node (read var6 var1))) (= var0 (write var6 var1 (O_node (node (|node::data| (getnode (read var6 var1))) var1 (|node::prev| (getnode (read var6 var1)))))))))) (inv_main_2 var0 var5 var4 var3 var2 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Heap)) (or (not (and (inv_main604_3 var5 var4 var3 var2 var1 var0) (and (is-O_node (read var5 var1)) (= var3 (|node::data| (getnode (read var5 var1))))))) (inv_main_19 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Int) (var6 Int) (var7 Int) (var8 Heap)) (or (not (and (inv_main_7 var8 var7 var6 var5 var4 var3 var2 var1) (and (and (is-O_node (read var8 var1)) (is-O_node (read var8 var1))) (= var0 (write var8 var1 (O_node (node (|node::data| (getnode (read var8 var1))) var2 (|node::prev| (getnode (read var8 var1)))))))))) (inv_main_11 var0 var7 var6 var5 var4 var3 var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Heap)) (or (not (and (inv_main583_3 var6 var5 var4 var3 var2 var1 var0) (not (<= 0 (+ (+ var3 (- 1)) (- 1)))))) (inv_main_5 var6 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Int) (var6 Int) (var7 Int) (var8 Heap)) (or (not (and (inv_main_11 var8 var7 var6 var5 var4 var3 var2 var1) (and (and (is-O_node (read var8 var1)) (is-O_node (read var8 var1))) (= var0 (write var8 var1 (O_node (node var4 (|node::next| (getnode (read var8 var1))) (|node::prev| (getnode (read var8 var1)))))))))) (inv_main_12 var0 var7 var6 var5 var4 var3 var2 var1))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Int) (var4 Int) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Int) (var9 Addr) (var10 Addr) (var11 Int) (var12 Int) (var13 Heap)) (or (not (and (inv_main_21 var13 var12 var11 var10 var9 var8) (and (and (not (= var7 var6)) (and (is-O_node (read var13 var9)) (and (and (and (and (and (and (= var5 var13) (= var4 var12)) (= var3 var11)) (= var6 var10)) (= var2 var9)) (= var1 var8)) (= var7 (|node::next| (getnode (read var13 var9))))))) (= var0 (+ var1 1))))) (inv_main604_3 var5 var4 var3 var6 var7 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Int) (var11 Int) (var12 Int) (var13 Int) (var14 Heap)) (or (not (and (inv_main_15 var14 var13 var12 var11 var10 var9 var8) (and (and (and (is-O_node (read var14 var8)) (is-O_node (read var14 var8))) (and (and (and (and (and (and (= var7 (write var14 var8 (O_node (node (|node::data| (getnode (read var14 var8))) (|node::next| (getnode (read var14 var8))) var9)))) (= var6 var13)) (= var5 var12)) (= var4 var11)) (= var3 var10)) (= var2 var9)) (= var1 var8))) (= var0 1)))) (inv_main604_3 var7 var6 var5 var1 var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Int) (var4 Int) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Int) (var9 Addr) (var10 Addr) (var11 Int) (var12 Int) (var13 Heap)) (or (not (and (inv_main_21 var13 var12 var11 var10 var9 var8) (and (and (= var7 var6) (and (is-O_node (read var13 var9)) (and (and (and (and (and (and (= var5 var13) (= var4 var12)) (= var3 var11)) (= var6 var10)) (= var2 var9)) (= var1 var8)) (= var7 (|node::next| (getnode (read var13 var9))))))) (= var0 (+ var1 1))))) (inv_main_18 var5 var4 var3 var6 var7 var0))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Addr) (var3 Addr) (var4 Int) (var5 Int) (var6 Heap)) (or (not (and (inv_main_19 var6 var5 var4 var3 var2 var1) (and (and (is-O_node (read var6 var2)) (is-O_node (read var6 var2))) (= var0 (write var6 var2 (O_node (node var1 (|node::next| (getnode (read var6 var2))) (|node::prev| (getnode (read var6 var2)))))))))) (inv_main_21 var0 var5 var4 var3 var2 var1))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Int) (var4 Int) (var5 Heap)) (not (and (inv_main var5 var4 var3 var2 var1 var0) (not (is-O_node (read var5 var0)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Int) (var4 Int) (var5 Heap)) (not (and (inv_main var5 var4 var3 var2 var1 var0) (and (is-O_node (read var5 var0)) (not (is-O_node (read var5 var0))))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Int) (var4 Int) (var5 Heap)) (not (and (inv_main_2 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var5 var0)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Int) (var4 Int) (var5 Heap)) (not (and (inv_main_2 var5 var4 var3 var2 var1 var0) (and (is-O_node (read var5 var0)) (not (is-O_node (read var5 var0))))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Int) (var4 Int) (var5 Heap)) (not (and (inv_main_3 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var5 var0)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Int) (var4 Int) (var5 Heap)) (not (and (inv_main_3 var5 var4 var3 var2 var1 var0) (and (is-O_node (read var5 var0)) (not (is-O_node (read var5 var0))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Heap)) (not (and (inv_main_7 var7 var6 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var7 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Heap)) (not (and (inv_main_7 var7 var6 var5 var4 var3 var2 var1 var0) (and (is-O_node (read var7 var0)) (not (is-O_node (read var7 var0))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Heap)) (not (and (inv_main_11 var7 var6 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var7 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Heap)) (not (and (inv_main_11 var7 var6 var5 var4 var3 var2 var1 var0) (and (is-O_node (read var7 var0)) (not (is-O_node (read var7 var0))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Heap)) (not (and (inv_main_12 var7 var6 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var7 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Heap)) (not (and (inv_main_12 var7 var6 var5 var4 var3 var2 var1 var0) (and (is-O_node (read var7 var1)) (not (is-O_node (read var7 var1))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Heap)) (not (and (inv_main_5 var6 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var6 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Heap)) (not (and (inv_main_5 var6 var5 var4 var3 var2 var1 var0) (and (is-O_node (read var6 var1)) (not (is-O_node (read var6 var1))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Heap)) (not (and (inv_main_15 var6 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var6 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Heap)) (not (and (inv_main_15 var6 var5 var4 var3 var2 var1 var0) (and (is-O_node (read var6 var0)) (not (is-O_node (read var6 var0))))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Heap)) (not (and (inv_main604_3 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var5 var1)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Heap)) (not (and (inv_main_19 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var5 var1)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Heap)) (not (and (inv_main_19 var5 var4 var3 var2 var1 var0) (and (is-O_node (read var5 var1)) (not (is-O_node (read var5 var1))))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Heap)) (not (and (inv_main_21 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var5 var1)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Heap)) (not (and (inv_main_18 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var5 var1)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Heap)) (not (and (inv_main_26 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var5 var1)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Heap)) (not (and (inv_main_27 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var5 var1)))))))
(check-sat)
