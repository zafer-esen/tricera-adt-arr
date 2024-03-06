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
   (node (|node::data| Int) (|node::next| Addr) (|node::prev| Addr))
  )
))
(declare-fun inv_main586_3 (Heap Int Int Int Int Addr) Bool)
(declare-fun inv_main590_7 (Heap Int Int Int Int Addr Addr Int) Bool)
(declare-fun inv_main595_8 (Heap Int Int Int Int Addr Addr) Bool)
(declare-fun inv_main609_5 (Heap Int Int Addr Int Int Addr Addr) Bool)
(declare-fun inv_main621_3 (Heap Int Int) Bool)
(declare-fun inv_main624_5 (Heap Int Int Addr Int Int) Bool)
(declare-fun inv_main_15 (Heap Int Int Addr Int Int Addr Addr) Bool)
(declare-fun inv_main_17 (Heap Int Int Addr Int Int Addr Addr) Bool)
(declare-fun inv_main_2 (Heap Int Int Int Int Addr Addr) Bool)
(declare-fun inv_main_4 (Heap Int Int Int Int Addr Addr) Bool)
(declare-fun inv_main_5 (Heap Int Int Int Int Addr Addr) Bool)
(assert (forall ((var0 Int) (var1 Int) (var2 Heap)) (or (not (and (and (= var2 emptyHeap) (= var1 2)) (= var0 1))) (inv_main621_3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Int) (var5 Int) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Int) (var10 Int) (var11 Addr) (var12 Int) (var13 Int) (var14 Heap) (var15 Int) (var16 Addr) (var17 Addr) (var18 Int) (var19 Int) (var20 Addr) (var21 Int) (var22 Int) (var23 Heap)) (or (not (and (inv_main_15 var23 var22 var21 var20 var19 var18 var17 var16) (and (and (and (<= 0 (+ var15 (- 1))) (and (and (and (is-O_node (read var23 var17)) (is-O_node (read var23 var17))) (and (and (and (and (and (and (and (= var14 (write var23 var17 (O_node (node (|node::data| (getnode (read var23 var17))) nullAddr (|node::prev| (getnode (read var23 var17))))))) (= var13 var22)) (= var12 var21)) (= var11 var20)) (= var10 var19)) (= var9 var18)) (= var8 var17)) (= var7 var16))) (and (and (and (and (and (= var6 (write var14 var7 defObj)) (= var5 var13)) (= var4 var12)) (= var3 var11)) (= var15 var10)) (= var2 var9)))) (= var1 (+ var15 (- 1)))) (= var0 3)))) (inv_main624_5 var6 var5 var4 var3 var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Int) (var5 Int) (var6 Heap) (var7 Int) (var8 Int) (var9 Addr) (var10 Int) (var11 Int) (var12 Heap) (var13 Int) (var14 Int) (var15 Int) (var16 Addr) (var17 Int) (var18 Int) (var19 Heap)) (or (not (and (inv_main624_5 var19 var18 var17 var16 var15 var14) (and (and (and (<= 0 (+ var13 (- 1))) (and (and (and (is-O_node (read var19 var16)) (= nullAddr (|node::next| (getnode (read var19 var16))))) (and (and (and (and (and (= var12 (write var19 var16 defObj)) (= var11 var18)) (= var10 var17)) (= var9 var16)) (= var8 var15)) (= var7 var14))) (and (and (and (and (and (= var6 var12) (= var5 var11)) (= var4 var10)) (= var3 nullAddr)) (= var13 var8)) (= var2 var7)))) (= var1 (+ var13 (- 1)))) (= var0 3)))) (inv_main624_5 var6 var5 var4 var3 var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Heap)) (or (not (and (inv_main586_3 var7 var6 var5 var4 var3 var2) (and (and (and (<= 0 (+ var6 (- 1))) (not (<= 0 (+ var4 (- 1))))) (= var1 (+ var6 (- 1)))) (= var0 3)))) (inv_main624_5 var7 var6 var5 var2 var1 var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Heap)) (or (not (and (inv_main_2 var7 var6 var5 var4 var3 var2 var1) (and (and (is-O_node (read var7 var1)) (is-O_node (read var7 var1))) (= var0 (write var7 var1 (O_node (node var3 (|node::next| (getnode (read var7 var1))) (|node::prev| (getnode (read var7 var1)))))))))) (inv_main_4 var0 var6 var5 var4 var3 var2 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Int) (var11 Int) (var12 Int) (var13 Int) (var14 Heap)) (or (not (and (inv_main595_8 var14 var13 var12 var11 var10 var9 var8) (and (and (and (is-O_node (read var14 var9)) (is-O_node (read var14 var9))) (and (and (and (and (and (and (= var7 (write var14 var9 (O_node (node (|node::data| (getnode (read var14 var9))) (|node::next| (getnode (read var14 var9))) var8)))) (= var6 var13)) (= var5 var12)) (= var4 var11)) (= var3 var10)) (= var2 var9)) (= var1 var8))) (= var0 (+ var4 (- 1)))))) (inv_main586_3 var7 var6 var5 var0 var3 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Int) (var11 Int) (var12 Int) (var13 Int) (var14 Heap)) (or (not (and (inv_main_5 var14 var13 var12 var11 var10 var9 var8) (and (and (and (= var7 nullAddr) (and (is-O_node (read var14 var8)) (is-O_node (read var14 var8)))) (and (and (and (and (and (and (= var6 (write var14 var8 (O_node (node (|node::data| (getnode (read var14 var8))) (|node::next| (getnode (read var14 var8))) nullAddr)))) (= var5 var13)) (= var4 var12)) (= var3 var11)) (= var2 var10)) (= var7 var9)) (= var1 var8))) (= var0 (+ var3 (- 1)))))) (inv_main586_3 var6 var5 var4 var0 var2 var1))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Heap)) (or (not (and (inv_main621_3 var3 var2 var1) (= var0 nullAddr))) (inv_main586_3 var3 var2 var1 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Int) (var4 Int) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Int) (var10 Int) (var11 Int) (var12 Int) (var13 Heap)) (or (not (and (inv_main_5 var13 var12 var11 var10 var9 var8 var7) (and (and (not (= var6 nullAddr)) (and (is-O_node (read var13 var7)) (is-O_node (read var13 var7)))) (and (and (and (and (and (and (= var5 (write var13 var7 (O_node (node (|node::data| (getnode (read var13 var7))) (|node::next| (getnode (read var13 var7))) nullAddr)))) (= var4 var12)) (= var3 var11)) (= var2 var10)) (= var1 var9)) (= var6 var8)) (= var0 var7))))) (inv_main595_8 var5 var4 var3 var2 var1 var6 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Int) (var4 Int) (var5 node) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Int) (var10 Int) (var11 Int) (var12 Int) (var13 Heap)) (or (not (and (inv_main586_3 var13 var12 var11 var10 var9 var8) (and (and (not (= nullAddr var7)) (and (and (and (and (and (and (= var6 (newHeap (alloc var13 (O_node var5)))) (= var4 var12)) (= var3 var11)) (= var2 var10)) (= var1 var9)) (= var0 var8)) (= var7 (newAddr (alloc var13 (O_node var5)))))) (<= 0 (+ var10 (- 1)))))) (inv_main_2 var6 var4 var3 var2 var1 var0 var7))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Heap)) (or (not (and (inv_main_4 var7 var6 var5 var4 var3 var2 var1) (and (and (is-O_node (read var7 var1)) (is-O_node (read var7 var1))) (= var0 (write var7 var1 (O_node (node (|node::data| (getnode (read var7 var1))) var2 (|node::prev| (getnode (read var7 var1)))))))))) (inv_main_5 var0 var6 var5 var4 var3 var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Addr) (var5 Int) (var6 Int) (var7 Heap)) (or (not (and (inv_main609_5 var7 var6 var5 var4 var3 var2 var1 var0) (and (is-O_node (read var7 var0)) (not (= (|node::next| (getnode (read var7 var0))) nullAddr))))) (inv_main_17 var7 var6 var5 var4 var3 var2 var0 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Addr) (var5 Int) (var6 Int) (var7 Heap)) (or (not (and (inv_main609_5 var7 var6 var5 var4 var3 var2 var1 var0) (and (is-O_node (read var7 var0)) (= (|node::next| (getnode (read var7 var0))) nullAddr)))) (inv_main_15 var7 var6 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Heap)) (or (not (inv_main590_7 var7 var6 var5 var4 var3 var2 var1 var0)) (inv_main590_7 var7 var6 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 node) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Int) (var11 Int) (var12 Int) (var13 Int) (var14 Heap)) (or (not (and (inv_main586_3 var14 var13 var12 var11 var10 var9) (and (and (and (= nullAddr var8) (and (and (and (and (and (and (= var7 (newHeap (alloc var14 (O_node var6)))) (= var5 var13)) (= var4 var12)) (= var3 var11)) (= var2 var10)) (= var1 var9)) (= var8 (newAddr (alloc var14 (O_node var6)))))) (<= 0 (+ var11 (- 1)))) (= var0 1)))) (inv_main590_7 var7 var5 var4 var3 var2 var1 var8 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Addr) (var6 Int) (var7 Int) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Int) (var12 Int) (var13 Addr) (var14 Int) (var15 Int) (var16 Heap)) (or (not (and (inv_main_17 var16 var15 var14 var13 var12 var11 var10 var9) (and (is-O_node (read var16 var9)) (and (and (and (and (and (and (and (and (= var8 var16) (= var7 var15)) (= var6 var14)) (= var5 var13)) (= var4 var12)) (= var3 var11)) (= var2 var10)) (= var1 var9)) (= var0 (|node::next| (getnode (read var16 var9)))))))) (inv_main609_5 var8 var7 var6 var5 var4 var3 var2 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Addr) (var4 Int) (var5 Int) (var6 Heap) (var7 Int) (var8 Int) (var9 Addr) (var10 Int) (var11 Int) (var12 Heap)) (or (not (and (inv_main624_5 var12 var11 var10 var9 var8 var7) (and (and (and (and (and (and (and (= var6 var12) (= var5 var11)) (= var4 var10)) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var0 nullAddr)) (and (is-O_node (read var12 var9)) (not (= nullAddr (|node::next| (getnode (read var12 var9))))))))) (inv_main609_5 var6 var5 var4 var3 var2 var1 var0 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Heap)) (not (and (inv_main_2 var6 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var6 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Heap)) (not (and (inv_main_2 var6 var5 var4 var3 var2 var1 var0) (and (is-O_node (read var6 var0)) (not (is-O_node (read var6 var0))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Heap)) (not (and (inv_main_4 var6 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var6 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Heap)) (not (and (inv_main_4 var6 var5 var4 var3 var2 var1 var0) (and (is-O_node (read var6 var0)) (not (is-O_node (read var6 var0))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Heap)) (not (and (inv_main_5 var6 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var6 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Heap)) (not (and (inv_main_5 var6 var5 var4 var3 var2 var1 var0) (and (is-O_node (read var6 var0)) (not (is-O_node (read var6 var0))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Heap)) (not (and (inv_main595_8 var6 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var6 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Heap)) (not (and (inv_main595_8 var6 var5 var4 var3 var2 var1 var0) (and (is-O_node (read var6 var1)) (not (is-O_node (read var6 var1))))))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Int) (var4 Int) (var5 Heap)) (not (and (inv_main624_5 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var5 var2)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Addr) (var5 Int) (var6 Int) (var7 Heap)) (not (and (inv_main609_5 var7 var6 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var7 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Addr) (var5 Int) (var6 Int) (var7 Heap)) (not (and (inv_main_17 var7 var6 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var7 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Addr) (var5 Int) (var6 Int) (var7 Heap)) (not (and (inv_main_15 var7 var6 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var7 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Addr) (var5 Int) (var6 Int) (var7 Heap)) (not (and (inv_main_15 var7 var6 var5 var4 var3 var2 var1 var0) (and (is-O_node (read var7 var1)) (not (is-O_node (read var7 var1))))))))
(check-sat)
