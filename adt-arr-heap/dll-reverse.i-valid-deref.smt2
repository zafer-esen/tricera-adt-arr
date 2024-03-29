(set-logic HORN)
(set-info :source |
    Benchmark: C_VC
    Output by Princess (http://www.philipp.ruemmer.org/princess.shtml)
|)
(set-info :status sat)
(declare-heap Heap Addr HeapObject
 defObj
 ((HeapObject 0) (TDLL 0)) (
  (
   (O_Int (getInt Int))
   (O_UInt (getUInt Int))
   (O_Addr (getAddr Addr))
   (O_AddrRange (getAddrRange AddrRange))
   (O_TDLL (getTDLL TDLL))
   (defObj)
  )
  (
   (TDLL (|TDLL::next| Addr) (|TDLL::prev| Addr) (|TDLL::data| Int))
  )
))
(declare-fun inv_main (Heap Addr) Bool)
(declare-fun inv_main1004_36 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main1019_3 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main1022_3 (Heap Addr Addr) Bool)
(declare-fun inv_main1029_3 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main1047_7 (Heap Addr Addr Addr Int Int) Bool)
(declare-fun inv_main1052_7_42 (Heap Addr Addr Addr Int Int) Bool)
(declare-fun inv_main996_2 (Heap) Bool)
(declare-fun inv_main996_2_1 (Heap Addr) Bool)
(declare-fun inv_main_10 (Heap Addr Addr) Bool)
(declare-fun inv_main_14 (Heap Addr Addr) Bool)
(declare-fun inv_main_17 (Heap Addr Addr) Bool)
(declare-fun inv_main_2 (Heap Addr) Bool)
(declare-fun inv_main_20 (Heap Addr Addr) Bool)
(declare-fun inv_main_22 (Heap Addr Addr) Bool)
(declare-fun inv_main_23 (Heap Addr Addr) Bool)
(declare-fun inv_main_24 (Heap Addr Addr) Bool)
(declare-fun inv_main_25 (Heap Addr Addr) Bool)
(declare-fun inv_main_28 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main_29 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main_33 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main_35 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main_38 (Heap Addr Addr Addr Int Int) Bool)
(declare-fun inv_main_41 (Heap Addr Addr Addr Int Int) Bool)
(declare-fun inv_main_47 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main_6 (Heap Addr Addr) Bool)
(declare-fun inv_main_7 (Heap Addr Addr) Bool)
(declare-fun inv_main_8 (Heap Addr Addr) Bool)
(declare-fun inv_main_9 (Heap Addr Addr) Bool)
(assert (forall ((var0 Heap)) (or (not (= var0 emptyHeap)) (inv_main996_2 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Int) (var8 Int) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Heap)) (or (not (and (inv_main1052_7_42 var12 var11 var10 var9 var8 var7) (and (is-O_TDLL (read var12 var10)) (and (and (and (and (and (and (= var6 var12) (= var5 var11)) (= var4 var10)) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var0 (|TDLL::next| (getTDLL (read var12 var10)))))))) (inv_main_41 var6 var5 var0 var3 var2 var1))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Int) (var7 Int) (var8 Int) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Heap)) (or (not (and (inv_main_38 var12 var11 var10 var9 var8 var7) (and (and (not (= var6 2)) (is-O_TDLL (read var12 var10))) (and (and (and (and (and (and (= var5 var12) (= var4 var11)) (= var3 var10)) (= var2 var9)) (= var1 var8)) (= var0 var7)) (= var6 (|TDLL::data| (getTDLL (read var12 var10)))))))) (inv_main_41 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main_23 var6 var5 var4) (and (is-O_TDLL (read var6 var4)) (and (and (and (= var3 var6) (= var2 var5)) (= var1 var4)) (= var0 (|TDLL::next| (getTDLL (read var6 var4)))))))) (inv_main_24 var3 var2 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Int) (var8 Int) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Heap)) (or (not (and (inv_main_41 var12 var11 var10 var9 var8 var7) (and (is-O_TDLL (read var12 var10)) (and (and (and (and (and (and (= var6 var12) (= var5 var11)) (= var4 var10)) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var0 (|TDLL::next| (getTDLL (read var12 var10)))))))) (inv_main_33 var6 var5 var0 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main_29 var9 var8 var7 var6 var5) (and (= var4 nullAddr) (and (and (is-O_TDLL (read var9 var7)) (is-O_TDLL (read var9 var7))) (and (and (and (and (= var3 (write var9 var7 (O_TDLL (TDLL (|TDLL::next| (getTDLL (read var9 var7))) var5 (|TDLL::data| (getTDLL (read var9 var7))))))) (= var2 var8)) (= var1 var7)) (= var0 var6)) (= var4 var5)))))) (inv_main_33 var3 var1 var1 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main_25 var9 var8 var7) (and (and (and (= var6 nullAddr) (and (and (and (= var5 var4) (= var6 var3)) (= var2 var1)) (= var0 nullAddr))) (and (is-O_TDLL (read var9 var7)) (is-O_TDLL (read var9 var7)))) (and (and (= var4 (write var9 var7 (O_TDLL (TDLL (|TDLL::next| (getTDLL (read var9 var7))) (|TDLL::prev| (getTDLL (read var9 var7))) 2)))) (= var3 var8)) (= var1 var7))))) (inv_main_33 var5 var0 var0 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main1022_3 var9 var8 var7) (and (and (and (= var6 nullAddr) (and (and (and (= var5 var4) (= var6 var3)) (= var2 var1)) (= var0 nullAddr))) (and (and (is-O_TDLL (read var9 var7)) (is-O_TDLL (read var9 (|TDLL::next| (getTDLL (read var9 var7)))))) (is-O_TDLL (read var9 (|TDLL::next| (getTDLL (read var9 var7))))))) (and (and (= var4 (write var9 (|TDLL::next| (getTDLL (read var9 var7))) (O_TDLL (TDLL (|TDLL::next| (getTDLL (read var9 (|TDLL::next| (getTDLL (read var9 var7)))))) (|TDLL::prev| (getTDLL (read var9 (|TDLL::next| (getTDLL (read var9 var7)))))) 2)))) (= var3 var8)) (= var1 var7))))) (inv_main_33 var5 var0 var0 var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main1019_3 var4 var3 var2 var1) (and (and (is-O_TDLL (read var4 var2)) (is-O_TDLL (read var4 var2))) (= var0 (write var4 var2 (O_TDLL (TDLL var1 (|TDLL::prev| (getTDLL (read var4 var2))) (|TDLL::data| (getTDLL (read var4 var2)))))))))) (inv_main_22 var0 var3 var2))))
(assert (forall ((var0 Addr) (var1 TDLL) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Int) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main_9 var9 var8 var7) (and (and (and (and (not (= var6 0)) (and (is-O_TDLL (read var9 var7)) (is-O_TDLL (read var9 var7)))) (and (and (= var5 (write var9 var7 (O_TDLL (TDLL (|TDLL::next| (getTDLL (read var9 var7))) (|TDLL::prev| (getTDLL (read var9 var7))) 0)))) (= var4 var8)) (= var3 var7))) (= var2 (newHeap (alloc var5 (O_TDLL var1))))) (= var0 (newAddr (alloc var5 (O_TDLL var1))))))) (inv_main1004_36 var2 var4 var3 var0))))
(assert (forall ((var0 Addr) (var1 TDLL) (var2 Heap) (var3 Addr) (var4 Heap) (var5 Int) (var6 Addr) (var7 Heap)) (or (not (and (inv_main_2 var7 var6) (and (and (and (and (not (= var5 0)) (and (is-O_TDLL (read var7 var6)) (is-O_TDLL (read var7 var6)))) (and (= var4 (write var7 var6 (O_TDLL (TDLL (|TDLL::next| (getTDLL (read var7 var6))) (|TDLL::prev| (getTDLL (read var7 var6))) 0)))) (= var3 var6))) (= var2 (newHeap (alloc var4 (O_TDLL var1))))) (= var0 (newAddr (alloc var4 (O_TDLL var1))))))) (inv_main1004_36 var2 var3 var3 var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Heap)) (or (not (and (inv_main var2 var1) (and (and (is-O_TDLL (read var2 var1)) (is-O_TDLL (read var2 var1))) (= var0 (write var2 var1 (O_TDLL (TDLL (|TDLL::next| (getTDLL (read var2 var1))) nullAddr (|TDLL::data| (getTDLL (read var2 var1)))))))))) (inv_main_2 var0 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main_29 var9 var8 var7 var6 var5) (and (not (= var4 nullAddr)) (and (and (is-O_TDLL (read var9 var7)) (is-O_TDLL (read var9 var7))) (and (and (and (and (= var3 (write var9 var7 (O_TDLL (TDLL (|TDLL::next| (getTDLL (read var9 var7))) var5 (|TDLL::data| (getTDLL (read var9 var7))))))) (= var2 var8)) (= var1 var7)) (= var0 var6)) (= var4 var5)))))) (inv_main_28 var3 var2 var4 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main_25 var9 var8 var7) (and (and (and (not (= var6 nullAddr)) (and (and (and (= var5 var4) (= var6 var3)) (= var2 var1)) (= var0 nullAddr))) (and (is-O_TDLL (read var9 var7)) (is-O_TDLL (read var9 var7)))) (and (and (= var4 (write var9 var7 (O_TDLL (TDLL (|TDLL::next| (getTDLL (read var9 var7))) (|TDLL::prev| (getTDLL (read var9 var7))) 2)))) (= var3 var8)) (= var1 var7))))) (inv_main_28 var5 var6 var6 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main1022_3 var9 var8 var7) (and (and (and (not (= var6 nullAddr)) (and (and (and (= var5 var4) (= var6 var3)) (= var2 var1)) (= var0 nullAddr))) (and (and (is-O_TDLL (read var9 var7)) (is-O_TDLL (read var9 (|TDLL::next| (getTDLL (read var9 var7)))))) (is-O_TDLL (read var9 (|TDLL::next| (getTDLL (read var9 var7))))))) (and (and (= var4 (write var9 (|TDLL::next| (getTDLL (read var9 var7))) (O_TDLL (TDLL (|TDLL::next| (getTDLL (read var9 (|TDLL::next| (getTDLL (read var9 var7)))))) (|TDLL::prev| (getTDLL (read var9 (|TDLL::next| (getTDLL (read var9 var7)))))) 2)))) (= var3 var8)) (= var1 var7))))) (inv_main_28 var5 var6 var6 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main_20 var6 var5 var4) (and (and (not (= var3 nullAddr)) (is-O_TDLL (read var6 var4))) (and (and (and (= var2 var6) (= var1 var5)) (= var0 var4)) (= var3 (|TDLL::next| (getTDLL (read var6 var4)))))))) (inv_main1022_3 var2 var1 var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Heap)) (or (not (and (inv_main996_2_1 var2 var1) (and (and (is-O_TDLL (read var2 var1)) (is-O_TDLL (read var2 var1))) (= var0 (write var2 var1 (O_TDLL (TDLL nullAddr (|TDLL::prev| (getTDLL (read var2 var1))) (|TDLL::data| (getTDLL (read var2 var1)))))))))) (inv_main var0 var1))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Int) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main_10 var7 var6 var5) (and (not (= var4 nullAddr)) (and (not (= var3 0)) (and (and (not (= var2 nullAddr)) (is-O_TDLL (read var7 var5))) (and (and (and (= var1 var7) (= var0 var6)) (= var4 var5)) (= var2 (|TDLL::next| (getTDLL (read var7 var5)))))))))) (inv_main_14 var1 var0 var4))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Int) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main_35 var9 var8 var7 var6) (and (and (and (= var5 2) (is-O_TDLL (read var9 var7))) (and (and (and (and (= var4 var9) (= var3 var8)) (= var2 var7)) (= var1 var6)) (= var5 (|TDLL::data| (getTDLL (read var9 var7)))))) (= var0 0)))) (inv_main1047_7 var4 var3 var2 var1 var5 var0))))
(assert (forall ((var0 Addr) (var1 TDLL) (var2 Heap) (var3 Heap)) (or (not (and (inv_main996_2 var3) (and (= var2 (newHeap (alloc var3 (O_TDLL var1)))) (= var0 (newAddr (alloc var3 (O_TDLL var1))))))) (inv_main996_2_1 var2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main_7 var6 var5 var4) (and (is-O_TDLL (read var6 var4)) (and (and (and (= var3 var6) (= var2 var5)) (= var1 var4)) (= var0 (|TDLL::next| (getTDLL (read var6 var4)))))))) (inv_main_8 var3 var2 var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main_24 var3 var2 var1) (and (and (is-O_TDLL (read var3 var1)) (is-O_TDLL (read var3 var1))) (= var0 (write var3 var1 (O_TDLL (TDLL nullAddr (|TDLL::prev| (getTDLL (read var3 var1))) (|TDLL::data| (getTDLL (read var3 var1)))))))))) (inv_main_25 var0 var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main_33 var3 var2 var1 var0) (and (not (= var2 nullAddr)) (= var1 nullAddr)))) (inv_main_47 var3 var2 var2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Heap)) (or (not (and (inv_main_47 var12 var11 var10 var9) (and (and (not (= var8 nullAddr)) (and (is-O_TDLL (read var12 var10)) (and (and (and (and (= var7 var12) (= var6 var11)) (= var5 var10)) (= var4 var9)) (= var3 (|TDLL::next| (getTDLL (read var12 var10))))))) (and (and (and (= var2 (write var7 var6 defObj)) (= var1 var6)) (= var8 var3)) (= var0 var4))))) (inv_main_47 var2 var8 var8 var0))))
(assert (forall ((var0 Addr) (var1 TDLL) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main_20 var9 var8 var7) (and (and (and (and (= var6 nullAddr) (is-O_TDLL (read var9 var7))) (and (and (and (= var5 var9) (= var4 var8)) (= var3 var7)) (= var6 (|TDLL::next| (getTDLL (read var9 var7)))))) (= var2 (newHeap (alloc var5 (O_TDLL var1))))) (= var0 (newAddr (alloc var5 (O_TDLL var1))))))) (inv_main1019_3 var2 var4 var3 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main_33 var3 var2 var1 var0) (not (= var1 nullAddr)))) (inv_main_35 var3 var2 var1 var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main_6 var3 var2 var1) (and (and (and (is-O_TDLL (read var3 var1)) (is-O_TDLL (read var3 (|TDLL::next| (getTDLL (read var3 var1)))))) (is-O_TDLL (read var3 (|TDLL::next| (getTDLL (read var3 var1)))))) (= var0 (write var3 (|TDLL::next| (getTDLL (read var3 var1))) (O_TDLL (TDLL (|TDLL::next| (getTDLL (read var3 (|TDLL::next| (getTDLL (read var3 var1)))))) var1 (|TDLL::data| (getTDLL (read var3 (|TDLL::next| (getTDLL (read var3 var1))))))))))))) (inv_main_7 var0 var2 var1))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main_8 var3 var2 var1) (and (and (is-O_TDLL (read var3 var1)) (is-O_TDLL (read var3 var1))) (= var0 (write var3 var1 (O_TDLL (TDLL nullAddr (|TDLL::prev| (getTDLL (read var3 var1))) (|TDLL::data| (getTDLL (read var3 var1)))))))))) (inv_main_9 var0 var2 var1))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main1029_3 var5 var4 var3 var2 var1) (and (and (is-O_TDLL (read var5 var3)) (is-O_TDLL (read var5 var3))) (= var0 (write var5 var3 (O_TDLL (TDLL var2 (|TDLL::prev| (getTDLL (read var5 var3))) (|TDLL::data| (getTDLL (read var5 var3)))))))))) (inv_main_29 var0 var4 var3 var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main_14 var6 var5 var4) (and (is-O_TDLL (read var6 var4)) (and (and (and (= var3 var6) (= var2 var5)) (= var1 var4)) (= var0 (|TDLL::next| (getTDLL (read var6 var4)))))))) (inv_main_10 var3 var2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Int) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main_9 var6 var5 var4) (and (and (= var3 0) (and (is-O_TDLL (read var6 var4)) (is-O_TDLL (read var6 var4)))) (and (and (= var2 (write var6 var4 (O_TDLL (TDLL (|TDLL::next| (getTDLL (read var6 var4))) (|TDLL::prev| (getTDLL (read var6 var4))) 0)))) (= var1 var5)) (= var0 var4))))) (inv_main_10 var2 var1 var1))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Addr) (var4 Heap)) (or (not (and (inv_main_2 var4 var3) (and (and (= var2 0) (and (is-O_TDLL (read var4 var3)) (is-O_TDLL (read var4 var3)))) (and (= var1 (write var4 var3 (O_TDLL (TDLL (|TDLL::next| (getTDLL (read var4 var3))) (|TDLL::prev| (getTDLL (read var4 var3))) 0)))) (= var0 var3))))) (inv_main_10 var1 var0 var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main_17 var3 var2 var1) (and (and (is-O_TDLL (read var3 var1)) (is-O_TDLL (read var3 var1))) (= var0 (write var3 var1 (O_TDLL (TDLL (|TDLL::next| (getTDLL (read var3 var1))) (|TDLL::prev| (getTDLL (read var3 var1))) 1))))))) (inv_main_20 var0 var2 var1))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main_22 var3 var2 var1) (and (and (and (is-O_TDLL (read var3 var1)) (is-O_TDLL (read var3 (|TDLL::next| (getTDLL (read var3 var1)))))) (is-O_TDLL (read var3 (|TDLL::next| (getTDLL (read var3 var1)))))) (= var0 (write var3 (|TDLL::next| (getTDLL (read var3 var1))) (O_TDLL (TDLL (|TDLL::next| (getTDLL (read var3 (|TDLL::next| (getTDLL (read var3 var1)))))) var1 (|TDLL::data| (getTDLL (read var3 (|TDLL::next| (getTDLL (read var3 var1))))))))))))) (inv_main_23 var0 var2 var1))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Int) (var7 Int) (var8 Int) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Heap)) (or (not (and (inv_main_38 var12 var11 var10 var9 var8 var7) (and (and (= var6 2) (is-O_TDLL (read var12 var10))) (and (and (and (and (and (and (= var5 var12) (= var4 var11)) (= var3 var10)) (= var2 var9)) (= var1 var8)) (= var0 var7)) (= var6 (|TDLL::data| (getTDLL (read var12 var10)))))))) (inv_main1052_7_42 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main_10 var6 var5 var4) (and (not (= var3 nullAddr)) (and (and (= var2 nullAddr) (is-O_TDLL (read var6 var4))) (and (and (and (= var1 var6) (= var0 var5)) (= var3 var4)) (= var2 (|TDLL::next| (getTDLL (read var6 var4))))))))) (inv_main_17 var1 var0 var3))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Int) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main_10 var7 var6 var5) (and (not (= var4 nullAddr)) (and (= var3 0) (and (and (not (= var2 nullAddr)) (is-O_TDLL (read var7 var5))) (and (and (and (= var1 var7) (= var0 var6)) (= var4 var5)) (= var2 (|TDLL::next| (getTDLL (read var7 var5)))))))))) (inv_main_17 var1 var0 var4))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main_28 var4 var3 var2 var1) (and (is-O_TDLL (read var4 var2)) (= var0 (|TDLL::next| (getTDLL (read var4 var2))))))) (inv_main1029_3 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main1004_36 var4 var3 var2 var1) (and (and (is-O_TDLL (read var4 var2)) (is-O_TDLL (read var4 var2))) (= var0 (write var4 var2 (O_TDLL (TDLL var1 (|TDLL::prev| (getTDLL (read var4 var2))) (|TDLL::data| (getTDLL (read var4 var2)))))))))) (inv_main_6 var0 var3 var2))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Int) (var6 Int) (var7 Int) (var8 Int) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Heap)) (or (not (and (inv_main1047_7 var12 var11 var10 var9 var8 var7) (and (or (not (= var6 2)) (= var5 1)) (and (and (is-O_TDLL (read var12 var10)) (is-O_TDLL (read var12 (|TDLL::next| (getTDLL (read var12 var10)))))) (and (and (and (and (and (and (= var4 var12) (= var3 var11)) (= var2 var10)) (= var1 var9)) (= var6 var8)) (= var0 var7)) (= var5 (|TDLL::data| (getTDLL (read var12 (|TDLL::next| (getTDLL (read var12 var10)))))))))))) (inv_main_38 var4 var3 var2 var1 var6 var5))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Int) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main_35 var9 var8 var7 var6) (and (and (and (and (not (= var5 2)) (not (= var5 2))) (is-O_TDLL (read var9 var7))) (and (and (and (and (= var4 var9) (= var3 var8)) (= var2 var7)) (= var1 var6)) (= var5 (|TDLL::data| (getTDLL (read var9 var7)))))) (= var0 0)))) (inv_main_38 var4 var3 var2 var1 var5 var0))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main996_2_1 var1 var0) (not (is-O_TDLL (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main996_2_1 var1 var0) (and (is-O_TDLL (read var1 var0)) (not (is-O_TDLL (read var1 var0))))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main var1 var0) (not (is-O_TDLL (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main var1 var0) (and (is-O_TDLL (read var1 var0)) (not (is-O_TDLL (read var1 var0))))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main_2 var1 var0) (not (is-O_TDLL (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main_2 var1 var0) (and (is-O_TDLL (read var1 var0)) (not (is-O_TDLL (read var1 var0))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main1004_36 var3 var2 var1 var0) (not (is-O_TDLL (read var3 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main1004_36 var3 var2 var1 var0) (and (is-O_TDLL (read var3 var1)) (not (is-O_TDLL (read var3 var1))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_6 var2 var1 var0) (not (is-O_TDLL (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_6 var2 var1 var0) (and (is-O_TDLL (read var2 var0)) (not (is-O_TDLL (read var2 (|TDLL::next| (getTDLL (read var2 var0)))))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_6 var2 var1 var0) (and (and (is-O_TDLL (read var2 var0)) (is-O_TDLL (read var2 (|TDLL::next| (getTDLL (read var2 var0)))))) (not (is-O_TDLL (read var2 (|TDLL::next| (getTDLL (read var2 var0)))))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_7 var2 var1 var0) (not (is-O_TDLL (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_8 var2 var1 var0) (not (is-O_TDLL (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_8 var2 var1 var0) (and (is-O_TDLL (read var2 var0)) (not (is-O_TDLL (read var2 var0))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_9 var2 var1 var0) (not (is-O_TDLL (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_9 var2 var1 var0) (and (is-O_TDLL (read var2 var0)) (not (is-O_TDLL (read var2 var0))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_10 var2 var1 var0) (not (is-O_TDLL (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_14 var2 var1 var0) (not (is-O_TDLL (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_17 var2 var1 var0) (not (is-O_TDLL (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_17 var2 var1 var0) (and (is-O_TDLL (read var2 var0)) (not (is-O_TDLL (read var2 var0))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_20 var2 var1 var0) (not (is-O_TDLL (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main1019_3 var3 var2 var1 var0) (not (is-O_TDLL (read var3 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main1019_3 var3 var2 var1 var0) (and (is-O_TDLL (read var3 var1)) (not (is-O_TDLL (read var3 var1))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_22 var2 var1 var0) (not (is-O_TDLL (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_22 var2 var1 var0) (and (is-O_TDLL (read var2 var0)) (not (is-O_TDLL (read var2 (|TDLL::next| (getTDLL (read var2 var0)))))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_22 var2 var1 var0) (and (and (is-O_TDLL (read var2 var0)) (is-O_TDLL (read var2 (|TDLL::next| (getTDLL (read var2 var0)))))) (not (is-O_TDLL (read var2 (|TDLL::next| (getTDLL (read var2 var0)))))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_23 var2 var1 var0) (not (is-O_TDLL (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_24 var2 var1 var0) (not (is-O_TDLL (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_24 var2 var1 var0) (and (is-O_TDLL (read var2 var0)) (not (is-O_TDLL (read var2 var0))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_25 var2 var1 var0) (not (is-O_TDLL (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_25 var2 var1 var0) (and (is-O_TDLL (read var2 var0)) (not (is-O_TDLL (read var2 var0))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main1022_3 var2 var1 var0) (not (is-O_TDLL (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main1022_3 var2 var1 var0) (and (is-O_TDLL (read var2 var0)) (not (is-O_TDLL (read var2 (|TDLL::next| (getTDLL (read var2 var0)))))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main1022_3 var2 var1 var0) (and (and (is-O_TDLL (read var2 var0)) (is-O_TDLL (read var2 (|TDLL::next| (getTDLL (read var2 var0)))))) (not (is-O_TDLL (read var2 (|TDLL::next| (getTDLL (read var2 var0)))))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_28 var3 var2 var1 var0) (not (is-O_TDLL (read var3 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main1029_3 var4 var3 var2 var1 var0) (not (is-O_TDLL (read var4 var2)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main1029_3 var4 var3 var2 var1 var0) (and (is-O_TDLL (read var4 var2)) (not (is-O_TDLL (read var4 var2))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main_29 var4 var3 var2 var1 var0) (not (is-O_TDLL (read var4 var2)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main_29 var4 var3 var2 var1 var0) (and (is-O_TDLL (read var4 var2)) (not (is-O_TDLL (read var4 var2))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_35 var3 var2 var1 var0) (not (is-O_TDLL (read var3 var1)))))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (not (and (inv_main1047_7 var5 var4 var3 var2 var1 var0) (not (is-O_TDLL (read var5 var3)))))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (not (and (inv_main1047_7 var5 var4 var3 var2 var1 var0) (and (is-O_TDLL (read var5 var3)) (not (is-O_TDLL (read var5 (|TDLL::next| (getTDLL (read var5 var3)))))))))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (not (and (inv_main_38 var5 var4 var3 var2 var1 var0) (not (is-O_TDLL (read var5 var3)))))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (not (and (inv_main1052_7_42 var5 var4 var3 var2 var1 var0) (not (is-O_TDLL (read var5 var3)))))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (not (and (inv_main_41 var5 var4 var3 var2 var1 var0) (not (is-O_TDLL (read var5 var3)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_47 var3 var2 var1 var0) (not (is-O_TDLL (read var3 var1)))))))
(check-sat)
