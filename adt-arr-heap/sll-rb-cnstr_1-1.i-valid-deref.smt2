(set-logic HORN)
(set-info :source |
    Benchmark: C_VC
    Output by Princess (http://www.philipp.ruemmer.org/princess.shtml)
|)
(set-info :status sat)
(declare-heap Heap Addr HeapObject
 defObj
 ((HeapObject 0) (TSLL 0)) (
  (
   (O_Int (getInt Int))
   (O_UInt (getUInt Int))
   (O_Addr (getAddr Addr))
   (O_AddrRange (getAddrRange AddrRange))
   (O_TSLL (getTSLL TSLL))
   (defObj)
  )
  (
   (TSLL (|TSLL::next| Addr) (|TSLL::colour| Int))
  )
))
(declare-fun inv_main (Heap Addr) Bool)
(declare-fun inv_main1006_2 (Heap) Bool)
(declare-fun inv_main1006_2_1 (Heap Addr) Bool)
(declare-fun inv_main1010_2 (Heap Addr Addr) Bool)
(declare-fun inv_main1016_3 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main1021_3 (Heap Addr Addr) Bool)
(declare-fun inv_main1025_3 (Heap Addr Addr) Bool)
(declare-fun inv_main1027_4 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main1043_7 (Heap Addr Addr) Bool)
(declare-fun inv_main1057_3 (Heap Addr Addr) Bool)
(declare-fun inv_main1064_3 (Heap Addr Addr) Bool)
(declare-fun inv_main_10 (Heap Addr Addr) Bool)
(declare-fun inv_main_11 (Heap Addr Addr) Bool)
(declare-fun inv_main_14 (Heap Addr Addr) Bool)
(declare-fun inv_main_21 (Heap Addr Addr) Bool)
(declare-fun inv_main_22 (Heap Addr Addr) Bool)
(declare-fun inv_main_25 (Heap Addr Addr) Bool)
(declare-fun inv_main_31 (Heap Addr Addr) Bool)
(declare-fun inv_main_33 (Heap Addr Addr) Bool)
(declare-fun inv_main_5 (Heap Addr Addr) Bool)
(declare-fun inv_main_6 (Heap Addr Addr) Bool)
(declare-fun inv_main_9 (Heap Addr Addr) Bool)
(assert (forall ((var0 Heap)) (or (not (= var0 emptyHeap)) (inv_main1006_2 var0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main_33 var9 var8 var7) (and (and (not (= nullAddr var6)) (and (is-O_TSLL (read var9 var7)) (and (and (and (= var5 var9) (= var4 var8)) (= var3 var7)) (= var2 (|TSLL::next| (getTSLL (read var9 var7))))))) (and (and (= var1 (write var5 var3 defObj)) (= var6 var2)) (= var0 var3))))) (inv_main_31 var1 var6 var0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main1064_3 var9 var8 var7) (and (not (= nullAddr var6)) (and (and (is-O_TSLL (read var9 var8)) (and (and (and (= var5 var9) (= var4 var8)) (= var3 var7)) (= var2 (|TSLL::next| (getTSLL (read var9 var8)))))) (and (and (= var1 (write var5 var4 defObj)) (= var0 var4)) (= var6 var2)))))) (inv_main_31 var1 var6 var6))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main_22 var6 var5 var4) (and (not (= nullAddr var3)) (and (= nullAddr var2) (and (is-O_TSLL (read var6 var4)) (and (and (and (= var1 var6) (= var3 var5)) (= var0 var4)) (= var2 (|TSLL::next| (getTSLL (read var6 var4)))))))))) (inv_main_31 var1 var3 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (and (inv_main_14 var2 var1 var0) (and (not (= nullAddr var1)) (and (= nullAddr var0) (and (is-O_TSLL (read var2 var0)) (= 1 (|TSLL::colour| (getTSLL (read var2 var0))))))))) (inv_main_31 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 TSLL) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main1025_3 var8 var7 var6) (and (and (and (and (is-O_TSLL (read var8 var6)) (is-O_TSLL (read var8 var6))) (and (and (= var5 (write var8 var6 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var8 var6))) 0)))) (= var4 var7)) (= var3 var6))) (= var2 (newHeap (alloc var5 (O_TSLL var1))))) (= var0 (newAddr (alloc var5 (O_TSLL var1))))))) (inv_main1027_4 var2 var4 var3 var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Heap)) (or (not (and (inv_main1006_2_1 var2 var1) (and (and (is-O_TSLL (read var2 var1)) (is-O_TSLL (read var2 var1))) (= var0 (write var2 var1 (O_TSLL (TSLL nullAddr (|TSLL::colour| (getTSLL (read var2 var1)))))))))) (inv_main var0 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main_9 var6 var5 var4) (and (is-O_TSLL (read var6 var4)) (and (and (and (= var3 var6) (= var2 var5)) (= var1 var4)) (= var0 (|TSLL::next| (getTSLL (read var6 var4)))))))) (inv_main_10 var3 var2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (and (inv_main_21 var2 var1 var0) (and (is-O_TSLL (read var2 var0)) (not (= 0 (|TSLL::colour| (getTSLL (read var2 var0)))))))) (inv_main_22 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (and (inv_main_25 var2 var1 var0) (and (is-O_TSLL (read var2 var0)) (= 1 (|TSLL::colour| (getTSLL (read var2 var0))))))) (inv_main_22 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main_5 var6 var5 var4) (and (is-O_TSLL (read var6 var4)) (and (and (and (= var3 var6) (= var2 var5)) (= var1 var4)) (= var0 (|TSLL::next| (getTSLL (read var6 var4)))))))) (inv_main_6 var3 var2 var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main_10 var3 var2 var1) (and (and (is-O_TSLL (read var3 var1)) (is-O_TSLL (read var3 var1))) (= var0 (write var3 var1 (O_TSLL (TSLL nullAddr (|TSLL::colour| (getTSLL (read var3 var1)))))))))) (inv_main_11 var0 var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main_22 var6 var5 var4) (and (not (= nullAddr var3)) (and (is-O_TSLL (read var6 var4)) (and (and (and (= var2 var6) (= var1 var5)) (= var0 var4)) (= var3 (|TSLL::next| (getTSLL (read var6 var4))))))))) (inv_main_21 var2 var1 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (and (inv_main_14 var2 var1 var0) (and (not (= nullAddr var0)) (and (is-O_TSLL (read var2 var0)) (= 1 (|TSLL::colour| (getTSLL (read var2 var0)))))))) (inv_main_21 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Int) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main_6 var6 var5 var4) (and (= var3 0) (and (and (is-O_TSLL (read var6 var4)) (is-O_TSLL (read var6 var4))) (and (and (= var2 (write var6 var4 (O_TSLL (TSLL nullAddr (|TSLL::colour| (getTSLL (read var6 var4))))))) (= var1 var5)) (= var0 var4)))))) (inv_main1025_3 var2 var1 var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main1027_4 var4 var3 var2 var1) (and (and (is-O_TSLL (read var4 var2)) (is-O_TSLL (read var4 var2))) (= var0 (write var4 var2 (O_TSLL (TSLL var1 (|TSLL::colour| (getTSLL (read var4 var2)))))))))) (inv_main_9 var0 var3 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (and (inv_main_31 var2 var1 var0) (and (is-O_TSLL (read var2 var1)) (not (= 0 (|TSLL::colour| (getTSLL (read var2 var1)))))))) (inv_main1064_3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (and (inv_main_21 var2 var1 var0) (and (is-O_TSLL (read var2 var0)) (= 0 (|TSLL::colour| (getTSLL (read var2 var0))))))) (inv_main1043_7 var2 var1 var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main1057_3 var7 var6 var5) (and (and (is-O_TSLL (read var7 var6)) (and (and (and (= var4 var7) (= var3 var6)) (= var2 var5)) (= var1 (|TSLL::next| (getTSLL (read var7 var6)))))) (= var0 (write var4 var3 defObj))))) (inv_main_33 var0 var3 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main1043_7 var6 var5 var4) (and (not (= nullAddr var3)) (and (is-O_TSLL (read var6 var4)) (and (and (and (= var2 var6) (= var1 var5)) (= var0 var4)) (= var3 (|TSLL::next| (getTSLL (read var6 var4))))))))) (inv_main_25 var2 var1 var3))))
(assert (forall ((var0 Addr) (var1 TSLL) (var2 Heap) (var3 Int) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main1010_2 var6 var5 var4) (and (and (not (= var3 0)) (= var2 (newHeap (alloc var6 (O_TSLL var1))))) (= var0 (newAddr (alloc var6 (O_TSLL var1))))))) (inv_main1016_3 var2 var5 var4 var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main1016_3 var4 var3 var2 var1) (and (and (is-O_TSLL (read var4 var2)) (is-O_TSLL (read var4 var2))) (= var0 (write var4 var2 (O_TSLL (TSLL var1 (|TSLL::colour| (getTSLL (read var4 var2)))))))))) (inv_main_5 var0 var3 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Int) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main_6 var6 var5 var4) (and (not (= var3 0)) (and (and (is-O_TSLL (read var6 var4)) (is-O_TSLL (read var6 var4))) (and (and (= var2 (write var6 var4 (O_TSLL (TSLL nullAddr (|TSLL::colour| (getTSLL (read var6 var4))))))) (= var1 var5)) (= var0 var4)))))) (inv_main1021_3 var2 var1 var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main1021_3 var3 var2 var1) (and (and (is-O_TSLL (read var3 var1)) (is-O_TSLL (read var3 var1))) (= var0 (write var3 var1 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var3 var1))) 1))))))) (inv_main1010_2 var0 var2 var1))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main_11 var3 var2 var1) (and (and (is-O_TSLL (read var3 var1)) (is-O_TSLL (read var3 var1))) (= var0 (write var3 var1 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var3 var1))) 1))))))) (inv_main1010_2 var0 var2 var1))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Heap)) (or (not (and (inv_main var3 var2) (and (and (is-O_TSLL (read var3 var2)) (is-O_TSLL (read var3 var2))) (and (= var1 (write var3 var2 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var3 var2))) 1)))) (= var0 var2))))) (inv_main1010_2 var1 var0 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (and (inv_main_31 var2 var1 var0) (and (is-O_TSLL (read var2 var1)) (= 0 (|TSLL::colour| (getTSLL (read var2 var1))))))) (inv_main1057_3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main1010_2 var6 var5 var4) (and (not (= nullAddr var3)) (and (= var2 0) (and (and (= var1 var6) (= var3 var5)) (= var0 nullAddr)))))) (inv_main_14 var1 var3 var3))))
(assert (forall ((var0 Addr) (var1 TSLL) (var2 Heap) (var3 Heap)) (or (not (and (inv_main1006_2 var3) (and (= var2 (newHeap (alloc var3 (O_TSLL var1)))) (= var0 (newAddr (alloc var3 (O_TSLL var1))))))) (inv_main1006_2_1 var2 var0))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main1006_2_1 var1 var0) (not (is-O_TSLL (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main1006_2_1 var1 var0) (and (is-O_TSLL (read var1 var0)) (not (is-O_TSLL (read var1 var0))))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main var1 var0) (not (is-O_TSLL (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main var1 var0) (and (is-O_TSLL (read var1 var0)) (not (is-O_TSLL (read var1 var0))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main1016_3 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main1016_3 var3 var2 var1 var0) (and (is-O_TSLL (read var3 var1)) (not (is-O_TSLL (read var3 var1))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_5 var2 var1 var0) (not (is-O_TSLL (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_6 var2 var1 var0) (not (is-O_TSLL (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_6 var2 var1 var0) (and (is-O_TSLL (read var2 var0)) (not (is-O_TSLL (read var2 var0))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main1021_3 var2 var1 var0) (not (is-O_TSLL (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main1021_3 var2 var1 var0) (and (is-O_TSLL (read var2 var0)) (not (is-O_TSLL (read var2 var0))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main1025_3 var2 var1 var0) (not (is-O_TSLL (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main1025_3 var2 var1 var0) (and (is-O_TSLL (read var2 var0)) (not (is-O_TSLL (read var2 var0))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main1027_4 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main1027_4 var3 var2 var1 var0) (and (is-O_TSLL (read var3 var1)) (not (is-O_TSLL (read var3 var1))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_9 var2 var1 var0) (not (is-O_TSLL (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_10 var2 var1 var0) (not (is-O_TSLL (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_10 var2 var1 var0) (and (is-O_TSLL (read var2 var0)) (not (is-O_TSLL (read var2 var0))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_11 var2 var1 var0) (not (is-O_TSLL (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_11 var2 var1 var0) (and (is-O_TSLL (read var2 var0)) (not (is-O_TSLL (read var2 var0))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_14 var2 var1 var0) (not (is-O_TSLL (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_21 var2 var1 var0) (not (is-O_TSLL (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main1043_7 var2 var1 var0) (not (is-O_TSLL (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_25 var2 var1 var0) (not (is-O_TSLL (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_22 var2 var1 var0) (not (is-O_TSLL (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_31 var2 var1 var0) (not (is-O_TSLL (read var2 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main1057_3 var2 var1 var0) (not (is-O_TSLL (read var2 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_33 var2 var1 var0) (not (is-O_TSLL (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main1064_3 var2 var1 var0) (not (is-O_TSLL (read var2 var1)))))))
(check-sat)
