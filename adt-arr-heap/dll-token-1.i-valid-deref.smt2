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
   (TSLL (|TSLL::next| Addr) (|TSLL::prev| Addr) (|TSLL::data| Int))
  )
))
(declare-fun inv_main (Heap Addr) Bool)
(declare-fun inv_main1004_2 (Heap) Bool)
(declare-fun inv_main1004_2_1 (Heap Addr) Bool)
(declare-fun inv_main1015_3 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main1022_2 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main_13 (Heap Addr Addr) Bool)
(declare-fun inv_main_14 (Heap Addr Addr) Bool)
(declare-fun inv_main_17 (Heap Addr Addr) Bool)
(declare-fun inv_main_2 (Heap Addr) Bool)
(declare-fun inv_main_20 (Heap Addr Addr) Bool)
(declare-fun inv_main_21 (Heap Addr Addr) Bool)
(declare-fun inv_main_22 (Heap Addr Addr) Bool)
(declare-fun inv_main_25 (Heap Addr Addr) Bool)
(declare-fun inv_main_28 (Heap Addr Addr) Bool)
(declare-fun inv_main_32 (Heap Addr Addr) Bool)
(declare-fun inv_main_33 (Heap Addr Addr) Bool)
(declare-fun inv_main_35 (Heap Addr Addr) Bool)
(declare-fun inv_main_37 (Heap Addr Addr) Bool)
(declare-fun inv_main_4 (Heap Addr Addr) Bool)
(declare-fun inv_main_6 (Heap Addr Addr) Bool)
(declare-fun inv_main_7 (Heap Addr Addr) Bool)
(declare-fun inv_main_8 (Heap Addr Addr) Bool)
(assert (forall ((var0 Heap)) (or (not (= var0 emptyHeap)) (inv_main1004_2 var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main_6 var3 var2 var1) (and (and (and (is-O_TSLL (read var3 var1)) (is-O_TSLL (read var3 (|TSLL::next| (getTSLL (read var3 var1)))))) (is-O_TSLL (read var3 (|TSLL::next| (getTSLL (read var3 var1)))))) (= var0 (write var3 (|TSLL::next| (getTSLL (read var3 var1))) (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var3 (|TSLL::next| (getTSLL (read var3 var1)))))) var1 (|TSLL::data| (getTSLL (read var3 (|TSLL::next| (getTSLL (read var3 var1))))))))))))) (inv_main_7 var0 var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (and (inv_main_32 var2 var1 var0) (and (is-O_TSLL (read var2 var0)) (= 1 (|TSLL::data| (getTSLL (read var2 var0))))))) (inv_main_33 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (and (inv_main_28 var2 var1 var0) (and (is-O_TSLL (read var2 var0)) (= 2 (|TSLL::data| (getTSLL (read var2 var0))))))) (inv_main_32 var2 var1 var1))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main_35 var7 var6 var5) (and (and (is-O_TSLL (read var7 var5)) (and (and (and (= var4 var7) (= var3 var6)) (= var2 var5)) (= var1 (|TSLL::next| (getTSLL (read var7 var5)))))) (= var0 (write var4 var3 defObj))))) (inv_main_32 var0 var3 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (and (inv_main_32 var2 var1 var0) (and (is-O_TSLL (read var2 var0)) (not (= 1 (|TSLL::data| (getTSLL (read var2 var0)))))))) (inv_main_35 var2 var0 var0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Int) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main_8 var6 var5 var4) (and (= var3 0) (and (and (not (= nullAddr var2)) (and (is-O_TSLL (read var6 var4)) (is-O_TSLL (read var6 var4)))) (and (and (= var1 (write var6 var4 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var6 var4))) (|TSLL::prev| (getTSLL (read var6 var4))) 0)))) (= var0 var5)) (= var2 var4)))))) (inv_main_4 var1 var0 var2))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Addr) (var4 Heap)) (or (not (and (inv_main_2 var4 var3) (and (and (= var2 0) (and (is-O_TSLL (read var4 var3)) (is-O_TSLL (read var4 var3)))) (and (= var1 (write var4 var3 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var4 var3))) (|TSLL::prev| (getTSLL (read var4 var3))) 0)))) (= var0 var3))))) (inv_main_4 var1 var0 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main_25 var6 var5 var4) (and (is-O_TSLL (read var6 var4)) (and (and (and (= var3 var6) (= var2 var5)) (= var1 var4)) (= var0 (|TSLL::next| (getTSLL (read var6 var4)))))))) (inv_main_28 var3 var2 var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main1022_2 var4 var3 var2 var1) (and (and (is-O_TSLL (read var4 var2)) (is-O_TSLL (read var4 var2))) (= var0 (write var4 var2 (O_TSLL (TSLL var1 (|TSLL::prev| (getTSLL (read var4 var2))) (|TSLL::data| (getTSLL (read var4 var2)))))))))) (inv_main_13 var0 var3 var2))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Heap)) (or (not (and (inv_main1004_2_1 var2 var1) (and (and (is-O_TSLL (read var2 var1)) (is-O_TSLL (read var2 var1))) (= var0 (write var2 var1 (O_TSLL (TSLL nullAddr (|TSLL::prev| (getTSLL (read var2 var1))) (|TSLL::data| (getTSLL (read var2 var1)))))))))) (inv_main var0 var1))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Heap)) (or (not (and (inv_main var2 var1) (and (and (is-O_TSLL (read var2 var1)) (is-O_TSLL (read var2 var1))) (= var0 (write var2 var1 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var2 var1))) nullAddr (|TSLL::data| (getTSLL (read var2 var1)))))))))) (inv_main_2 var0 var1))))
(assert (forall ((var0 Addr) (var1 TSLL) (var2 Heap) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Int) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main_8 var9 var8 var7) (and (and (and (not (= var6 0)) (and (and (not (= nullAddr var5)) (and (is-O_TSLL (read var9 var7)) (is-O_TSLL (read var9 var7)))) (and (and (= var4 (write var9 var7 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var9 var7))) (|TSLL::prev| (getTSLL (read var9 var7))) 0)))) (= var3 var8)) (= var5 var7)))) (= var2 (newHeap (alloc var4 (O_TSLL var1))))) (= var0 (newAddr (alloc var4 (O_TSLL var1))))))) (inv_main1015_3 var2 var3 var5 var0))))
(assert (forall ((var0 Addr) (var1 TSLL) (var2 Heap) (var3 Addr) (var4 Heap) (var5 Int) (var6 Addr) (var7 Heap)) (or (not (and (inv_main_2 var7 var6) (and (and (and (and (not (= var5 0)) (and (is-O_TSLL (read var7 var6)) (is-O_TSLL (read var7 var6)))) (and (= var4 (write var7 var6 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var7 var6))) (|TSLL::prev| (getTSLL (read var7 var6))) 0)))) (= var3 var6))) (= var2 (newHeap (alloc var4 (O_TSLL var1))))) (= var0 (newAddr (alloc var4 (O_TSLL var1))))))) (inv_main1015_3 var2 var3 var3 var0))))
(assert (forall ((var0 Addr) (var1 TSLL) (var2 Heap) (var3 Heap)) (or (not (and (inv_main1004_2 var3) (and (= var2 (newHeap (alloc var3 (O_TSLL var1)))) (= var0 (newAddr (alloc var3 (O_TSLL var1))))))) (inv_main1004_2_1 var2 var0))))
(assert (forall ((var0 Addr) (var1 TSLL) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main_4 var8 var7 var6) (and (and (and (and (is-O_TSLL (read var8 var6)) (is-O_TSLL (read var8 var6))) (and (and (= var5 (write var8 var6 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var8 var6))) (|TSLL::prev| (getTSLL (read var8 var6))) 1)))) (= var4 var7)) (= var3 var6))) (= var2 (newHeap (alloc var5 (O_TSLL var1))))) (= var0 (newAddr (alloc var5 (O_TSLL var1))))))) (inv_main1022_2 var2 var4 var3 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main_7 var6 var5 var4) (and (is-O_TSLL (read var6 var4)) (and (and (and (= var3 var6) (= var2 var5)) (= var1 var4)) (= var0 (|TSLL::next| (getTSLL (read var6 var4)))))))) (inv_main_8 var3 var2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (and (inv_main_20 var2 var1 var0) (and (is-O_TSLL (read var2 var0)) (= 1 (|TSLL::data| (getTSLL (read var2 var0))))))) (inv_main_25 var2 var1 var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main1015_3 var4 var3 var2 var1) (and (and (is-O_TSLL (read var4 var2)) (is-O_TSLL (read var4 var2))) (= var0 (write var4 var2 (O_TSLL (TSLL var1 (|TSLL::prev| (getTSLL (read var4 var2))) (|TSLL::data| (getTSLL (read var4 var2)))))))))) (inv_main_6 var0 var3 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (and (inv_main_17 var2 var1 var0) (and (is-O_TSLL (read var2 var0)) (= 1 (|TSLL::data| (getTSLL (read var2 var0))))))) (inv_main_20 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (and (inv_main_21 var2 var1 var0) (and (is-O_TSLL (read var2 var0)) (= 0 (|TSLL::data| (getTSLL (read var2 var0))))))) (inv_main_22 var2 var1 var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main_13 var3 var2 var1) (and (and (and (is-O_TSLL (read var3 var1)) (is-O_TSLL (read var3 (|TSLL::next| (getTSLL (read var3 var1)))))) (is-O_TSLL (read var3 (|TSLL::next| (getTSLL (read var3 var1)))))) (= var0 (write var3 (|TSLL::next| (getTSLL (read var3 var1))) (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var3 (|TSLL::next| (getTSLL (read var3 var1)))))) var1 (|TSLL::data| (getTSLL (read var3 (|TSLL::next| (getTSLL (read var3 var1))))))))))))) (inv_main_14 var0 var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main_22 var6 var5 var4) (and (is-O_TSLL (read var6 var4)) (and (and (and (= var3 var6) (= var2 var5)) (= var1 var4)) (= var0 (|TSLL::next| (getTSLL (read var6 var4)))))))) (inv_main_17 var3 var2 var0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main_14 var5 var4 var3) (and (not (= nullAddr var2)) (and (and (and (is-O_TSLL (read var5 var3)) (is-O_TSLL (read var5 (|TSLL::next| (getTSLL (read var5 var3)))))) (is-O_TSLL (read var5 (|TSLL::next| (getTSLL (read var5 var3)))))) (and (and (= var1 (write var5 (|TSLL::next| (getTSLL (read var5 var3))) (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var5 (|TSLL::next| (getTSLL (read var5 var3)))))) (|TSLL::prev| (getTSLL (read var5 (|TSLL::next| (getTSLL (read var5 var3)))))) 2)))) (= var2 var4)) (= var0 var3)))))) (inv_main_17 var1 var2 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (and (inv_main_17 var2 var1 var0) (and (is-O_TSLL (read var2 var0)) (not (= 1 (|TSLL::data| (getTSLL (read var2 var0)))))))) (inv_main_21 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (and (inv_main_33 var2 var1 var0) (and (is-O_TSLL (read var2 var0)) (= 1 (|TSLL::data| (getTSLL (read var2 var0))))))) (inv_main_37 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main1004_2_1 var1 var0) (not (is-O_TSLL (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main1004_2_1 var1 var0) (and (is-O_TSLL (read var1 var0)) (not (is-O_TSLL (read var1 var0))))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main var1 var0) (not (is-O_TSLL (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main var1 var0) (and (is-O_TSLL (read var1 var0)) (not (is-O_TSLL (read var1 var0))))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main_2 var1 var0) (not (is-O_TSLL (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main_2 var1 var0) (and (is-O_TSLL (read var1 var0)) (not (is-O_TSLL (read var1 var0))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main1015_3 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main1015_3 var3 var2 var1 var0) (and (is-O_TSLL (read var3 var1)) (not (is-O_TSLL (read var3 var1))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_6 var2 var1 var0) (not (is-O_TSLL (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_6 var2 var1 var0) (and (is-O_TSLL (read var2 var0)) (not (is-O_TSLL (read var2 (|TSLL::next| (getTSLL (read var2 var0)))))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_6 var2 var1 var0) (and (and (is-O_TSLL (read var2 var0)) (is-O_TSLL (read var2 (|TSLL::next| (getTSLL (read var2 var0)))))) (not (is-O_TSLL (read var2 (|TSLL::next| (getTSLL (read var2 var0)))))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_7 var2 var1 var0) (not (is-O_TSLL (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_8 var2 var1 var0) (not (is-O_TSLL (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_8 var2 var1 var0) (and (is-O_TSLL (read var2 var0)) (not (is-O_TSLL (read var2 var0))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_4 var2 var1 var0) (not (is-O_TSLL (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_4 var2 var1 var0) (and (is-O_TSLL (read var2 var0)) (not (is-O_TSLL (read var2 var0))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main1022_2 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main1022_2 var3 var2 var1 var0) (and (is-O_TSLL (read var3 var1)) (not (is-O_TSLL (read var3 var1))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_13 var2 var1 var0) (not (is-O_TSLL (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_13 var2 var1 var0) (and (is-O_TSLL (read var2 var0)) (not (is-O_TSLL (read var2 (|TSLL::next| (getTSLL (read var2 var0)))))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_13 var2 var1 var0) (and (and (is-O_TSLL (read var2 var0)) (is-O_TSLL (read var2 (|TSLL::next| (getTSLL (read var2 var0)))))) (not (is-O_TSLL (read var2 (|TSLL::next| (getTSLL (read var2 var0)))))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_14 var2 var1 var0) (not (is-O_TSLL (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_14 var2 var1 var0) (and (is-O_TSLL (read var2 var0)) (not (is-O_TSLL (read var2 (|TSLL::next| (getTSLL (read var2 var0)))))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_14 var2 var1 var0) (and (and (is-O_TSLL (read var2 var0)) (is-O_TSLL (read var2 (|TSLL::next| (getTSLL (read var2 var0)))))) (not (is-O_TSLL (read var2 (|TSLL::next| (getTSLL (read var2 var0)))))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_17 var2 var1 var0) (not (is-O_TSLL (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_21 var2 var1 var0) (not (is-O_TSLL (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_22 var2 var1 var0) (not (is-O_TSLL (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_20 var2 var1 var0) (not (is-O_TSLL (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_25 var2 var1 var0) (not (is-O_TSLL (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_28 var2 var1 var0) (not (is-O_TSLL (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_32 var2 var1 var0) (not (is-O_TSLL (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_35 var2 var1 var0) (not (is-O_TSLL (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_33 var2 var1 var0) (not (is-O_TSLL (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_37 var2 var1 var0) (not (is-O_TSLL (read var2 var0)))))))
(check-sat)
