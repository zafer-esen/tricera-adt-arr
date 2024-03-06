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
(declare-fun inv_main1002_2 (Heap Addr Addr Int) Bool)
(declare-fun inv_main997_2 (Heap) Bool)
(declare-fun inv_main_30 (Heap Addr Addr Int) Bool)
(declare-fun inv_main_56 (Heap Addr Addr Int) Bool)
(declare-fun inv_main_65 (Heap Addr Addr Int) Bool)
(assert (forall ((var0 Heap)) (or (not (= var0 emptyHeap)) (inv_main997_2 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Heap) (var7 Addr) (var8 TSLL) (var9 Heap) (var10 Heap)) (or (not (and (inv_main997_2 var10) (and (and (and (and (and (= var9 (newHeap (alloc var10 (O_TSLL var8)))) (= var7 (newAddr (alloc var10 (O_TSLL var8))))) (and (= var6 (write var9 var7 (O_TSLL (TSLL nullAddr (|TSLL::prev| (getTSLL (read var9 var7))) (|TSLL::data| (getTSLL (read var9 var7))))))) (= var5 var7))) (and (= var4 (write var6 var5 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var6 var5))) nullAddr (|TSLL::data| (getTSLL (read var6 var5))))))) (= var3 var5))) (and (= var2 (write var4 var3 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var4 var3))) (|TSLL::prev| (getTSLL (read var4 var3))) 0)))) (= var1 var3))) (= var0 0)))) (inv_main1002_2 var2 var1 var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Int) (var7 Addr) (var8 Addr) (var9 Heap) (var10 Int) (var11 Addr) (var12 Int) (var13 Addr) (var14 Addr) (var15 TSLL) (var16 Heap) (var17 Addr) (var18 Int) (var19 Int) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Heap) (var25 Heap) (var26 Int) (var27 Addr) (var28 Addr) (var29 Int) (var30 Addr) (var31 Addr) (var32 Heap)) (or (not (and (inv_main1002_2 var32 var31 var30 var29) (and (and (and (not (= var28 nullAddr)) (not (= var27 nullAddr))) (and (and (and (= var26 0) (and (and (and (and (and (and (= var25 var24) (= var23 var22)) (= var21 var20)) (= var19 var18)) (= var17 (|TSLL::next| (getTSLL (read var24 var20))))) (and (and (and (and (and (and (= var16 (newHeap (alloc var32 (O_TSLL var15)))) (= var14 var31)) (= var13 var30)) (= var12 var29)) (= var11 (newAddr (alloc var32 (O_TSLL var15))))) (not (= var10 0))) (and (and (and (= var9 (write var16 var13 (O_TSLL (TSLL var11 (|TSLL::prev| (getTSLL (read var16 var13))) (|TSLL::data| (getTSLL (read var16 var13))))))) (= var8 var14)) (= var7 var13)) (= var6 var12)))) (and (and (and (= var24 (write var9 (|TSLL::next| (getTSLL (read var9 var7))) (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var9 (|TSLL::next| (getTSLL (read var9 var7)))))) var7 (|TSLL::data| (getTSLL (read var9 (|TSLL::next| (getTSLL (read var9 var7)))))))))) (= var22 var8)) (= var20 var7)) (= var18 var6)))) (and (and (and (= var5 (write var25 var17 (O_TSLL (TSLL nullAddr (|TSLL::prev| (getTSLL (read var25 var17))) (|TSLL::data| (getTSLL (read var25 var17))))))) (= var4 var23)) (= var3 var17)) (= var26 var19))) (and (and (and (= var2 (write var5 var3 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var5 var3))) (|TSLL::prev| (getTSLL (read var5 var3))) 1)))) (= var27 var4)) (= var28 var3)) (= var1 var26)))) (= var0 1)))) (inv_main1002_2 var2 var27 var28 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Int) (var7 Addr) (var8 Addr) (var9 Heap) (var10 Int) (var11 Addr) (var12 Int) (var13 Addr) (var14 Addr) (var15 TSLL) (var16 Heap) (var17 Addr) (var18 Int) (var19 Int) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Heap) (var25 Heap) (var26 Int) (var27 Addr) (var28 Addr) (var29 Int) (var30 Addr) (var31 Addr) (var32 Heap)) (or (not (and (inv_main1002_2 var32 var31 var30 var29) (and (and (and (not (= var28 nullAddr)) (not (= var27 nullAddr))) (and (and (= var26 1) (and (and (not (= var26 0)) (and (and (and (and (and (and (= var25 var24) (= var23 var22)) (= var21 var20)) (= var19 var18)) (= var17 (|TSLL::next| (getTSLL (read var24 var20))))) (and (and (and (and (and (and (= var16 (newHeap (alloc var32 (O_TSLL var15)))) (= var14 var31)) (= var13 var30)) (= var12 var29)) (= var11 (newAddr (alloc var32 (O_TSLL var15))))) (not (= var10 0))) (and (and (and (= var9 (write var16 var13 (O_TSLL (TSLL var11 (|TSLL::prev| (getTSLL (read var16 var13))) (|TSLL::data| (getTSLL (read var16 var13))))))) (= var8 var14)) (= var7 var13)) (= var6 var12)))) (and (and (and (= var24 (write var9 (|TSLL::next| (getTSLL (read var9 var7))) (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var9 (|TSLL::next| (getTSLL (read var9 var7)))))) var7 (|TSLL::data| (getTSLL (read var9 (|TSLL::next| (getTSLL (read var9 var7)))))))))) (= var22 var8)) (= var20 var7)) (= var18 var6)))) (and (and (and (= var5 (write var25 var17 (O_TSLL (TSLL nullAddr (|TSLL::prev| (getTSLL (read var25 var17))) (|TSLL::data| (getTSLL (read var25 var17))))))) (= var4 var23)) (= var3 var17)) (= var26 var19)))) (and (and (and (= var2 (write var5 var3 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var5 var3))) (|TSLL::prev| (getTSLL (read var5 var3))) 2)))) (= var27 var4)) (= var28 var3)) (= var1 var26)))) (= var0 2)))) (inv_main1002_2 var2 var27 var28 var0))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Int) (var6 Addr) (var7 Int) (var8 Addr) (var9 Addr) (var10 TSLL) (var11 Heap) (var12 Addr) (var13 Int) (var14 Int) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Heap) (var20 Heap) (var21 Int) (var22 Addr) (var23 Addr) (var24 Int) (var25 Addr) (var26 Addr) (var27 Heap)) (or (not (and (inv_main1002_2 var27 var26 var25 var24) (and (and (not (= var23 nullAddr)) (not (= var22 nullAddr))) (and (not (<= 0 (+ var21 (- 2)))) (and (not (= var21 1)) (and (and (not (= var21 0)) (and (and (and (and (and (and (= var20 var19) (= var18 var17)) (= var16 var15)) (= var14 var13)) (= var12 (|TSLL::next| (getTSLL (read var19 var15))))) (and (and (and (and (and (and (= var11 (newHeap (alloc var27 (O_TSLL var10)))) (= var9 var26)) (= var8 var25)) (= var7 var24)) (= var6 (newAddr (alloc var27 (O_TSLL var10))))) (not (= var5 0))) (and (and (and (= var4 (write var11 var8 (O_TSLL (TSLL var6 (|TSLL::prev| (getTSLL (read var11 var8))) (|TSLL::data| (getTSLL (read var11 var8))))))) (= var3 var9)) (= var2 var8)) (= var1 var7)))) (and (and (and (= var19 (write var4 (|TSLL::next| (getTSLL (read var4 var2))) (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var4 (|TSLL::next| (getTSLL (read var4 var2)))))) var2 (|TSLL::data| (getTSLL (read var4 (|TSLL::next| (getTSLL (read var4 var2)))))))))) (= var17 var3)) (= var15 var2)) (= var13 var1)))) (and (and (and (= var0 (write var20 var12 (O_TSLL (TSLL nullAddr (|TSLL::prev| (getTSLL (read var20 var12))) (|TSLL::data| (getTSLL (read var20 var12))))))) (= var22 var18)) (= var23 var12)) (= var21 var14)))))))) (inv_main1002_2 var0 var22 var23 var21))))
(assert (forall ((var0 Int) (var1 Int) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Int) (var7 Addr) (var8 Addr) (var9 Heap) (var10 Int) (var11 Addr) (var12 Int) (var13 Addr) (var14 Addr) (var15 TSLL) (var16 Heap) (var17 Addr) (var18 Int) (var19 Int) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Heap) (var25 Heap) (var26 Int) (var27 Addr) (var28 Addr) (var29 Int) (var30 Addr) (var31 Addr) (var32 Heap)) (or (not (and (inv_main1002_2 var32 var31 var30 var29) (and (and (and (not (= var28 nullAddr)) (not (= var27 nullAddr))) (and (and (<= 0 (+ var26 (- 2))) (and (not (= var26 1)) (and (and (not (= var26 0)) (and (and (and (and (and (and (= var25 var24) (= var23 var22)) (= var21 var20)) (= var19 var18)) (= var17 (|TSLL::next| (getTSLL (read var24 var20))))) (and (and (and (and (and (and (= var16 (newHeap (alloc var32 (O_TSLL var15)))) (= var14 var31)) (= var13 var30)) (= var12 var29)) (= var11 (newAddr (alloc var32 (O_TSLL var15))))) (not (= var10 0))) (and (and (and (= var9 (write var16 var13 (O_TSLL (TSLL var11 (|TSLL::prev| (getTSLL (read var16 var13))) (|TSLL::data| (getTSLL (read var16 var13))))))) (= var8 var14)) (= var7 var13)) (= var6 var12)))) (and (and (and (= var24 (write var9 (|TSLL::next| (getTSLL (read var9 var7))) (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var9 (|TSLL::next| (getTSLL (read var9 var7)))))) var7 (|TSLL::data| (getTSLL (read var9 (|TSLL::next| (getTSLL (read var9 var7)))))))))) (= var22 var8)) (= var20 var7)) (= var18 var6)))) (and (and (and (= var5 (write var25 var17 (O_TSLL (TSLL nullAddr (|TSLL::prev| (getTSLL (read var25 var17))) (|TSLL::data| (getTSLL (read var25 var17))))))) (= var4 var23)) (= var3 var17)) (= var26 var19))))) (and (and (and (= var2 (write var5 var3 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var5 var3))) (|TSLL::prev| (getTSLL (read var5 var3))) 3)))) (= var27 var4)) (= var28 var3)) (= var1 var26)))) (= var0 3)))) (inv_main1002_2 var2 var27 var28 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Int) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main_56 var9 var8 var7 var6) (and (and (and (and (and (= var5 var9) (= var4 var8)) (= var3 var7)) (= var2 var6)) (= var1 (|TSLL::next| (getTSLL (read var9 var7))))) (and (= var6 0) (and (not (= var0 0)) (not (= var7 nullAddr))))))) (inv_main_56 var5 var4 var1 var2))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Int) (var7 Addr) (var8 Int) (var9 Int) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Heap) (var15 Heap) (var16 Int) (var17 Addr) (var18 Addr) (var19 Heap)) (or (not (and (inv_main_56 var19 var18 var17 var16) (and (and (and (and (and (= var15 var14) (= var13 var12)) (= var11 var10)) (= var9 var8)) (= var7 (|TSLL::next| (getTSLL (read var14 var10))))) (and (and (and (not (= var6 0)) (and (not (= var16 0)) (and (and (and (and (= var5 var19) (= var4 var18)) (= var3 var17)) (= var2 var16)) (= var1 (|TSLL::data| (getTSLL (read var19 var17))))))) (and (and (and (and (= var14 var5) (= var12 var4)) (= var10 var3)) (= var8 var2)) (or (and (<= 0 (+ var1 (- 1))) (= var6 1)) (and (not (<= 0 (+ var1 (- 1)))) (= var6 0))))) (and (not (= var0 0)) (not (= var17 nullAddr))))))) (inv_main_56 var15 var13 var7 var9))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Int) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main_30 var8 var7 var6 var5) (and (and (and (and (and (= var4 var8) (= var3 var7)) (= var2 var6)) (= var1 var5)) (= var0 (|TSLL::next| (getTSLL (read var8 var7))))) (not (= var5 3))))) (inv_main_56 var4 var3 var0 var1))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Int) (var7 Addr) (var8 Addr) (var9 Heap) (var10 Addr) (var11 Int) (var12 Addr) (var13 Addr) (var14 Heap) (var15 Int) (var16 Addr) (var17 Int) (var18 Int) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Heap) (var24 Heap) (var25 Int) (var26 Addr) (var27 Addr) (var28 Heap)) (or (not (and (inv_main_30 var28 var27 var26 var25) (and (and (and (and (and (= var24 var23) (= var22 var21)) (= var20 var19)) (= var18 var17)) (= var16 (|TSLL::next| (getTSLL (read var23 var21))))) (and (and (= var15 3) (and (and (and (and (= var23 var14) (= var21 var13)) (= var19 var12)) (= var17 var11)) (= var15 (|TSLL::data| (getTSLL (read var14 (|TSLL::next| (getTSLL (read var14 (|TSLL::next| (getTSLL (read var14 (|TSLL::next| (getTSLL (read var14 var13))))))))))))))) (and (and (not (= var10 nullAddr)) (and (and (and (and (= var14 var9) (= var13 var8)) (= var12 var7)) (= var11 var6)) (= var10 (|TSLL::next| (getTSLL (read var9 (|TSLL::next| (getTSLL (read var9 (|TSLL::next| (getTSLL (read var9 var8)))))))))))) (and (and (not (= var5 nullAddr)) (and (and (and (and (= var9 var4) (= var8 var3)) (= var7 var2)) (= var6 var1)) (= var5 (|TSLL::next| (getTSLL (read var4 (|TSLL::next| (getTSLL (read var4 var3))))))))) (and (and (not (= var0 nullAddr)) (and (and (and (and (= var4 var28) (= var3 var27)) (= var2 var26)) (= var1 var25)) (= var0 (|TSLL::next| (getTSLL (read var28 var27)))))) (and (not (= var27 nullAddr)) (= var25 3))))))))) (inv_main_56 var24 var22 var16 var18))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Heap) (var9 Int) (var10 Addr) (var11 Addr) (var12 Heap)) (or (not (and (inv_main_65 var12 var11 var10 var9) (and (and (and (and (and (and (= var8 var7) (= var6 var5)) (= var4 var5)) (= var3 var2)) (= var1 (|TSLL::next| (getTSLL (read var7 var5))))) (not (= var5 nullAddr))) (and (and (and (= var7 (write var12 var10 defObj)) (= var5 var11)) (= var0 var10)) (= var2 var9))))) (inv_main_65 var8 var1 var4 var3))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Int) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main_56 var8 var7 var6 var5) (and (and (and (and (and (and (= var4 var8) (= var3 var7)) (= var2 var7)) (= var1 var5)) (= var0 (|TSLL::next| (getTSLL (read var8 var7))))) (not (= var7 nullAddr))) (= var6 nullAddr)))) (inv_main_65 var4 var0 var2 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Int) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main_56 var9 var8 var7 var6) (and (and (and (and (and (and (= var5 var9) (= var4 var8)) (= var3 var8)) (= var2 var6)) (= var1 (|TSLL::next| (getTSLL (read var9 var8))))) (not (= var8 nullAddr))) (and (= var0 0) (not (= var7 nullAddr)))))) (inv_main_65 var5 var1 var3 var2))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main1002_2 var4 var3 var2 var1) (and (not (= var1 2)) (and (not (= var1 1)) (and (not (= var3 nullAddr)) (= var0 0)))))) (inv_main_30 var4 var3 var2 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap) (var9 Heap) (var10 Addr) (var11 Int) (var12 Addr) (var13 Addr) (var14 Heap)) (or (not (and (inv_main1002_2 var14 var13 var12 var11) (and (and (and (not (= var10 nullAddr)) (and (and (and (and (= var9 var8) (= var7 var6)) (= var5 var4)) (= var3 var2)) (= var10 (|TSLL::next| (getTSLL (read var8 (|TSLL::next| (getTSLL (read var8 var6))))))))) (and (and (not (= var1 nullAddr)) (and (and (and (and (= var8 var14) (= var6 var13)) (= var4 var12)) (= var2 var11)) (= var1 (|TSLL::next| (getTSLL (read var14 var13)))))) (and (not (= var13 nullAddr)) (= var11 2)))) (and (not (= var11 1)) (and (not (= var13 nullAddr)) (= var0 0)))))) (inv_main_30 var9 var7 var5 var3))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Int) (var6 Int) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main1002_2 var9 var8 var7 var6) (and (not (= var5 2)) (and (and (not (= var4 nullAddr)) (and (and (and (and (= var3 var9) (= var2 var8)) (= var1 var7)) (= var5 var6)) (= var4 (|TSLL::next| (getTSLL (read var9 var8)))))) (and (not (= var8 nullAddr)) (and (= var6 1) (and (not (= var8 nullAddr)) (= var0 0)))))))) (inv_main_30 var3 var2 var1 var5))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Int) (var8 Int) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Heap) (var14 Heap) (var15 Addr) (var16 Int) (var17 Addr) (var18 Addr) (var19 Heap)) (or (not (and (inv_main1002_2 var19 var18 var17 var16) (and (and (and (not (= var15 nullAddr)) (and (and (and (and (= var14 var13) (= var12 var11)) (= var10 var9)) (= var8 var7)) (= var15 (|TSLL::next| (getTSLL (read var13 (|TSLL::next| (getTSLL (read var13 var11))))))))) (and (and (not (= var6 nullAddr)) (and (and (and (and (= var13 var5) (= var11 var4)) (= var9 var3)) (= var7 var2)) (= var6 (|TSLL::next| (getTSLL (read var5 var4)))))) (and (not (= var4 nullAddr)) (= var2 2)))) (and (and (not (= var1 nullAddr)) (and (and (and (and (= var5 var19) (= var4 var18)) (= var3 var17)) (= var2 var16)) (= var1 (|TSLL::next| (getTSLL (read var19 var18)))))) (and (not (= var18 nullAddr)) (and (= var16 1) (and (not (= var18 nullAddr)) (= var0 0)))))))) (inv_main_30 var14 var12 var10 var8))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_65 var3 var2 var1 var0) (and (not (= var1 nullAddr)) (= (read var3 var1) defObj))))))
(check-sat)
