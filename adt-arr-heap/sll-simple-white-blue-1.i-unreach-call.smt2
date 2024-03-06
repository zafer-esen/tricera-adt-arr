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
   (TSLL (|TSLL::next| Addr) (|TSLL::data| Int))
  )
))
(declare-fun inv_main1003_2 (Heap Addr Addr) Bool)
(declare-fun inv_main1053_13 (Heap Addr Addr) Bool)
(declare-fun inv_main999_2 (Heap) Bool)
(declare-fun inv_main_12 (Heap Addr Addr) Bool)
(declare-fun inv_main_20 (Heap Addr Addr) Bool)
(declare-fun inv_main_23 (Heap Addr Addr) Bool)
(declare-fun inv_main_31 (Heap Addr Addr) Bool)
(assert (forall ((var0 Heap)) (or (not (= var0 emptyHeap)) (inv_main999_2 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main1003_2 var4 var3 var2) (and (= var1 0) (= var0 0)))) (inv_main_12 var4 var3 var3))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main_12 var7 var6 var5) (and (and (and (and (= var4 var7) (= var3 var6)) (= var2 var5)) (= var1 (|TSLL::next| (getTSLL (read var7 var5))))) (and (= var0 0) (not (= (|TSLL::next| (getTSLL (read var7 var5))) nullAddr)))))) (inv_main_12 var4 var3 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main_20 var10 var9 var8) (and (and (and (and (= var7 var6) (= var5 var4)) (= var3 var2)) (= var1 (|TSLL::next| (getTSLL (read var6 var2))))) (and (= var0 1) (and (and (and (= var6 var10) (= var4 var9)) (= var2 var8)) (= var0 (|TSLL::data| (getTSLL (read var10 var8))))))))) (inv_main_23 var7 var5 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main_23 var10 var9 var8) (and (and (and (and (= var7 var6) (= var5 var4)) (= var3 var2)) (= var1 (|TSLL::next| (getTSLL (read var6 var2))))) (and (and (not (= var0 1)) (and (and (and (= var6 var10) (= var4 var9)) (= var2 var8)) (= var0 (|TSLL::data| (getTSLL (read var10 var8)))))) (not (= var8 nullAddr)))))) (inv_main_23 var7 var5 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main_20 var10 var9 var8) (and (and (and (and (= var7 var6) (= var5 var4)) (= var3 var2)) (= var1 (|TSLL::next| (getTSLL (read var6 var2))))) (and (not (= var0 1)) (and (and (and (= var6 var10) (= var4 var9)) (= var2 var8)) (= var0 (|TSLL::data| (getTSLL (read var10 var8))))))))) (inv_main_20 var7 var5 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Int) (var7 Int) (var8 Addr) (var9 Addr) (var10 Addr) (var11 TSLL) (var12 Heap) (var13 Addr) (var14 Addr) (var15 Heap)) (or (not (and (inv_main1003_2 var15 var14 var13) (and (and (and (and (and (and (= var12 (newHeap (alloc var15 (O_TSLL var11)))) (= var10 var14)) (= var9 var13)) (= var8 (newAddr (alloc var15 (O_TSLL var11))))) (and (not (= var7 0)) (= var6 0))) (and (and (= var5 (write var12 var8 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var12 var8))) 1)))) (= var4 var10)) (= var3 var8))) (and (and (= var2 (write var5 var3 (O_TSLL (TSLL var4 (|TSLL::data| (getTSLL (read var5 var3))))))) (= var1 var4)) (= var0 var3))))) (inv_main_20 var2 var0 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 TSLL) (var19 Heap) (var20 Heap) (var21 Addr) (var22 Addr) (var23 Heap)) (or (not (and (inv_main_12 var23 var22 var21) (and (and (and (and (and (and (and (and (and (= var20 (newHeap (alloc var19 (O_TSLL var18)))) (= var17 var16)) (= var15 var14)) (= var13 var12)) (= var11 (newAddr (alloc var19 (O_TSLL var18))))) (and (and (and (= var19 var23) (= var16 var22)) (= var14 var21)) (= var12 (|TSLL::next| (getTSLL (read var23 var21)))))) (and (and (and (= var10 (write var20 var15 (O_TSLL (TSLL var11 (|TSLL::data| (getTSLL (read var20 var15))))))) (= var9 var17)) (= var8 var15)) (= var7 var13))) (and (and (and (= var6 (write var10 var8 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var10 var8))) 1)))) (= var5 var9)) (= var4 var8)) (= var3 var7))) (and (and (= var2 (write var6 var4 (O_TSLL (TSLL var3 (|TSLL::data| (getTSLL (read var6 var4))))))) (= var1 var5)) (= var0 var4))) (= (|TSLL::next| (getTSLL (read var23 var21))) nullAddr)))) (inv_main_20 var2 var1 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Heap) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr) (var19 TSLL) (var20 Heap) (var21 Heap) (var22 Addr) (var23 Addr) (var24 Heap)) (or (not (and (inv_main_12 var24 var23 var22) (and (and (and (and (and (and (and (and (and (= var21 (newHeap (alloc var20 (O_TSLL var19)))) (= var18 var17)) (= var16 var15)) (= var14 var13)) (= var12 (newAddr (alloc var20 (O_TSLL var19))))) (and (and (and (= var20 var24) (= var17 var23)) (= var15 var22)) (= var13 (|TSLL::next| (getTSLL (read var24 var22)))))) (and (and (and (= var11 (write var21 var16 (O_TSLL (TSLL var12 (|TSLL::data| (getTSLL (read var21 var16))))))) (= var10 var18)) (= var9 var16)) (= var8 var14))) (and (and (and (= var7 (write var11 var9 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var11 var9))) 1)))) (= var6 var10)) (= var5 var9)) (= var4 var8))) (and (and (= var3 (write var7 var5 (O_TSLL (TSLL var4 (|TSLL::data| (getTSLL (read var7 var5))))))) (= var2 var6)) (= var1 var5))) (and (not (= var0 0)) (not (= (|TSLL::next| (getTSLL (read var24 var22))) nullAddr)))))) (inv_main_20 var3 var2 var2))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr) (var7 Addr) (var8 TSLL) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Heap) (var16 Heap) (var17 Addr) (var18 Addr) (var19 Heap)) (or (not (and (inv_main1003_2 var19 var18 var17) (and (and (and (and (and (and (and (= var16 var15) (= var14 var13)) (= var12 var11)) (= var10 (|TSLL::next| (getTSLL (read var15 var11))))) (and (and (and (and (= var9 (newHeap (alloc var19 (O_TSLL var8)))) (= var7 var18)) (= var6 var17)) (= var5 (newAddr (alloc var19 (O_TSLL var8))))) (not (= var4 0)))) (and (and (= var15 (write var9 var6 (O_TSLL (TSLL var5 (|TSLL::data| (getTSLL (read var9 var6))))))) (= var13 var7)) (= var11 var6))) (and (and (= var3 (write var16 var10 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var16 var10))) 0)))) (= var2 var14)) (= var1 var10))) (= var0 (write var3 var1 (O_TSLL (TSLL nullAddr (|TSLL::data| (getTSLL (read var3 var1)))))))))) (inv_main1003_2 var0 var2 var1))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Heap) (var4 Addr) (var5 TSLL) (var6 Heap) (var7 Heap)) (or (not (and (inv_main999_2 var7) (and (and (and (= var6 (newHeap (alloc var7 (O_TSLL var5)))) (= var4 (newAddr (alloc var7 (O_TSLL var5))))) (and (= var3 (write var6 var4 (O_TSLL (TSLL nullAddr (|TSLL::data| (getTSLL (read var6 var4))))))) (= var2 var4))) (and (= var1 (write var3 var2 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var3 var2))) 0)))) (= var0 var2))))) (inv_main1003_2 var1 var0 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Int) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main_23 var6 var5 var4) (and (and (= var3 1) (and (and (and (= var2 var6) (= var1 var5)) (= var0 var4)) (= var3 (|TSLL::data| (getTSLL (read var6 var4)))))) (not (= var4 nullAddr))))) (inv_main1053_13 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (and (inv_main_23 var2 var1 var0) (= var0 nullAddr))) (inv_main_31 var2 var1 var1))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main_31 var7 var6 var5) (and (and (and (and (and (= var4 var7) (= var3 var5)) (= var2 var5)) (= var1 (|TSLL::next| (getTSLL (read var7 var5))))) (not (= var5 nullAddr))) (= var0 (write var4 var3 defObj))))) (inv_main_31 var0 var3 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (inv_main1053_13 var2 var1 var0))))
(check-sat)
