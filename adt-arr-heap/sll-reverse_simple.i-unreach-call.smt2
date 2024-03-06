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
(declare-fun inv_main1008_12 (Heap Addr Addr) Bool)
(declare-fun inv_main1011_11 (Heap Addr Addr) Bool)
(declare-fun inv_main1046_12 (Heap Addr Addr Addr Int Int) Bool)
(declare-fun inv_main995_2 (Heap) Bool)
(declare-fun inv_main999_2 (Heap Addr Addr) Bool)
(declare-fun inv_main_23 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main_29 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main_32 (Heap Addr Addr Addr Int Int) Bool)
(declare-fun inv_main_40 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main_8 (Heap Addr Addr) Bool)
(assert (forall ((var0 Heap)) (or (not (= var0 emptyHeap)) (inv_main995_2 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Int) (var10 Int) (var11 Int) (var12 Int) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Heap) (var20 Heap) (var21 Int) (var22 Int) (var23 Addr) (var24 Addr) (var25 Addr) (var26 Heap)) (or (not (and (inv_main_32 var26 var25 var24 var23 var22 var21) (and (and (and (and (and (and (and (= var20 var19) (= var18 var17)) (= var16 var15)) (= var14 var13)) (= var12 var11)) (= var10 var9)) (= var8 (|TSLL::next| (getTSLL (read var19 var15))))) (and (and (and (and (and (and (and (= var19 var7) (= var17 var6)) (= var5 var4)) (= var13 var3)) (= var11 var2)) (= var9 var1)) (= var15 (|TSLL::next| (getTSLL (read var7 var4))))) (and (and (= var0 2) (and (and (and (and (and (and (= var7 var26) (= var6 var25)) (= var4 var24)) (= var3 var23)) (= var2 var22)) (= var1 var21)) (= var0 (|TSLL::data| (getTSLL (read var26 var24)))))) (or (not (= var22 2)) (= var21 1))))))) (inv_main_29 var20 var18 var8 var14))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Heap) (var13 Heap) (var14 Int) (var15 Int) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Heap)) (or (not (and (inv_main_32 var19 var18 var17 var16 var15 var14) (and (and (and (and (and (and (and (= var13 var12) (= var11 var10)) (= var9 var8)) (= var7 var6)) (= var5 var4)) (= var3 var2)) (= var1 (|TSLL::next| (getTSLL (read var12 var8))))) (and (and (not (= var0 2)) (and (and (and (and (and (and (= var12 var19) (= var10 var18)) (= var8 var17)) (= var6 var16)) (= var4 var15)) (= var2 var14)) (= var0 (|TSLL::data| (getTSLL (read var19 var17)))))) (or (not (= var15 2)) (= var14 1)))))) (inv_main_29 var13 var11 var1 var7))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main_23 var3 var2 var1 var0) (= var1 nullAddr))) (inv_main_29 var3 var0 var0 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Heap)) (or (not (and (inv_main_23 var13 var12 var11 var10) (and (and (and (and (and (and (= var9 var13) (= var8 var12)) (= var7 var11)) (= var6 var10)) (= var5 (|TSLL::next| (getTSLL (read var13 var11))))) (and (and (and (and (= var4 (write var9 var7 (O_TSLL (TSLL var6 (|TSLL::data| (getTSLL (read var9 var7))))))) (= var3 var8)) (= var2 var7)) (= var1 var6)) (= var0 var5))) (not (= var11 nullAddr))))) (inv_main_23 var4 var3 var0 var2))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Heap) (var17 Heap) (var18 Addr) (var19 Addr) (var20 Heap)) (or (not (and (inv_main_8 var20 var19 var18) (and (and (and (and (and (= var17 var16) (= var15 var14)) (= var13 var12)) (= var11 nullAddr)) (and (and (and (not (= var10 nullAddr)) (and (and (and (= var9 var8) (= var7 var6)) (= var5 var4)) (= var10 (|TSLL::next| (getTSLL (read var8 var4)))))) (and (not (= var3 nullAddr)) (and (= var2 nullAddr) (and (and (and (= var1 var20) (= var0 var19)) (= var3 var18)) (= var2 (|TSLL::next| (getTSLL (read var20 var18)))))))) (and (and (= var8 (write var1 var3 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var1 var3))) 1)))) (= var6 var0)) (= var4 var3)))) (and (and (= var16 (write var9 (|TSLL::next| (getTSLL (read var9 var5))) (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var9 (|TSLL::next| (getTSLL (read var9 var5)))))) 2)))) (= var14 var7)) (= var12 var5))))) (inv_main_23 var17 var15 var15 var11))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Int) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap) (var10 Heap) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Heap) (var18 Heap) (var19 Addr) (var20 Addr) (var21 Heap)) (or (not (and (inv_main_8 var21 var20 var19) (and (and (and (and (and (= var18 var17) (= var16 var15)) (= var14 var13)) (= var12 nullAddr)) (and (and (and (not (= var11 nullAddr)) (and (and (and (= var10 var9) (= var8 var7)) (= var6 var5)) (= var11 (|TSLL::next| (getTSLL (read var9 var5)))))) (and (not (= var4 nullAddr)) (and (= var3 0) (and (not (= var2 nullAddr)) (and (and (and (= var1 var21) (= var0 var20)) (= var4 var19)) (= var2 (|TSLL::next| (getTSLL (read var21 var19))))))))) (and (and (= var9 (write var1 var4 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var1 var4))) 1)))) (= var7 var0)) (= var5 var4)))) (and (and (= var17 (write var10 (|TSLL::next| (getTSLL (read var10 var6))) (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var10 (|TSLL::next| (getTSLL (read var10 var6)))))) 2)))) (= var15 var8)) (= var13 var6))))) (inv_main_23 var18 var16 var16 var12))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 TSLL) (var17 Heap) (var18 Heap) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Heap) (var25 Heap) (var26 Addr) (var27 Addr) (var28 Addr) (var29 Addr) (var30 Addr) (var31 Heap) (var32 Heap) (var33 Addr) (var34 Addr) (var35 Heap)) (or (not (and (inv_main_8 var35 var34 var33) (and (and (and (and (and (= var32 var31) (= var30 var29)) (= var28 var27)) (= var26 nullAddr)) (and (and (and (and (and (and (= var25 var24) (= var23 var22)) (= var21 var20)) (= var19 (|TSLL::next| (getTSLL (read var24 var20))))) (and (and (and (and (= var18 (newHeap (alloc var17 (O_TSLL var16)))) (= var15 var14)) (= var13 var12)) (= var11 (newAddr (alloc var17 (O_TSLL var16))))) (and (and (and (= var10 nullAddr) (and (and (and (= var17 var9) (= var14 var8)) (= var12 var7)) (= var10 (|TSLL::next| (getTSLL (read var9 var7)))))) (and (not (= var6 nullAddr)) (and (= var5 nullAddr) (and (and (and (= var4 var35) (= var3 var34)) (= var6 var33)) (= var5 (|TSLL::next| (getTSLL (read var35 var33)))))))) (and (and (= var9 (write var4 var6 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var4 var6))) 1)))) (= var8 var3)) (= var7 var6))))) (and (and (= var24 (write var18 var13 (O_TSLL (TSLL var11 (|TSLL::data| (getTSLL (read var18 var13))))))) (= var22 var15)) (= var20 var13))) (and (and (= var2 (write var25 var19 (O_TSLL (TSLL nullAddr (|TSLL::data| (getTSLL (read var25 var19))))))) (= var1 var23)) (= var0 var19)))) (and (and (= var31 (write var2 var0 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var2 var0))) 2)))) (= var29 var1)) (= var27 var0))))) (inv_main_23 var32 var30 var30 var26))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Int) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 TSLL) (var18 Heap) (var19 Heap) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Addr) (var25 Heap) (var26 Heap) (var27 Addr) (var28 Addr) (var29 Addr) (var30 Addr) (var31 Addr) (var32 Heap) (var33 Heap) (var34 Addr) (var35 Addr) (var36 Heap)) (or (not (and (inv_main_8 var36 var35 var34) (and (and (and (and (and (= var33 var32) (= var31 var30)) (= var29 var28)) (= var27 nullAddr)) (and (and (and (and (and (and (= var26 var25) (= var24 var23)) (= var22 var21)) (= var20 (|TSLL::next| (getTSLL (read var25 var21))))) (and (and (and (and (= var19 (newHeap (alloc var18 (O_TSLL var17)))) (= var16 var15)) (= var14 var13)) (= var12 (newAddr (alloc var18 (O_TSLL var17))))) (and (and (and (= var11 nullAddr) (and (and (and (= var18 var10) (= var15 var9)) (= var13 var8)) (= var11 (|TSLL::next| (getTSLL (read var10 var8)))))) (and (not (= var7 nullAddr)) (and (= var6 0) (and (not (= var5 nullAddr)) (and (and (and (= var4 var36) (= var3 var35)) (= var7 var34)) (= var5 (|TSLL::next| (getTSLL (read var36 var34))))))))) (and (and (= var10 (write var4 var7 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var4 var7))) 1)))) (= var9 var3)) (= var8 var7))))) (and (and (= var25 (write var19 var14 (O_TSLL (TSLL var12 (|TSLL::data| (getTSLL (read var19 var14))))))) (= var23 var16)) (= var21 var14))) (and (and (= var2 (write var26 var20 (O_TSLL (TSLL nullAddr (|TSLL::data| (getTSLL (read var26 var20))))))) (= var1 var24)) (= var0 var20)))) (and (and (= var32 (write var2 var0 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var2 var0))) 2)))) (= var30 var1)) (= var28 var0))))) (inv_main_23 var33 var31 var31 var27))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main_29 var3 var2 var1 var0) (= var1 nullAddr))) (inv_main_40 var3 var2 var2 var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main_40 var9 var8 var7 var6) (and (and (and (and (and (and (= var5 var9) (= var4 var7)) (= var3 var7)) (= var2 var6)) (= var1 (|TSLL::next| (getTSLL (read var9 var7))))) (not (= var7 nullAddr))) (= var0 (write var5 var4 defObj))))) (inv_main_40 var0 var4 var1 var2))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main_32 var5 var4 var3 var2 var1 var0) (and (= var1 2) (not (= var0 1))))) (inv_main1046_12 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr) (var7 Addr) (var8 TSLL) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Heap) (var16 Heap) (var17 Addr) (var18 Addr) (var19 Heap)) (or (not (and (inv_main999_2 var19 var18 var17) (and (and (and (and (and (and (and (= var16 var15) (= var14 var13)) (= var12 var11)) (= var10 (|TSLL::next| (getTSLL (read var15 var11))))) (and (and (and (and (= var9 (newHeap (alloc var19 (O_TSLL var8)))) (= var7 var18)) (= var6 var17)) (= var5 (newAddr (alloc var19 (O_TSLL var8))))) (not (= var4 0)))) (and (and (= var15 (write var9 var6 (O_TSLL (TSLL var5 (|TSLL::data| (getTSLL (read var9 var6))))))) (= var13 var7)) (= var11 var6))) (and (and (= var3 (write var16 var10 (O_TSLL (TSLL nullAddr (|TSLL::data| (getTSLL (read var16 var10))))))) (= var2 var14)) (= var1 var10))) (= var0 (write var3 var1 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var3 var1))) 0))))))) (inv_main999_2 var0 var2 var1))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Heap) (var4 Addr) (var5 TSLL) (var6 Heap) (var7 Heap)) (or (not (and (inv_main995_2 var7) (and (and (and (= var6 (newHeap (alloc var7 (O_TSLL var5)))) (= var4 (newAddr (alloc var7 (O_TSLL var5))))) (and (= var3 (write var6 var4 (O_TSLL (TSLL nullAddr (|TSLL::data| (getTSLL (read var6 var4))))))) (= var2 var4))) (and (= var1 (write var3 var2 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var3 var2))) 0)))) (= var0 var2))))) (inv_main999_2 var1 var0 var0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Int) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main_8 var7 var6 var5) (and (= var4 nullAddr) (and (not (= var3 0)) (and (not (= var2 nullAddr)) (and (and (and (= var1 var7) (= var0 var6)) (= var4 var5)) (= var2 (|TSLL::next| (getTSLL (read var7 var5)))))))))) (inv_main1008_12 var1 var0 var4))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Int) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap) (var11 Heap) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Heap)) (or (not (and (inv_main_29 var15 var14 var13 var12) (and (and (and (and (and (and (and (and (and (= var11 var10) (= var9 var8)) (= var7 var6)) (= var5 var4)) (= var3 var2)) (= var1 0)) (= var0 (|TSLL::data| (getTSLL (read var10 (|TSLL::next| (getTSLL (read var10 var6)))))))) (= var2 2)) (and (and (and (and (= var10 var15) (= var8 var14)) (= var6 var13)) (= var4 var12)) (= var2 (|TSLL::data| (getTSLL (read var15 var13)))))) (not (= var13 nullAddr))))) (inv_main_32 var11 var9 var7 var5 var3 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Int) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main_29 var9 var8 var7 var6) (and (and (and (not (= var5 2)) (and (and (and (and (= var4 var9) (= var3 var8)) (= var2 var7)) (= var1 var6)) (= var5 (|TSLL::data| (getTSLL (read var9 var7)))))) (not (= var7 nullAddr))) (= var0 0)))) (inv_main_32 var4 var3 var2 var1 var5 var0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main_8 var6 var5 var4) (and (= var3 nullAddr) (and (= var2 nullAddr) (and (and (and (= var1 var6) (= var0 var5)) (= var3 var4)) (= var2 (|TSLL::next| (getTSLL (read var6 var4))))))))) (inv_main1011_11 var1 var0 var3))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Int) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main_8 var7 var6 var5) (and (= var4 nullAddr) (and (= var3 0) (and (not (= var2 nullAddr)) (and (and (and (= var1 var7) (= var0 var6)) (= var4 var5)) (= var2 (|TSLL::next| (getTSLL (read var7 var5)))))))))) (inv_main1011_11 var1 var0 var4))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main999_2 var3 var2 var1) (= var0 0))) (inv_main_8 var3 var2 var2))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Heap)) (or (not (and (inv_main_8 var11 var10 var9) (and (and (and (and (= var8 var7) (= var6 var5)) (= var4 var3)) (= var2 (|TSLL::next| (getTSLL (read var7 var3))))) (and (not (= var3 nullAddr)) (and (not (= var1 0)) (and (not (= var0 nullAddr)) (and (and (and (= var7 var11) (= var5 var10)) (= var3 var9)) (= var0 (|TSLL::next| (getTSLL (read var11 var9))))))))))) (inv_main_8 var8 var6 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (inv_main1008_12 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (inv_main1011_11 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (not (inv_main1046_12 var5 var4 var3 var2 var1 var0))))
(check-sat)
