(set-logic HORN)
(set-info :source |
    Benchmark: C_VC
    Output by Princess (http://www.philipp.ruemmer.org/princess.shtml)
|)
(set-info :status unsat)
(declare-datatype bool (
  (true)
  (false)
))
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
(declare-fun inv_exit (Heap Addr) Bool)
(declare-fun inv_main1005_2 (Heap Addr) Bool)
(declare-fun inv_main1013_2 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main1076_9 (Heap Addr Int) Bool)
(declare-fun inv_main_19 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main_22 (Heap Addr Addr Addr Addr) Bool)
(assert (forall ((var0 Addr) (var1 Heap)) (or (not (and (= var1 emptyHeap) (= var0 nullAddr))) (inv_main1005_2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main_22 var10 var9 var8 var7 var6) (and (and (= var8 var7) (and (and (and (and (= var5 (write var10 var8 defObj)) (or (and (= var9 var8) (= var4 nullAddr)) (and (not (= var9 var8)) (= var4 var9)))) (= var3 var8)) (= var2 var7)) (= var1 var6))) (= var0 0)))) (inv_main1076_9 var5 var4 var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Int) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Bool) (var12 Addr) (var13 TSLL) (var14 Heap) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Heap) (var25 Heap) (var26 Int) (var27 Addr) (var28 Addr) (var29 Addr) (var30 Addr) (var31 Heap)) (or (not (and (inv_main1013_2 var31 var30 var29 var28 var27) (and (and (not (= var26 0)) (and (and (and (and (and (and (and (and (= var25 var24) (= var23 var22)) (= var21 var20)) (= var19 var18)) (= var17 var16)) (= var15 (|TSLL::next| (getTSLL (read var24 var16))))) (and (and (and (and (and (and (= var14 (newHeap (alloc var31 (O_TSLL var13)))) (or (and var11 (= var12 (newAddr (alloc var31 (O_TSLL var13))))) (and (not var11) (= var12 var30)))) (= var10 var29)) (= var9 var28)) (= var8 var27)) (= var7 (newAddr (alloc var31 (O_TSLL var13))))) (not (= var6 0)))) (and (and (and (and (= var24 (write var14 var8 (O_TSLL (TSLL var7 (|TSLL::colour| (getTSLL (read var14 var8))))))) (= var22 var12)) (= var20 var10)) (= var18 var9)) (= var16 var8))) (and (and (and (and (= var5 (write var25 var15 (O_TSLL (TSLL var21 (|TSLL::colour| (getTSLL (read var25 var15))))))) (= var4 var23)) (= var3 var21)) (= var2 var19)) (= var1 var15)))) (= var0 (write var5 var1 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var5 var1))) 1))))))) (inv_main1013_2 var0 var4 var3 var2 var1))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap) (var11 Int) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Bool) (var17 Addr) (var18 TSLL) (var19 Heap) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Addr) (var25 Addr) (var26 Addr) (var27 Addr) (var28 Addr) (var29 Heap) (var30 Heap) (var31 Int) (var32 Addr) (var33 Addr) (var34 Addr) (var35 Addr) (var36 Addr) (var37 Addr) (var38 Addr) (var39 Addr) (var40 Bool) (var41 Addr) (var42 TSLL) (var43 Heap) (var44 Heap) (var45 Addr) (var46 Addr) (var47 Addr) (var48 Addr) (var49 Addr) (var50 Addr) (var51 Addr) (var52 Addr) (var53 Addr) (var54 Heap) (var55 Heap) (var56 Addr) (var57 Addr) (var58 Addr) (var59 Addr) (var60 Heap)) (or (not (and (inv_main1013_2 var60 var59 var58 var57 var56) (and (and (and (and (and (and (and (and (and (= var55 var54) (= var53 var52)) (= var51 var50)) (= var49 var48)) (= var47 var46)) (= var45 (|TSLL::next| (getTSLL (read var54 var46))))) (and (and (and (and (and (and (and (= var44 (newHeap (alloc var43 (O_TSLL var42)))) (or (and var40 (= var41 (newAddr (alloc var43 (O_TSLL var42))))) (and (not var40) (= var41 var39)))) (= var38 var37)) (= var36 var35)) (= var34 var33)) (= var32 (newAddr (alloc var43 (O_TSLL var42))))) (and (= var31 0) (and (and (and (and (and (and (and (and (= var30 var29) (= var28 var27)) (= var26 var25)) (= var24 var23)) (= var22 var21)) (= var20 (|TSLL::next| (getTSLL (read var29 var21))))) (and (and (and (and (and (and (= var19 (newHeap (alloc var60 (O_TSLL var18)))) (or (and var16 (= var17 (newAddr (alloc var60 (O_TSLL var18))))) (and (not var16) (= var17 var59)))) (= var15 var58)) (= var14 var57)) (= var13 var56)) (= var12 (newAddr (alloc var60 (O_TSLL var18))))) (not (= var11 0)))) (and (and (and (and (= var29 (write var19 var13 (O_TSLL (TSLL var12 (|TSLL::colour| (getTSLL (read var19 var13))))))) (= var27 var17)) (= var25 var15)) (= var23 var14)) (= var21 var13))) (and (and (and (and (= var10 (write var30 var20 (O_TSLL (TSLL var26 (|TSLL::colour| (getTSLL (read var30 var20))))))) (= var9 var28)) (= var8 var26)) (= var7 var24)) (= var6 var20))))) (and (and (and (and (= var43 (write var10 var6 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var10 var6))) 0)))) (= var39 var9)) (= var37 var8)) (= var35 var7)) (= var33 var6)))) (and (and (and (and (= var54 (write var44 var34 (O_TSLL (TSLL var32 (|TSLL::colour| (getTSLL (read var44 var34))))))) (= var52 var41)) (= var50 var38)) (= var48 var36)) (= var46 var34))) (and (and (and (and (= var5 (write var55 var45 (O_TSLL (TSLL var51 (|TSLL::colour| (getTSLL (read var55 var45))))))) (= var4 var53)) (= var3 var51)) (= var2 var49)) (= var1 var45))) (= var0 (write var5 var1 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var5 var1))) 1))))))) (inv_main1013_2 var0 var4 var3 var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Bool) (var5 Addr) (var6 TSLL) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Heap) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Heap) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Bool) (var21 Addr) (var22 TSLL) (var23 Heap) (var24 Heap) (var25 Addr) (var26 Heap)) (or (not (and (inv_main1005_2 var26 var25) (and (and (and (and (and (and (and (= var24 (newHeap (alloc var23 (O_TSLL var22)))) (or (and var20 (= var21 (newAddr (alloc var23 (O_TSLL var22))))) (and (not var20) (= var21 var19)))) (= var18 var17)) (= var16 (newAddr (alloc var23 (O_TSLL var22))))) (and (and (and (= var15 (write var24 var16 (O_TSLL (TSLL var18 (|TSLL::colour| (getTSLL (read var24 var16))))))) (= var14 var21)) (= var13 var18)) (= var12 var16))) (and (and (and (= var11 (write var15 var12 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var15 var12))) 1)))) (= var10 var14)) (= var9 var13)) (= var8 var12))) (and (and (and (= var7 (newHeap (alloc var26 (O_TSLL var6)))) (or (and var4 (= var5 (newAddr (alloc var26 (O_TSLL var6))))) (and (not var4) (= var5 var25)))) (= var3 (newAddr (alloc var26 (O_TSLL var6))))) (and (and (= var2 (write var7 var3 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var7 var3))) 1)))) (= var1 var5)) (= var0 var3)))) (and (and (= var23 (write var2 var0 (O_TSLL (TSLL nullAddr (|TSLL::colour| (getTSLL (read var2 var0))))))) (= var19 var1)) (= var17 var0))))) (inv_main1013_2 var11 var10 var9 var8 var8))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main_19 var4 var3 var2 var1 var0) (= var2 var0))) (inv_main_22 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Heap) (var18 Heap) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Heap)) (or (not (and (inv_main_22 var23 var22 var21 var20 var19) (and (and (and (and (and (and (and (and (and (= var18 var17) (= var16 var15)) (= var14 var13)) (= var12 var11)) (= var10 var9)) (= var8 (|TSLL::next| (getTSLL (read var17 var9))))) (and (and (and (and (and (and (= var7 var23) (= var6 var22)) (= var5 var21)) (= var4 var20)) (= var3 var19)) (= var2 (|TSLL::next| (getTSLL (read var23 var20))))) (and (= 0 (|TSLL::colour| (getTSLL (read var23 var20)))) (not (= var21 var20))))) (and (and (and (and (= var17 (write var7 var4 defObj)) (or (and (= var6 var4) (= var15 nullAddr)) (and (not (= var6 var4)) (= var15 var6)))) (= var13 var5)) (= var11 var4)) (= var9 var2))) (= var1 (write var18 var10 defObj))) (or (and (= var16 var10) (= var0 nullAddr)) (and (not (= var16 var10)) (= var0 var16)))))) (inv_main_22 var1 var0 var14 var8 var10))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Heap)) (or (not (and (inv_main_22 var15 var14 var13 var12 var11) (and (and (and (and (and (and (and (= var10 var15) (= var9 var14)) (= var8 var13)) (= var7 var12)) (= var6 var11)) (= var5 (|TSLL::next| (getTSLL (read var15 var12))))) (and (not (= 0 (|TSLL::colour| (getTSLL (read var15 var12))))) (not (= var13 var12)))) (and (and (and (and (= var4 (write var10 var7 defObj)) (or (and (= var9 var7) (= var3 nullAddr)) (and (not (= var9 var7)) (= var3 var9)))) (= var2 var8)) (= var1 var7)) (= var0 var5))))) (inv_main_22 var4 var3 var2 var0 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main1013_2 var5 var4 var3 var2 var1) (and (= var3 var2) (= var0 0)))) (inv_exit var5 var4))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main1013_2 var5 var4 var3 var2 var1) (and (not (= 1 (|TSLL::colour| (getTSLL (read var5 var2))))) (and (not (= var3 var2)) (= var0 0))))) (inv_exit var5 var4))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main_19 var10 var9 var8 var7 var6) (and (= var5 var4) (and (and (and (and (and (and (= var3 var10) (= var2 var9)) (= var5 var8)) (= var1 var7)) (= var0 var6)) (= var4 (|TSLL::next| (getTSLL (read var10 var6))))) (and (= 0 (|TSLL::colour| (getTSLL (read var10 var6)))) (not (= var8 var6))))))) (inv_exit var3 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main_19 var10 var9 var8 var7 var6) (and (= 1 (|TSLL::colour| (getTSLL (read var5 var4)))) (and (not (= var3 var4)) (and (and (and (and (and (and (= var5 var10) (= var2 var9)) (= var3 var8)) (= var1 var7)) (= var0 var6)) (= var4 (|TSLL::next| (getTSLL (read var10 var6))))) (and (= 0 (|TSLL::colour| (getTSLL (read var10 var6)))) (not (= var8 var6)))))))) (inv_exit var5 var2))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main1013_2 var5 var4 var3 var2 var1) (and (= 1 (|TSLL::colour| (getTSLL (read var5 var2)))) (and (not (= var3 var2)) (= var0 0))))) (inv_main_19 var5 var4 var3 var2 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main_19 var10 var9 var8 var7 var6) (and (and (and (and (and (and (= var5 var10) (= var4 var9)) (= var3 var8)) (= var2 var7)) (= var1 var6)) (= var0 (|TSLL::next| (getTSLL (read var10 var6))))) (and (not (= 0 (|TSLL::colour| (getTSLL (read var10 var6))))) (not (= var8 var6)))))) (inv_main_19 var5 var4 var3 var2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap) (var11 Heap) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Heap)) (or (not (and (inv_main_19 var16 var15 var14 var13 var12) (and (and (and (and (and (and (= var11 var10) (= var9 var8)) (= var7 var6)) (= var5 var4)) (= var3 var2)) (= var1 (|TSLL::next| (getTSLL (read var10 var2))))) (and (not (= 1 (|TSLL::colour| (getTSLL (read var10 var2))))) (and (not (= var6 var2)) (and (and (and (and (and (and (= var10 var16) (= var8 var15)) (= var6 var14)) (= var4 var13)) (= var0 var12)) (= var2 (|TSLL::next| (getTSLL (read var16 var12))))) (and (= 0 (|TSLL::colour| (getTSLL (read var16 var12)))) (not (= var14 var12))))))))) (inv_main_19 var11 var9 var7 var5 var1))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_exit var1 var0) (not (= var0 nullAddr))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap)) (not (and (inv_main1076_9 var2 var1 var0) (not (= var1 nullAddr))))))
(check-sat)
