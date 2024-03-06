(set-logic HORN)
(set-info :source |
    Benchmark: C_VC
    Output by Princess (http://www.philipp.ruemmer.org/princess.shtml)
|)
(set-info :status unknown)
(declare-datatype bool (
  (true)
  (false)
))
(declare-heap Heap Addr HeapObject
 defObj
 ((HeapObject 0) (sll 0)) (
  (
   (O_Int (getInt Int))
   (O_UInt (getUInt Int))
   (O_Addr (getAddr Addr))
   (O_AddrRange (getAddrRange AddrRange))
   (O_sll (getsll sll))
   (defObj)
  )
  (
   (sll (|sll::data| Addr) (|sll::next| Addr))
  )
))
(declare-fun inv_main2438_5 (Heap Addr) Bool)
(declare-fun inv_main2439_5 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main2441_12 (Heap Addr Int) Bool)
(declare-fun inv_main_15 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main_2 (Heap Addr Addr Addr Addr) Bool)
(assert (forall ((var0 Addr) (var1 Heap)) (or (not (and (= var1 emptyHeap) (= var0 nullAddr))) (inv_main2438_5 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Heap)) (or (not (and (inv_main2439_5 var13 var12 var11 var10) (and (and (and (and (and (= var9 var8) (= var7 var6)) (= var5 var4)) (= var3 var2)) (= var1 (|sll::next| (getsll (read var8 var2))))) (and (and (and (and (and (= var8 var13) (= var6 var12)) (= var4 var11)) (= var2 var10)) (= var0 (|sll::data| (getsll (read var13 var10))))) (not (= var10 nullAddr)))))) (inv_main2439_5 var9 var7 var5 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main_2 var5 var4 var3 var2 var1) (= var0 0))) (inv_main2439_5 var5 var4 var3 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Heap)) (or (not (and (inv_main_15 var13 var12 var11 var10) (and (and (and (and (and (and (= var9 var13) (= var8 var12)) (= var7 var11)) (= var6 var10)) (= var5 (|sll::next| (getsll (read var13 var10))))) (and (and (and (and (= var4 (write var9 var6 defObj)) (or (and (= var8 var6) (= var3 nullAddr)) (and (not (= var8 var6)) (= var3 var8)))) (= var2 var7)) (= var1 var6)) (= var0 var5))) (not (= var10 nullAddr))))) (inv_main_15 var4 var3 var2 var0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main2439_5 var5 var4 var3 var2) (and (and (and (not (= var3 nullAddr)) (= var2 nullAddr)) (= var1 (write var5 (|sll::data| (getsll (read var5 var3))) defObj))) (or (and (= var4 (|sll::data| (getsll (read var5 var3)))) (= var0 nullAddr)) (and (not (= var4 (|sll::data| (getsll (read var5 var3))))) (= var0 var4)))))) (inv_main_15 var1 var0 var3 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main2439_5 var3 var2 var1 var0) (and (= var1 nullAddr) (= var0 nullAddr)))) (inv_main_15 var3 var2 var1 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main_15 var4 var3 var2 var1) (and (= var1 nullAddr) (= var0 0)))) (inv_main2441_12 var4 var3 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Int) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Heap) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Bool) (var17 Addr) (var18 sll) (var19 Heap) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Addr) (var25 Addr) (var26 Addr) (var27 Addr) (var28 Addr) (var29 Heap) (var30 Heap) (var31 Addr) (var32 Addr) (var33 Addr) (var34 Addr) (var35 Heap)) (or (not (and (inv_main_2 var35 var34 var33 var32 var31) (and (and (and (and (and (and (and (= var30 var29) (= var28 var27)) (= var26 var25)) (= var24 var23)) (= var22 var21)) (= var20 (|sll::next| (getsll (read var29 var23))))) (and (and (and (and (and (and (and (and (= var19 (newHeap (alloc var35 (O_sll var18)))) (or (and var16 (= var17 (newAddr (alloc var35 (O_sll var18))))) (and (not var16) (= var17 var34)))) (= var15 var33)) (= var14 var32)) (= var13 var31)) (= var12 (newAddr (alloc var35 (O_sll var18))))) (and (and (and (and (and (= var11 (write var19 var12 (O_sll (sll (|sll::data| (getsll (read var19 var12))) nullAddr)))) (= var10 var17)) (= var9 var15)) (= var8 var14)) (= var7 var13)) (= var6 var12))) (not (= var5 0))) (and (and (and (and (= var4 (write var11 var8 (O_sll (sll (|sll::data| (getsll (read var11 var8))) var6)))) (= var3 var10)) (= var2 var9)) (= var1 var8)) (= var0 var7)))) (and (and (and (and (= var29 (write var4 (|sll::next| (getsll (read var4 var1))) (O_sll (sll var0 (|sll::next| (getsll (read var4 (|sll::next| (getsll (read var4 var1)))))))))) (= var27 var3)) (= var25 var2)) (= var23 var1)) (= var21 var0))))) (inv_main_2 var30 var28 var26 var20 var22))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Bool) (var3 Addr) (var4 sll) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Int) (var11 Heap) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Bool) (var18 Addr) (var19 Int) (var20 Heap) (var21 Heap) (var22 Addr) (var23 Heap)) (or (not (and (inv_main2438_5 var23 var22) (and (and (and (and (and (and (and (= var21 (newHeap (alloc var20 (O_Int var19)))) (or (and var17 (= var18 (newAddr (alloc var20 (O_Int var19))))) (and (not var17) (= var18 var16)))) (= var15 var14)) (= var13 var14)) (= var12 (newAddr (alloc var20 (O_Int var19))))) (and (and (and (and (= var11 (write var21 var12 (O_Int var10))) (= var9 var18)) (= var8 var15)) (= var7 var13)) (= var6 var12))) (and (and (and (= var5 (newHeap (alloc var23 (O_sll var4)))) (or (and var2 (= var3 (newAddr (alloc var23 (O_sll var4))))) (and (not var2) (= var3 var22)))) (= var1 (newAddr (alloc var23 (O_sll var4))))) (and (and (= var20 (write var5 var1 (O_sll (sll (|sll::data| (getsll (read var5 var1))) nullAddr)))) (= var16 var3)) (= var14 var1)))) (= var0 (write var11 var7 (O_sll (sll var6 (|sll::next| (getsll (read var11 var7)))))))))) (inv_main_2 var0 var9 var8 var7 var6))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap)) (not (and (inv_main2441_12 var2 var1 var0) (not (= var1 nullAddr))))))
(check-sat)
