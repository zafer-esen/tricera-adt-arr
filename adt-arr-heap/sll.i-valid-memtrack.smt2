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
   (sll (|sll::next| Addr))
  )
))
(declare-fun inv_main2403_5 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main2412_5 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main2427_5 (Heap Addr) Bool)
(declare-fun inv_main2429_5 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main2430_12 (Heap Addr Int) Bool)
(assert (forall ((var0 Addr) (var1 Heap)) (or (not (and (= var1 emptyHeap) (= var0 nullAddr))) (inv_main2427_5 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main2412_5 var10 var9 var8 var7 var6) (and (and (and (and (and (and (= var5 var10) (= var4 var9)) (= var3 var8)) (= var2 var7)) (= var1 var6)) (= var0 (|sll::next| (getsll (read var10 var6))))) (not (= var6 nullAddr))))) (inv_main2412_5 var5 var4 var3 var2 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main2403_5 var4 var3 var2 var1) (= var0 0))) (inv_main2412_5 var4 var3 var2 var2 var2))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main2429_5 var4 var3 var2 var1) (and (= var1 nullAddr) (= var0 0)))) (inv_main2430_12 var4 var3 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Heap)) (or (not (and (inv_main2429_5 var13 var12 var11 var10) (and (and (and (and (and (and (= var9 var13) (= var8 var12)) (= var7 var11)) (= var6 var10)) (= var5 (|sll::next| (getsll (read var13 var10))))) (and (and (and (and (= var4 (write var9 var6 defObj)) (or (and (= var8 var6) (= var3 nullAddr)) (and (not (= var8 var6)) (= var3 var8)))) (= var2 var7)) (= var1 var6)) (= var0 var5))) (not (= var10 nullAddr))))) (inv_main2429_5 var4 var3 var2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main2412_5 var4 var3 var2 var1 var0) (= var0 nullAddr))) (inv_main2429_5 var4 var3 var2 var2))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Bool) (var10 Addr) (var11 sll) (var12 Heap) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Heap) (var21 Heap) (var22 Addr) (var23 Addr) (var24 Addr) (var25 Heap)) (or (not (and (inv_main2403_5 var25 var24 var23 var22) (and (and (and (and (and (and (= var21 var20) (= var19 var18)) (= var17 var16)) (= var15 var14)) (= var13 (|sll::next| (getsll (read var20 var14))))) (and (and (and (and (and (and (= var12 (newHeap (alloc var25 (O_sll var11)))) (or (and var9 (= var10 (newAddr (alloc var25 (O_sll var11))))) (and (not var9) (= var10 var24)))) (= var8 var23)) (= var7 var22)) (= var6 (newAddr (alloc var25 (O_sll var11))))) (and (and (and (and (= var5 (write var12 var6 (O_sll (sll nullAddr)))) (= var4 var10)) (= var3 var8)) (= var2 var7)) (= var1 var6))) (not (= var0 0)))) (and (and (and (= var20 (write var5 var2 (O_sll (sll var1)))) (= var18 var4)) (= var16 var3)) (= var14 var2))))) (inv_main2403_5 var21 var19 var17 var13))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Bool) (var5 Addr) (var6 sll) (var7 Heap) (var8 Addr) (var9 Heap)) (or (not (and (inv_main2427_5 var9 var8) (and (and (and (= var7 (newHeap (alloc var9 (O_sll var6)))) (or (and var4 (= var5 (newAddr (alloc var9 (O_sll var6))))) (and (not var4) (= var5 var8)))) (= var3 (newAddr (alloc var9 (O_sll var6))))) (and (and (= var2 (write var7 var3 (O_sll (sll nullAddr)))) (= var1 var5)) (= var0 var3))))) (inv_main2403_5 var2 var1 var0 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap)) (not (and (inv_main2430_12 var2 var1 var0) (not (= var1 nullAddr))))))
(check-sat)
