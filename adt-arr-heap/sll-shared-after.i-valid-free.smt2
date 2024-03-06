(set-logic HORN)
(set-info :source |
    Benchmark: C_VC
    Output by Princess (http://www.philipp.ruemmer.org/princess.shtml)
|)
(set-info :status sat)
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
(declare-fun inv_main2409_5 (Heap Addr Addr) Bool)
(declare-fun inv_main2426_9 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main2433_5 (Heap) Bool)
(declare-fun inv_main2436_5 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main_12 (Heap Addr Addr) Bool)
(assert (forall ((var0 Heap)) (or (not (= var0 emptyHeap)) (inv_main2433_5 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap) (var10 Heap) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Heap)) (or (not (and (inv_main2436_5 var15 var14 var13 var12 var11) (and (and (and (and (and (and (and (= var10 var9) (= var8 var7)) (= var6 var5)) (= var4 var3)) (= var2 var1)) (= var0 (|sll::next| (getsll (read var9 var3))))) (not (= var12 nullAddr))) (and (and (and (and (= var9 (write var15 var12 (O_sll (sll var11 (|sll::next| (getsll (read var15 var12))))))) (= var7 var14)) (= var5 var13)) (= var3 var12)) (= var1 var11))))) (inv_main2436_5 var10 var8 var6 var0 var2))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Int) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Heap)) (or (not (and (inv_main2409_5 var11 var10 var9) (and (and (and (and (= var8 (newHeap (alloc var11 (O_Int var7)))) (= var6 var10)) (= var5 (newAddr (alloc var11 (O_Int var7))))) (and (and (= var4 (write var8 var5 (O_Int var3))) (= var2 var6)) (= var1 var5))) (= var0 0)))) (inv_main2436_5 var4 var2 var1 var2 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 sll) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Heap) (var16 Heap) (var17 Addr) (var18 Addr) (var19 Heap)) (or (not (and (inv_main2409_5 var19 var18 var17) (and (and (and (and (and (= var16 var15) (= var14 var13)) (= var12 var11)) (= var10 (|sll::next| (getsll (read var15 var11))))) (and (and (and (and (and (= var9 (newHeap (alloc var19 (O_sll var8)))) (= var7 var18)) (= var6 var17)) (= var5 (newAddr (alloc var19 (O_sll var8))))) (and (and (and (= var4 (write var9 var5 (O_sll (sll (|sll::data| (getsll (read var9 var5))) nullAddr)))) (= var3 var7)) (= var2 var6)) (= var1 var5))) (not (= var0 0)))) (and (and (= var15 (write var4 var2 (O_sll (sll (|sll::data| (getsll (read var4 var2))) var1)))) (= var13 var3)) (= var11 var2))))) (inv_main2409_5 var16 var14 var10))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 sll) (var4 Heap) (var5 Heap)) (or (not (and (inv_main2433_5 var5) (and (and (= var4 (newHeap (alloc var5 (O_sll var3)))) (= var2 (newAddr (alloc var5 (O_sll var3))))) (and (= var1 (write var4 var2 (O_sll (sll (|sll::data| (getsll (read var4 var2))) nullAddr)))) (= var0 var2))))) (inv_main2409_5 var1 var0 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main2426_9 var9 var8 var7 var6 var5) (and (= var4 nullAddr) (and (and (and (and (= var3 (write var9 var6 defObj)) (= var2 var8)) (= var1 var7)) (= var0 var6)) (= var4 var5))))) (inv_main_12 var3 var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main2436_5 var4 var3 var2 var1 var0) (and (= var3 nullAddr) (= var1 nullAddr)))) (inv_main_12 var4 var3 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main2426_9 var10 var9 var8 var7 var6) (and (and (not (= var5 nullAddr)) (and (and (and (and (= var4 (write var10 var7 defObj)) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var5 var6))) (= var0 (|sll::next| (getsll (read var4 var5))))))) (inv_main2426_9 var4 var3 var2 var5 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main2436_5 var5 var4 var3 var2 var1) (and (and (not (= var4 nullAddr)) (= var2 nullAddr)) (= var0 (|sll::next| (getsll (read var5 var4))))))) (inv_main2426_9 var5 var4 var3 var4 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main2426_9 var4 var3 var2 var1 var0) (and (not (= var1 nullAddr)) (= (read var4 var1) defObj))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_12 var2 var1 var0) (and (not (= var0 nullAddr)) (= (read var2 var0) defObj))))))
(check-sat)
