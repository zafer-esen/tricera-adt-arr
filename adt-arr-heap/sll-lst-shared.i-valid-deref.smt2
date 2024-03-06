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
(declare-fun inv_main2395_1_6 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main2397_5 (Heap Addr) Bool)
(declare-fun inv_main2397_5_7 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main2410_13 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main2422_9 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main2428_9 (Heap Addr Addr) Bool)
(declare-fun inv_main2438_5 (Heap) Bool)
(declare-fun inv_main2439_5_12 (Heap Addr Addr) Bool)
(declare-fun inv_main_1 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main_11 (Heap Addr) Bool)
(declare-fun inv_main_13 (Heap Addr Addr) Bool)
(declare-fun inv_main_17 (Heap Addr Addr) Bool)
(declare-fun inv_main_5 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main_9 (Heap Addr Addr Addr) Bool)
(assert (forall ((var0 Heap)) (or (not (= var0 emptyHeap)) (inv_main2438_5 var0))))
(assert (forall ((var0 Int) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main2410_13 var5 var4 var3 var2) (and (and (is-O_Int (read var5 var2)) (is-O_Int (read var5 var2))) (= var1 (write var5 var2 (O_Int var0)))))) (inv_main_1 var1 var4 var3 var2))))
(assert (forall ((var0 Addr) (var1 Heap)) (or (not (and (inv_main_11 var1 var0) (not (= var0 nullAddr)))) (inv_main2428_9 var1 var0 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main_13 var6 var5 var4) (and (not (= var3 nullAddr)) (and (is-O_sll (read var6 var4)) (and (and (and (= var2 var6) (= var1 var5)) (= var0 var4)) (= var3 (|sll::next| (getsll (read var6 var4))))))))) (inv_main2439_5_12 var2 var1 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Int) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main_1 var8 var7 var6 var5) (and (not (= var4 nullAddr)) (and (and (= var3 0) (and (is-O_sll (read var8 var6)) (is-O_sll (read var8 var6)))) (and (and (and (= var2 (write var8 var6 (O_sll (sll var5 (|sll::next| (getsll (read var8 var6))))))) (= var4 var7)) (= var1 var6)) (= var0 var5)))))) (inv_main2439_5_12 var2 var4 var4))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main_9 var9 var8 var7 var6) (and (not (= var5 nullAddr)) (and (= var4 0) (and (is-O_sll (read var9 var7)) (and (and (and (and (= var3 var9) (= var5 var8)) (= var2 var7)) (= var1 var6)) (= var0 (|sll::next| (getsll (read var9 var7)))))))))) (inv_main2439_5_12 var3 var5 var5))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main2395_1_6 var5 var4 var3 var2 var1) (and (and (is-O_sll (read var5 var3)) (is-O_sll (read var5 var3))) (= var0 (write var5 var3 (O_sll (sll (|sll::data| (getsll (read var5 var3))) var1))))))) (inv_main_5 var0 var4 var3 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap) (var6 Heap) (var7 Addr) (var8 Heap)) (or (not (and (inv_main2397_5 var8 var7) (and (and (and (and (= var6 (newHeap (alloc var5 (O_Int var4)))) (= var3 var2)) (= var1 var2)) (= var0 (newAddr (alloc var5 (O_Int var4))))) (and (and (is-O_sll (read var8 var7)) (is-O_sll (read var8 var7))) (and (= var5 (write var8 var7 (O_sll (sll (|sll::data| (getsll (read var8 var7))) nullAddr)))) (= var2 var7)))))) (inv_main2410_13 var6 var3 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main2439_5_12 var3 var2 var1) (and (is-O_sll (read var3 var1)) (= var0 (|sll::data| (getsll (read var3 var1))))))) (inv_main2422_9 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main_13 var6 var5 var4) (and (= var3 nullAddr) (and (is-O_sll (read var6 var4)) (and (and (and (= var2 var6) (= var1 var5)) (= var0 var4)) (= var3 (|sll::next| (getsll (read var6 var4))))))))) (inv_main_11 var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Int) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main_1 var8 var7 var6 var5) (and (= var4 nullAddr) (and (and (= var3 0) (and (is-O_sll (read var8 var6)) (is-O_sll (read var8 var6)))) (and (and (and (= var2 (write var8 var6 (O_sll (sll var5 (|sll::next| (getsll (read var8 var6))))))) (= var4 var7)) (= var1 var6)) (= var0 var5)))))) (inv_main_11 var2 var4))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main_9 var9 var8 var7 var6) (and (= var5 nullAddr) (and (= var4 0) (and (is-O_sll (read var9 var7)) (and (and (and (and (= var3 var9) (= var5 var8)) (= var2 var7)) (= var1 var6)) (= var0 (|sll::next| (getsll (read var9 var7)))))))))) (inv_main_11 var3 var5))))
(assert (forall ((var0 Addr) (var1 sll) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Int) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Heap)) (or (not (and (inv_main_1 var11 var10 var9 var8) (and (and (and (and (not (= var7 0)) (and (is-O_sll (read var11 var9)) (is-O_sll (read var11 var9)))) (and (and (and (= var6 (write var11 var9 (O_sll (sll var8 (|sll::next| (getsll (read var11 var9))))))) (= var5 var10)) (= var4 var9)) (= var3 var8))) (= var2 (newHeap (alloc var6 (O_sll var1))))) (= var0 (newAddr (alloc var6 (O_sll var1))))))) (inv_main2397_5_7 var2 var5 var4 var3 var0))))
(assert (forall ((var0 Addr) (var1 sll) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Int) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Heap)) (or (not (and (inv_main_9 var12 var11 var10 var9) (and (and (and (not (= var8 0)) (and (is-O_sll (read var12 var10)) (and (and (and (and (= var7 var12) (= var6 var11)) (= var5 var10)) (= var4 var9)) (= var3 (|sll::next| (getsll (read var12 var10))))))) (= var2 (newHeap (alloc var7 (O_sll var1))))) (= var0 (newAddr (alloc var7 (O_sll var1))))))) (inv_main2397_5_7 var2 var6 var3 var4 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main2397_5_7 var9 var8 var7 var6 var5) (and (and (is-O_sll (read var9 var5)) (is-O_sll (read var9 var5))) (and (and (and (and (= var4 (write var9 var5 (O_sll (sll (|sll::data| (getsll (read var9 var5))) nullAddr)))) (= var3 var8)) (= var2 var7)) (= var1 var6)) (= var0 var5))))) (inv_main2395_1_6 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 sll) (var2 Heap) (var3 Heap)) (or (not (and (inv_main2438_5 var3) (and (= var2 (newHeap (alloc var3 (O_sll var1)))) (= var0 (newAddr (alloc var3 (O_sll var1))))))) (inv_main2397_5 var2 var0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main2428_9 var5 var4 var3) (and (and (not (= var2 nullAddr)) (is-O_sll (read var5 var3))) (and (and (= var1 (write var5 (|sll::data| (getsll (read var5 var3))) defObj)) (= var0 var4)) (= var2 var3))))) (inv_main_17 var1 var0 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main_17 var10 var9 var8) (and (not (= var7 nullAddr)) (and (and (is-O_sll (read var10 var8)) (and (and (and (= var6 var10) (= var5 var9)) (= var4 var8)) (= var3 (|sll::next| (getsll (read var10 var8)))))) (and (and (and (= var2 (write var6 var4 defObj)) (= var1 var5)) (= var0 var4)) (= var7 var3)))))) (inv_main_17 var2 var1 var7))))
(assert (forall ((var0 Addr) (var1 Heap)) (or (not (and (inv_main_11 var1 var0) (and (not (= var0 nullAddr)) (= var0 nullAddr)))) (inv_main_17 var1 var0 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main2422_9 var3 var2 var1 var0) (is-O_Int (read var3 var0)))) (inv_main_13 var3 var2 var1))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main_5 var4 var3 var2 var1) (and (and (and (is-O_sll (read var4 var2)) (is-O_sll (read var4 (|sll::next| (getsll (read var4 var2)))))) (is-O_sll (read var4 (|sll::next| (getsll (read var4 var2)))))) (= var0 (write var4 (|sll::next| (getsll (read var4 var2))) (O_sll (sll var1 (|sll::next| (getsll (read var4 (|sll::next| (getsll (read var4 var2))))))))))))) (inv_main_9 var0 var3 var2 var1))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main2397_5 var1 var0) (not (is-O_sll (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main2397_5 var1 var0) (and (is-O_sll (read var1 var0)) (not (is-O_sll (read var1 var0))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main2410_13 var3 var2 var1 var0) (not (is-O_Int (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main2410_13 var3 var2 var1 var0) (and (is-O_Int (read var3 var0)) (not (is-O_Int (read var3 var0))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_1 var3 var2 var1 var0) (not (is-O_sll (read var3 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_1 var3 var2 var1 var0) (and (is-O_sll (read var3 var1)) (not (is-O_sll (read var3 var1))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main2397_5_7 var4 var3 var2 var1 var0) (not (is-O_sll (read var4 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main2397_5_7 var4 var3 var2 var1 var0) (and (is-O_sll (read var4 var0)) (not (is-O_sll (read var4 var0))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main2395_1_6 var4 var3 var2 var1 var0) (not (is-O_sll (read var4 var2)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main2395_1_6 var4 var3 var2 var1 var0) (and (is-O_sll (read var4 var2)) (not (is-O_sll (read var4 var2))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_5 var3 var2 var1 var0) (not (is-O_sll (read var3 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_5 var3 var2 var1 var0) (and (is-O_sll (read var3 var1)) (not (is-O_sll (read var3 (|sll::next| (getsll (read var3 var1)))))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_5 var3 var2 var1 var0) (and (and (is-O_sll (read var3 var1)) (is-O_sll (read var3 (|sll::next| (getsll (read var3 var1)))))) (not (is-O_sll (read var3 (|sll::next| (getsll (read var3 var1)))))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_9 var3 var2 var1 var0) (not (is-O_sll (read var3 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main2439_5_12 var2 var1 var0) (not (is-O_sll (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main2422_9 var3 var2 var1 var0) (not (is-O_Int (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_13 var2 var1 var0) (not (is-O_sll (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main2428_9 var2 var1 var0) (not (is-O_sll (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_17 var2 var1 var0) (not (is-O_sll (read var2 var0)))))))
(check-sat)