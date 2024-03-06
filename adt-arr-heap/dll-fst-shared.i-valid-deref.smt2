(set-logic HORN)
(set-info :source |
    Benchmark: C_VC
    Output by Princess (http://www.philipp.ruemmer.org/princess.shtml)
|)
(set-info :status sat)
(declare-heap Heap Addr HeapObject
 defObj
 ((HeapObject 0) (dll 0)) (
  (
   (O_Int (getInt Int))
   (O_UInt (getUInt Int))
   (O_Addr (getAddr Addr))
   (O_AddrRange (getAddrRange AddrRange))
   (O_dll (getdll dll))
   (defObj)
  )
  (
   (dll (|dll::next| Addr) (|dll::prev| Addr) (|dll::data| Addr))
  )
))
(declare-fun inv_main (Heap Addr) Bool)
(declare-fun inv_main2396_1_7 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main2398_5 (Heap Addr) Bool)
(declare-fun inv_main2398_5_8 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main2412_13 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main2424_5_15 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main2426_9 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main2432_9 (Heap Addr Addr) Bool)
(declare-fun inv_main2442_5 (Heap) Bool)
(declare-fun inv_main_11 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main_12 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main_14 (Heap Addr) Bool)
(declare-fun inv_main_16 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main_2 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main_20 (Heap Addr Addr) Bool)
(declare-fun inv_main_6 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main_9 (Heap Addr Addr Addr Addr) Bool)
(assert (forall ((var0 Heap)) (or (not (= var0 emptyHeap)) (inv_main2442_5 var0))))
(assert (forall ((var0 Addr) (var1 Heap)) (or (not (and (inv_main_14 var1 var0) (not (= var0 nullAddr)))) (inv_main2432_9 var1 var0 var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Heap)) (or (not (and (inv_main2398_5 var2 var1) (and (and (is-O_dll (read var2 var1)) (is-O_dll (read var2 var1))) (= var0 (write var2 var1 (O_dll (dll nullAddr (|dll::prev| (getdll (read var2 var1))) (|dll::data| (getdll (read var2 var1)))))))))) (inv_main var0 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main_16 var8 var7 var6 var5) (and (not (= var4 nullAddr)) (and (is-O_dll (read var8 var5)) (and (and (and (and (= var3 var8) (= var2 var7)) (= var1 var6)) (= var0 var5)) (= var4 (|dll::next| (getdll (read var8 var5))))))))) (inv_main2424_5_15 var3 var2 var1 var4))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Int) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main_2 var8 var7 var6 var5) (and (not (= var4 nullAddr)) (and (and (= var3 0) (and (is-O_dll (read var8 var6)) (is-O_dll (read var8 var6)))) (and (and (and (= var2 (write var8 var6 (O_dll (dll (|dll::next| (getdll (read var8 var6))) (|dll::prev| (getdll (read var8 var6))) var5)))) (= var4 var7)) (= var1 var6)) (= var0 var5)))))) (inv_main2424_5_15 var2 var4 var4 var4))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main_12 var9 var8 var7 var6) (and (not (= var5 nullAddr)) (and (= var4 0) (and (is-O_dll (read var9 var7)) (and (and (and (and (= var3 var9) (= var5 var8)) (= var2 var7)) (= var1 var6)) (= var0 (|dll::next| (getdll (read var9 var7)))))))))) (inv_main2424_5_15 var3 var5 var5 var5))))
(assert (forall ((var0 Addr) (var1 dll) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Int) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Heap)) (or (not (and (inv_main_2 var11 var10 var9 var8) (and (and (and (and (not (= var7 0)) (and (is-O_dll (read var11 var9)) (is-O_dll (read var11 var9)))) (and (and (and (= var6 (write var11 var9 (O_dll (dll (|dll::next| (getdll (read var11 var9))) (|dll::prev| (getdll (read var11 var9))) var8)))) (= var5 var10)) (= var4 var9)) (= var3 var8))) (= var2 (newHeap (alloc var6 (O_dll var1))))) (= var0 (newAddr (alloc var6 (O_dll var1))))))) (inv_main2398_5_8 var2 var5 var4 var3 var0))))
(assert (forall ((var0 Addr) (var1 dll) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Int) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Heap)) (or (not (and (inv_main_12 var12 var11 var10 var9) (and (and (and (not (= var8 0)) (and (is-O_dll (read var12 var10)) (and (and (and (and (= var7 var12) (= var6 var11)) (= var5 var10)) (= var4 var9)) (= var3 (|dll::next| (getdll (read var12 var10))))))) (= var2 (newHeap (alloc var7 (O_dll var1))))) (= var0 (newAddr (alloc var7 (O_dll var1))))))) (inv_main2398_5_8 var2 var6 var3 var4 var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main_11 var4 var3 var2 var1) (and (and (and (is-O_dll (read var4 var2)) (is-O_dll (read var4 (|dll::next| (getdll (read var4 var2)))))) (is-O_dll (read var4 (|dll::next| (getdll (read var4 var2)))))) (= var0 (write var4 (|dll::next| (getdll (read var4 var2))) (O_dll (dll (|dll::next| (getdll (read var4 (|dll::next| (getdll (read var4 var2)))))) (|dll::prev| (getdll (read var4 (|dll::next| (getdll (read var4 var2)))))) var1))))))) (inv_main_12 var0 var3 var2 var1))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main2398_5_8 var5 var4 var3 var2 var1) (and (and (is-O_dll (read var5 var1)) (is-O_dll (read var5 var1))) (= var0 (write var5 var1 (O_dll (dll nullAddr (|dll::prev| (getdll (read var5 var1))) (|dll::data| (getdll (read var5 var1)))))))))) (inv_main_9 var0 var4 var3 var2 var1))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main2396_1_7 var5 var4 var3 var2 var1) (and (and (is-O_dll (read var5 var3)) (is-O_dll (read var5 var3))) (= var0 (write var5 var3 (O_dll (dll var1 (|dll::prev| (getdll (read var5 var3))) (|dll::data| (getdll (read var5 var3)))))))))) (inv_main_6 var0 var4 var3 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main2424_5_15 var4 var3 var2 var1) (and (is-O_dll (read var4 var2)) (= var0 (|dll::data| (getdll (read var4 var2))))))) (inv_main2426_9 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main_9 var9 var8 var7 var6 var5) (and (and (is-O_dll (read var9 var5)) (is-O_dll (read var9 var5))) (and (and (and (and (= var4 (write var9 var5 (O_dll (dll (|dll::next| (getdll (read var9 var5))) nullAddr (|dll::data| (getdll (read var9 var5))))))) (= var3 var8)) (= var2 var7)) (= var1 var6)) (= var0 var5))))) (inv_main2396_1_7 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main_6 var4 var3 var2 var1) (and (and (and (is-O_dll (read var4 var2)) (is-O_dll (read var4 (|dll::next| (getdll (read var4 var2)))))) (is-O_dll (read var4 (|dll::next| (getdll (read var4 var2)))))) (= var0 (write var4 (|dll::next| (getdll (read var4 var2))) (O_dll (dll (|dll::next| (getdll (read var4 (|dll::next| (getdll (read var4 var2)))))) var2 (|dll::data| (getdll (read var4 (|dll::next| (getdll (read var4 var2))))))))))))) (inv_main_11 var0 var3 var2 var1))))
(assert (forall ((var0 Int) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main2412_13 var5 var4 var3 var2) (and (and (is-O_Int (read var5 var2)) (is-O_Int (read var5 var2))) (= var1 (write var5 var2 (O_Int var0)))))) (inv_main_2 var1 var4 var3 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main2426_9 var4 var3 var2 var1 var0) (is-O_Int (read var4 var0)))) (inv_main_16 var4 var3 var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main_16 var8 var7 var6 var5) (and (= var4 nullAddr) (and (is-O_dll (read var8 var5)) (and (and (and (and (= var3 var8) (= var2 var7)) (= var1 var6)) (= var0 var5)) (= var4 (|dll::next| (getdll (read var8 var5))))))))) (inv_main_14 var3 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Int) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main_2 var8 var7 var6 var5) (and (= var4 nullAddr) (and (and (= var3 0) (and (is-O_dll (read var8 var6)) (is-O_dll (read var8 var6)))) (and (and (and (= var2 (write var8 var6 (O_dll (dll (|dll::next| (getdll (read var8 var6))) (|dll::prev| (getdll (read var8 var6))) var5)))) (= var4 var7)) (= var1 var6)) (= var0 var5)))))) (inv_main_14 var2 var4))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main_12 var9 var8 var7 var6) (and (= var5 nullAddr) (and (= var4 0) (and (is-O_dll (read var9 var7)) (and (and (and (and (= var3 var9) (= var5 var8)) (= var2 var7)) (= var1 var6)) (= var0 (|dll::next| (getdll (read var9 var7)))))))))) (inv_main_14 var3 var5))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main2432_9 var5 var4 var3) (and (and (not (= var2 nullAddr)) (is-O_dll (read var5 var3))) (and (and (= var1 (write var5 (|dll::data| (getdll (read var5 var3))) defObj)) (= var0 var4)) (= var2 var3))))) (inv_main_20 var1 var0 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main_20 var10 var9 var8) (and (not (= var7 nullAddr)) (and (and (is-O_dll (read var10 var8)) (and (and (and (= var6 var10) (= var5 var9)) (= var4 var8)) (= var3 (|dll::next| (getdll (read var10 var8)))))) (and (and (and (= var2 (write var6 var4 defObj)) (= var1 var5)) (= var0 var4)) (= var7 var3)))))) (inv_main_20 var2 var1 var7))))
(assert (forall ((var0 Addr) (var1 Heap)) (or (not (and (inv_main_14 var1 var0) (and (not (= var0 nullAddr)) (= var0 nullAddr)))) (inv_main_20 var1 var0 var0))))
(assert (forall ((var0 Addr) (var1 dll) (var2 Heap) (var3 Heap)) (or (not (and (inv_main2442_5 var3) (and (= var2 (newHeap (alloc var3 (O_dll var1)))) (= var0 (newAddr (alloc var3 (O_dll var1))))))) (inv_main2398_5 var2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap) (var6 Heap) (var7 Addr) (var8 Heap)) (or (not (and (inv_main var8 var7) (and (and (and (and (= var6 (newHeap (alloc var5 (O_Int var4)))) (= var3 var2)) (= var1 var2)) (= var0 (newAddr (alloc var5 (O_Int var4))))) (and (and (is-O_dll (read var8 var7)) (is-O_dll (read var8 var7))) (and (= var5 (write var8 var7 (O_dll (dll (|dll::next| (getdll (read var8 var7))) nullAddr (|dll::data| (getdll (read var8 var7))))))) (= var2 var7)))))) (inv_main2412_13 var6 var3 var1 var0))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main2398_5 var1 var0) (not (is-O_dll (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main2398_5 var1 var0) (and (is-O_dll (read var1 var0)) (not (is-O_dll (read var1 var0))))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main var1 var0) (not (is-O_dll (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main var1 var0) (and (is-O_dll (read var1 var0)) (not (is-O_dll (read var1 var0))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main2412_13 var3 var2 var1 var0) (not (is-O_Int (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main2412_13 var3 var2 var1 var0) (and (is-O_Int (read var3 var0)) (not (is-O_Int (read var3 var0))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_2 var3 var2 var1 var0) (not (is-O_dll (read var3 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_2 var3 var2 var1 var0) (and (is-O_dll (read var3 var1)) (not (is-O_dll (read var3 var1))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main2398_5_8 var4 var3 var2 var1 var0) (not (is-O_dll (read var4 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main2398_5_8 var4 var3 var2 var1 var0) (and (is-O_dll (read var4 var0)) (not (is-O_dll (read var4 var0))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main_9 var4 var3 var2 var1 var0) (not (is-O_dll (read var4 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main_9 var4 var3 var2 var1 var0) (and (is-O_dll (read var4 var0)) (not (is-O_dll (read var4 var0))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main2396_1_7 var4 var3 var2 var1 var0) (not (is-O_dll (read var4 var2)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main2396_1_7 var4 var3 var2 var1 var0) (and (is-O_dll (read var4 var2)) (not (is-O_dll (read var4 var2))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_6 var3 var2 var1 var0) (not (is-O_dll (read var3 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_6 var3 var2 var1 var0) (and (is-O_dll (read var3 var1)) (not (is-O_dll (read var3 (|dll::next| (getdll (read var3 var1)))))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_6 var3 var2 var1 var0) (and (and (is-O_dll (read var3 var1)) (is-O_dll (read var3 (|dll::next| (getdll (read var3 var1)))))) (not (is-O_dll (read var3 (|dll::next| (getdll (read var3 var1)))))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_11 var3 var2 var1 var0) (not (is-O_dll (read var3 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_11 var3 var2 var1 var0) (and (is-O_dll (read var3 var1)) (not (is-O_dll (read var3 (|dll::next| (getdll (read var3 var1)))))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_11 var3 var2 var1 var0) (and (and (is-O_dll (read var3 var1)) (is-O_dll (read var3 (|dll::next| (getdll (read var3 var1)))))) (not (is-O_dll (read var3 (|dll::next| (getdll (read var3 var1)))))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_12 var3 var2 var1 var0) (not (is-O_dll (read var3 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main2424_5_15 var3 var2 var1 var0) (not (is-O_dll (read var3 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main2426_9 var4 var3 var2 var1 var0) (not (is-O_Int (read var4 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_16 var3 var2 var1 var0) (not (is-O_dll (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main2432_9 var2 var1 var0) (not (is-O_dll (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_20 var2 var1 var0) (not (is-O_dll (read var2 var0)))))))
(check-sat)
