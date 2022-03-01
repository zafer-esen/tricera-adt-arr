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
   (O_TSLL (getTSLL TSLL))
   (defObj)
  )
  (
   (TSLL (next Addr) (data Int))
  )
))
(declare-fun inv_main10 (Heap Addr Addr) Bool)
(declare-fun inv_main11 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main12 (Heap Addr Addr) Bool)
(declare-fun inv_main14 (Heap Addr Addr) Bool)
(declare-fun inv_main15 (Heap Addr Addr) Bool)
(declare-fun inv_main2 (Heap) Bool)
(declare-fun inv_main21 (Heap Addr Addr) Bool)
(declare-fun inv_main23 (Heap Addr Addr) Bool)
(declare-fun inv_main27 (Heap Addr Addr) Bool)
(declare-fun inv_main29 (Heap Addr Addr) Bool)
(declare-fun inv_main3 (Heap Addr) Bool)
(declare-fun inv_main32 (Heap Addr Addr) Bool)
(declare-fun inv_main35 (Heap Addr Addr) Bool)
(declare-fun inv_main37 (Heap Addr Addr) Bool)
(declare-fun inv_main38 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main39 (Heap Addr Addr) Bool)
(declare-fun inv_main4 (Heap Addr) Bool)
(declare-fun inv_main41 (Heap Addr Addr) Bool)
(declare-fun inv_main45 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main46 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main50 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main52 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main56 (Heap Addr Addr Addr Int Int) Bool)
(declare-fun inv_main59 (Heap Addr Addr Addr Int Int) Bool)
(declare-fun inv_main61 (Heap Addr Addr Addr Int Int) Bool)
(declare-fun inv_main64 (Heap Addr Addr Addr Int Int) Bool)
(declare-fun inv_main65 (Heap Addr Addr Addr Int Int) Bool)
(declare-fun inv_main73 (Heap Addr Addr Addr) Bool)
(assert (inv_main2 emptyHeap))
(assert (forall ((var0 TSLL) (var1 Heap)) (or (not (inv_main2 var1)) (inv_main3 (newHeap (alloc var1 (O_TSLL var0))) (newAddr (alloc var1 (O_TSLL var0)))))))
(assert (forall ((var0 Addr) (var1 Heap)) (or (not (and (inv_main3 var1 var0) (is-O_TSLL (read var1 var0)))) (inv_main4 (write var1 var0 (O_TSLL (TSLL nullAddr (data (getTSLL (read var1 var0)))))) var0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main15 var6 var5 var4) (and (= var3 nullAddr) (and (and (= var2 nullAddr) (is-O_TSLL (read var6 var4))) (and (and (and (= var1 var6) (= var0 var5)) (= var3 var4)) (= var2 (next (getTSLL (read var6 var4))))))))) (inv_main29 var1 var0 var3))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Int) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main15 var7 var6 var5) (and (= var4 nullAddr) (and (= var3 0) (and (and (not (= var2 nullAddr)) (is-O_TSLL (read var7 var5))) (and (and (and (= var1 var7) (= var0 var6)) (= var4 var5)) (= var2 (next (getTSLL (read var7 var5)))))))))) (inv_main29 var1 var0 var4))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main52 var8 var7 var6 var5) (and (and (= var4 2) (is-O_TSLL (read var8 var6))) (and (and (and (and (= var3 var8) (= var2 var7)) (= var1 var6)) (= var0 var5)) (= var4 (data (getTSLL (read var8 var6)))))))) (inv_main56 var3 var2 var1 var0 var4 0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main15 var6 var5 var4) (and (not (= var3 nullAddr)) (and (and (= var2 nullAddr) (is-O_TSLL (read var6 var4))) (and (and (and (= var1 var6) (= var0 var5)) (= var3 var4)) (= var2 (next (getTSLL (read var6 var4))))))))) (inv_main27 var1 var0 var3))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Int) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main15 var7 var6 var5) (and (not (= var4 nullAddr)) (and (= var3 0) (and (and (not (= var2 nullAddr)) (is-O_TSLL (read var7 var5))) (and (and (and (= var1 var7) (= var0 var6)) (= var4 var5)) (= var2 (next (getTSLL (read var7 var5)))))))))) (inv_main27 var1 var0 var4))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main37 var6 var5 var4) (and (is-O_TSLL (read var6 var4)) (and (and (and (= var3 var6) (= var2 var5)) (= var1 var4)) (= var0 (next (getTSLL (read var6 var4)))))))) (inv_main39 var3 var2 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Int) (var6 Int) (var7 Int) (var8 Int) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Heap)) (or (not (and (inv_main56 var12 var11 var10 var9 var8 var7) (and (or (not (= var6 2)) (= var5 1)) (and (and (is-O_TSLL (read var12 var10)) (is-O_TSLL (read var12 (next (getTSLL (read var12 var10)))))) (and (and (and (and (and (and (= var4 var12) (= var3 var11)) (= var2 var10)) (= var1 var9)) (= var6 var8)) (= var0 var7)) (= var5 (data (getTSLL (read var12 (next (getTSLL (read var12 var10)))))))))))) (inv_main59 var4 var3 var2 var1 var6 var5))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main52 var8 var7 var6 var5) (and (and (and (not (= var4 2)) (not (= var4 2))) (is-O_TSLL (read var8 var6))) (and (and (and (and (= var3 var8) (= var2 var7)) (= var1 var6)) (= var0 var5)) (= var4 (data (getTSLL (read var8 var6)))))))) (inv_main59 var3 var2 var1 var0 var4 0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main38 var3 var2 var1 var0) (is-O_TSLL (read var3 var1)))) (inv_main37 (write var3 var1 (O_TSLL (TSLL var0 (data (getTSLL (read var3 var1)))))) var2 var1))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Int) (var7 Int) (var8 Int) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Heap)) (or (not (and (inv_main59 var12 var11 var10 var9 var8 var7) (and (and (= var6 2) (is-O_TSLL (read var12 var10))) (and (and (and (and (and (and (= var5 var12) (= var4 var11)) (= var3 var10)) (= var2 var9)) (= var1 var8)) (= var0 var7)) (= var6 (data (getTSLL (read var12 var10)))))))) (inv_main65 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main32 var6 var5 var4) (and (and (not (= var3 nullAddr)) (is-O_TSLL (read var6 var4))) (and (and (and (= var2 var6) (= var1 var5)) (= var0 var4)) (= var3 (next (getTSLL (read var6 var4)))))))) (inv_main35 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main10 var6 var5 var4) (and (is-O_TSLL (read var6 var4)) (and (and (and (= var3 var6) (= var2 var5)) (= var1 var4)) (= var0 (next (getTSLL (read var6 var4)))))))) (inv_main12 var3 var2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (and (inv_main27 var2 var1 var0) (is-O_TSLL (read var2 var0)))) (inv_main32 (write var2 var0 (O_TSLL (TSLL (next (getTSLL (read var2 var0))) 1))) var1 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Int) (var8 Int) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Heap)) (or (not (and (inv_main65 var12 var11 var10 var9 var8 var7) (and (is-O_TSLL (read var12 var10)) (and (and (and (and (and (and (= var6 var12) (= var5 var11)) (= var4 var10)) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var0 (next (getTSLL (read var12 var10)))))))) (inv_main64 var6 var5 var0 var3 var2 var1))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Int) (var7 Int) (var8 Int) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Heap)) (or (not (and (inv_main59 var12 var11 var10 var9 var8 var7) (and (and (not (= var6 2)) (is-O_TSLL (read var12 var10))) (and (and (and (and (and (and (= var5 var12) (= var4 var11)) (= var3 var10)) (= var2 var9)) (= var1 var8)) (= var0 var7)) (= var6 (data (getTSLL (read var12 var10)))))))) (inv_main64 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Int) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main15 var7 var6 var5) (and (not (= var4 nullAddr)) (and (not (= var3 0)) (and (and (not (= var2 nullAddr)) (is-O_TSLL (read var7 var5))) (and (and (and (= var1 var7) (= var0 var6)) (= var4 var5)) (= var2 (next (getTSLL (read var7 var5)))))))))) (inv_main21 var1 var0 var4))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main46 var9 var8 var7 var6 var5) (and (not (= var4 nullAddr)) (and (is-O_TSLL (read var9 var7)) (and (and (and (and (= var3 (write var9 var7 (O_TSLL (TSLL var6 (data (getTSLL (read var9 var7))))))) (= var2 var8)) (= var1 var7)) (= var0 var6)) (= var4 var5)))))) (inv_main45 var3 var2 var4 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main41 var9 var8 var7) (and (and (and (not (= var6 nullAddr)) (and (and (and (= var5 var4) (= var6 var3)) (= var2 var1)) (= var0 nullAddr))) (is-O_TSLL (read var9 var7))) (and (and (= var4 (write var9 var7 (O_TSLL (TSLL (next (getTSLL (read var9 var7))) 2)))) (= var3 var8)) (= var1 var7))))) (inv_main45 var5 var6 var6 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main35 var9 var8 var7) (and (and (and (not (= var6 nullAddr)) (and (and (and (= var5 var4) (= var6 var3)) (= var2 var1)) (= var0 nullAddr))) (and (is-O_TSLL (read var9 var7)) (is-O_TSLL (read var9 (next (getTSLL (read var9 var7))))))) (and (and (= var4 (write var9 (next (getTSLL (read var9 var7))) (O_TSLL (TSLL (next (getTSLL (read var9 (next (getTSLL (read var9 var7)))))) 2)))) (= var3 var8)) (= var1 var7))))) (inv_main45 var5 var6 var6 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (and (inv_main39 var2 var1 var0) (is-O_TSLL (read var2 var0)))) (inv_main41 (write var2 var0 (O_TSLL (TSLL nullAddr (data (getTSLL (read var2 var0)))))) var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main50 var3 var2 var1 var0) (and (not (= var2 nullAddr)) (= var1 nullAddr)))) (inv_main73 var3 var2 var2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Heap)) (or (not (and (inv_main73 var12 var11 var10 var9) (and (and (not (= var8 nullAddr)) (and (is-O_TSLL (read var12 var10)) (and (and (and (and (= var7 var12) (= var6 var11)) (= var5 var10)) (= var4 var9)) (= var3 (next (getTSLL (read var12 var10))))))) (and (and (and (= var2 (write var7 var6 defObj)) (= var1 var6)) (= var8 var3)) (= var0 var4))))) (inv_main73 var2 var8 var8 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main50 var3 var2 var1 var0) (not (= var1 nullAddr)))) (inv_main52 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main45 var3 var2 var1 var0) (is-O_TSLL (read var3 var1)))) (inv_main46 var3 var2 var1 var0 (next (getTSLL (read var3 var1)))))))
(assert (forall ((var0 TSLL) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main14 var7 var6 var5) (and (and (not (= var4 0)) (is-O_TSLL (read var7 var5))) (and (and (= var3 (write var7 var5 (O_TSLL (TSLL (next (getTSLL (read var7 var5))) 0)))) (= var2 var6)) (= var1 var5))))) (inv_main11 (newHeap (alloc var3 (O_TSLL var0))) var2 var1 (newAddr (alloc var3 (O_TSLL var0)))))))
(assert (forall ((var0 TSLL) (var1 Addr) (var2 Heap) (var3 Int) (var4 Addr) (var5 Heap)) (or (not (and (inv_main4 var5 var4) (and (and (not (= var3 0)) (is-O_TSLL (read var5 var4))) (and (= var2 (write var5 var4 (O_TSLL (TSLL (next (getTSLL (read var5 var4))) 0)))) (= var1 var4))))) (inv_main11 (newHeap (alloc var2 (O_TSLL var0))) var1 var1 (newAddr (alloc var2 (O_TSLL var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (and (inv_main12 var2 var1 var0) (is-O_TSLL (read var2 var0)))) (inv_main14 (write var2 var0 (O_TSLL (TSLL nullAddr (data (getTSLL (read var2 var0)))))) var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main21 var6 var5 var4) (and (is-O_TSLL (read var6 var4)) (and (and (and (= var3 var6) (= var2 var5)) (= var1 var4)) (= var0 (next (getTSLL (read var6 var4)))))))) (inv_main15 var3 var2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Int) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main14 var6 var5 var4) (and (and (= var3 0) (is-O_TSLL (read var6 var4))) (and (and (= var2 (write var6 var4 (O_TSLL (TSLL (next (getTSLL (read var6 var4))) 0)))) (= var1 var5)) (= var0 var4))))) (inv_main15 var2 var1 var1))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Addr) (var4 Heap)) (or (not (and (inv_main4 var4 var3) (and (and (= var2 0) (is-O_TSLL (read var4 var3))) (and (= var1 (write var4 var3 (O_TSLL (TSLL (next (getTSLL (read var4 var3))) 0)))) (= var0 var3))))) (inv_main15 var1 var0 var0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Int) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main15 var7 var6 var5) (and (= var4 nullAddr) (and (not (= var3 0)) (and (and (not (= var2 nullAddr)) (is-O_TSLL (read var7 var5))) (and (and (and (= var1 var7) (= var0 var6)) (= var4 var5)) (= var2 (next (getTSLL (read var7 var5)))))))))) (inv_main23 var1 var0 var4))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Int) (var8 Int) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Heap)) (or (not (and (inv_main64 var12 var11 var10 var9 var8 var7) (and (is-O_TSLL (read var12 var10)) (and (and (and (and (and (and (= var6 var12) (= var5 var11)) (= var4 var10)) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var0 (next (getTSLL (read var12 var10)))))))) (inv_main50 var6 var5 var0 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main46 var9 var8 var7 var6 var5) (and (= var4 nullAddr) (and (is-O_TSLL (read var9 var7)) (and (and (and (and (= var3 (write var9 var7 (O_TSLL (TSLL var6 (data (getTSLL (read var9 var7))))))) (= var2 var8)) (= var1 var7)) (= var0 var6)) (= var4 var5)))))) (inv_main50 var3 var1 var1 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main41 var9 var8 var7) (and (and (and (= var6 nullAddr) (and (and (and (= var5 var4) (= var6 var3)) (= var2 var1)) (= var0 nullAddr))) (is-O_TSLL (read var9 var7))) (and (and (= var4 (write var9 var7 (O_TSLL (TSLL (next (getTSLL (read var9 var7))) 2)))) (= var3 var8)) (= var1 var7))))) (inv_main50 var5 var0 var0 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main35 var9 var8 var7) (and (and (and (= var6 nullAddr) (and (and (and (= var5 var4) (= var6 var3)) (= var2 var1)) (= var0 nullAddr))) (and (is-O_TSLL (read var9 var7)) (is-O_TSLL (read var9 (next (getTSLL (read var9 var7))))))) (and (and (= var4 (write var9 (next (getTSLL (read var9 var7))) (O_TSLL (TSLL (next (getTSLL (read var9 (next (getTSLL (read var9 var7)))))) 2)))) (= var3 var8)) (= var1 var7))))) (inv_main50 var5 var0 var0 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main11 var3 var2 var1 var0) (is-O_TSLL (read var3 var1)))) (inv_main10 (write var3 var1 (O_TSLL (TSLL var0 (data (getTSLL (read var3 var1)))))) var2 var1))))
(assert (forall ((var0 TSLL) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main32 var7 var6 var5) (and (and (= var4 nullAddr) (is-O_TSLL (read var7 var5))) (and (and (and (= var3 var7) (= var2 var6)) (= var1 var5)) (= var4 (next (getTSLL (read var7 var5)))))))) (inv_main38 (newHeap (alloc var3 (O_TSLL var0))) var2 var1 (newAddr (alloc var3 (O_TSLL var0)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Int) (var6 Int) (var7 Int) (var8 Int) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Heap)) (or (not (and (inv_main56 var12 var11 var10 var9 var8 var7) (and (and (= var6 2) (not (= var5 1))) (and (and (is-O_TSLL (read var12 var10)) (is-O_TSLL (read var12 (next (getTSLL (read var12 var10)))))) (and (and (and (and (and (and (= var4 var12) (= var3 var11)) (= var2 var10)) (= var1 var9)) (= var6 var8)) (= var0 var7)) (= var5 (data (getTSLL (read var12 (next (getTSLL (read var12 var10)))))))))))) (inv_main61 var4 var3 var2 var1 var6 var5))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main52 var8 var7 var6 var5) (and (and (and (= var4 2) (not (= var4 2))) (is-O_TSLL (read var8 var6))) (and (and (and (and (= var3 var8) (= var2 var7)) (= var1 var6)) (= var0 var5)) (= var4 (data (getTSLL (read var8 var6)))))))) (inv_main61 var3 var2 var1 var0 var4 0))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main3 var1 var0) (not (is-O_TSLL (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main4 var1 var0) (not (is-O_TSLL (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main11 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main10 var2 var1 var0) (not (is-O_TSLL (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main12 var2 var1 var0) (not (is-O_TSLL (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main14 var2 var1 var0) (not (is-O_TSLL (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main15 var2 var1 var0) (not (is-O_TSLL (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (inv_main23 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main21 var2 var1 var0) (not (is-O_TSLL (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (inv_main29 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main27 var2 var1 var0) (not (is-O_TSLL (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main32 var2 var1 var0) (not (is-O_TSLL (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main38 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main37 var2 var1 var0) (not (is-O_TSLL (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main39 var2 var1 var0) (not (is-O_TSLL (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main41 var2 var1 var0) (not (is-O_TSLL (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main35 var2 var1 var0) (not (is-O_TSLL (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main35 var2 var1 var0) (and (is-O_TSLL (read var2 var0)) (not (is-O_TSLL (read var2 (next (getTSLL (read var2 var0)))))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main45 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main46 var4 var3 var2 var1 var0) (not (is-O_TSLL (read var4 var2)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main52 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var1)))))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (not (and (inv_main56 var5 var4 var3 var2 var1 var0) (not (is-O_TSLL (read var5 var3)))))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (not (and (inv_main56 var5 var4 var3 var2 var1 var0) (and (is-O_TSLL (read var5 var3)) (not (is-O_TSLL (read var5 (next (getTSLL (read var5 var3)))))))))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (not (inv_main61 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (not (and (inv_main59 var5 var4 var3 var2 var1 var0) (not (is-O_TSLL (read var5 var3)))))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (not (and (inv_main65 var5 var4 var3 var2 var1 var0) (not (is-O_TSLL (read var5 var3)))))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (not (and (inv_main64 var5 var4 var3 var2 var1 var0) (not (is-O_TSLL (read var5 var3)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main73 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var1)))))))
(check-sat)
