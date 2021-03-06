(set-logic HORN)
(set-info :source |
    Benchmark: C_VC
    Output by Princess (http://www.philipp.ruemmer.org/princess.shtml)
|)
(set-info :status unsat)
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
   (TSLL (next Addr) (prev Addr) (colour Int))
  )
))
(declare-fun inv_main0 (Heap Int) Bool)
(declare-fun inv_main101 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main11 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main15 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main16 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main17 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main18 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main2 (Heap) Bool)
(declare-fun inv_main21 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main22 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main23 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main27 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main28 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main29 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main3 (Heap Addr) Bool)
(declare-fun inv_main30 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main32 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main34 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main37 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main4 (Heap Addr) Bool)
(declare-fun inv_main44 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main5 (Heap Addr) Bool)
(declare-fun inv_main51 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main57 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main60 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main67 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main7 (Heap Addr Addr) Bool)
(declare-fun inv_main71 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main72 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main73 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main74 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main78 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main8 (Heap Addr Addr) Bool)
(declare-fun inv_main81 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main88 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main9 (Heap Addr Addr) Bool)
(declare-fun inv_main95 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main97 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main98 (Heap Addr Addr Addr) Bool)
(assert (inv_main2 emptyHeap))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main18 var8 var7 var6 var5) (and (not (= var4 0)) (and (is-O_TSLL (read var8 var5)) (and (and (and (= var3 (write var8 var5 (O_TSLL (TSLL var7 (prev (getTSLL (read var8 var5))) (colour (getTSLL (read var8 var5))))))) (= var2 var7)) (= var1 var6)) (= var0 var5)))))) (inv_main22 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main73 var8 var7 var6 var5) (and (= var4 var3) (and (is-O_TSLL (read var8 var5)) (and (and (and (and (= var2 var8) (= var4 var7)) (= var1 var6)) (= var0 var5)) (= var3 (next (getTSLL (read var8 var5))))))))) (inv_main71 var2 var4 var1 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main57 var3 var2 var1 var0) (and (= var2 var0) (and (is-O_TSLL (read var3 var0)) (= 1 (colour (getTSLL (read var3 var0)))))))) (inv_main71 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Heap)) (or (not (and (inv_main101 var12 var11 var10 var9) (and (and (is-O_TSLL (read var12 var9)) (and (and (and (and (= var8 var12) (= var7 var11)) (= var6 var10)) (= var5 var9)) (= var4 (next (getTSLL (read var12 var9)))))) (and (and (and (= var3 (write var8 var5 defObj)) (= var2 var7)) (= var1 var4)) (= var0 var5))))) (inv_main71 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Heap)) (or (not (and (inv_main98 var12 var11 var10 var9) (and (and (is-O_TSLL (read var12 var10)) (and (and (and (and (= var8 var12) (= var7 var11)) (= var6 var10)) (= var5 var9)) (= var4 (next (getTSLL (read var12 var10)))))) (and (and (and (= var3 (write var8 var6 defObj)) (= var2 var7)) (= var1 var6)) (= var0 var4))))) (inv_main71 var3 var2 var0 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main71 var3 var2 var1 var0) (not (= var2 var1)))) (inv_main95 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main57 var3 var2 var1 var0) (and (is-O_TSLL (read var3 var0)) (not (= 1 (colour (getTSLL (read var3 var0)))))))) (inv_main67 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main95 var3 var2 var1 var0) (and (is-O_TSLL (read var3 var1)) (not (= 0 (colour (getTSLL (read var3 var1)))))))) (inv_main98 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main72 var3 var2 var1 var0) (and (is-O_TSLL (read var3 var0)) (= 0 (colour (getTSLL (read var3 var0))))))) (inv_main74 var3 var2 var1 var0))))
(assert (forall ((var0 TSLL) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main23 var8 var7 var6 var5) (and (is-O_TSLL (read var8 var5)) (and (and (and (= var4 (write var8 var5 (O_TSLL (TSLL (next (getTSLL (read var8 var5))) (prev (getTSLL (read var8 var5))) 0)))) (= var3 var7)) (= var2 var6)) (= var1 var5))))) (inv_main28 (newHeap (alloc var4 (O_TSLL var0))) var3 var2 var1 (newAddr (alloc var4 (O_TSLL var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main28 var4 var3 var2 var1 var0) (is-O_TSLL (read var4 var1)))) (inv_main27 (write var4 var1 (O_TSLL (TSLL var0 (prev (getTSLL (read var4 var1))) (colour (getTSLL (read var4 var1)))))) var3 var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main15 var3 var2 var1 var0) (and (is-O_TSLL (read var3 var0)) (is-O_TSLL (read var3 (next (getTSLL (read var3 var0)))))))) (inv_main17 (write var3 (next (getTSLL (read var3 var0))) (O_TSLL (TSLL (next (getTSLL (read var3 (next (getTSLL (read var3 var0)))))) var0 (colour (getTSLL (read var3 (next (getTSLL (read var3 var0))))))))) var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main21 var3 var2 var1 var0) (and (is-O_TSLL (read var3 var0)) (= 1 (colour (getTSLL (read var3 var0))))))) (inv_main34 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main73 var8 var7 var6 var5) (and (not (= var4 var3)) (and (is-O_TSLL (read var8 var5)) (and (and (and (and (= var2 var8) (= var4 var7)) (= var1 var6)) (= var0 var5)) (= var3 (next (getTSLL (read var8 var5))))))))) (inv_main72 var2 var4 var1 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main57 var3 var2 var1 var0) (and (not (= var2 var0)) (and (is-O_TSLL (read var3 var0)) (= 1 (colour (getTSLL (read var3 var0)))))))) (inv_main72 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main18 var8 var7 var6 var5) (and (= var4 0) (and (is-O_TSLL (read var8 var5)) (and (and (and (= var3 (write var8 var5 (O_TSLL (TSLL var7 (prev (getTSLL (read var8 var5))) (colour (getTSLL (read var8 var5))))))) (= var2 var7)) (= var1 var6)) (= var0 var5)))))) (inv_main23 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main30 var3 var2 var1 var0) (is-O_TSLL (read var3 var0)))) (inv_main32 (write var3 var0 (O_TSLL (TSLL var2 (prev (getTSLL (read var3 var0))) (colour (getTSLL (read var3 var0)))))) var2 var1 var0))))
(assert (forall ((var0 TSLL) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main11 var5 var4 var3 var2) (not (= var1 0)))) (inv_main16 (newHeap (alloc var5 (O_TSLL var0))) var4 var3 var2 (newAddr (alloc var5 (O_TSLL var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main29 var8 var7 var6 var5) (and (is-O_TSLL (read var8 var5)) (and (and (and (and (= var4 var8) (= var3 var7)) (= var2 var6)) (= var1 var5)) (= var0 (next (getTSLL (read var8 var5)))))))) (inv_main30 var4 var3 var2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main22 var7 var6 var5 var4) (and (is-O_TSLL (read var7 var4)) (and (and (and (= var3 (write var7 var4 (O_TSLL (TSLL (next (getTSLL (read var7 var4))) (prev (getTSLL (read var7 var4))) 1)))) (= var2 var6)) (= var1 var5)) (= var0 var4))))) (inv_main21 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main32 var7 var6 var5 var4) (and (is-O_TSLL (read var7 var4)) (and (and (and (= var3 (write var7 var4 (O_TSLL (TSLL (next (getTSLL (read var7 var4))) (prev (getTSLL (read var7 var4))) 1)))) (= var2 var6)) (= var1 var5)) (= var0 var4))))) (inv_main21 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Heap)) (or (not (and (inv_main3 var1 var0) (is-O_TSLL (read var1 var0)))) (inv_main4 (write var1 var0 (O_TSLL (TSLL nullAddr (prev (getTSLL (read var1 var0))) (colour (getTSLL (read var1 var0)))))) var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main71 var3 var2 var1 var0) (= var2 var1))) (inv_main0 var3 0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main34 var3 var2 var1 var0) (and (is-O_TSLL (read var3 var0)) (not (= var2 (next (getTSLL (read var3 var0)))))))) (inv_main44 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main74 var8 var7 var6 var5) (and (= var4 var3) (and (is-O_TSLL (read var8 var5)) (and (and (and (and (= var2 var8) (= var4 var7)) (= var1 var6)) (= var0 var5)) (= var3 (next (getTSLL (read var8 var5))))))))) (inv_main81 var2 var4 var1 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main74 var8 var7 var6 var5) (and (not (= var4 var3)) (and (is-O_TSLL (read var8 var5)) (and (and (and (and (= var2 var8) (= var4 var7)) (= var1 var6)) (= var0 var5)) (= var3 (next (getTSLL (read var8 var5))))))))) (inv_main78 var2 var4 var1 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main17 var8 var7 var6 var5) (and (is-O_TSLL (read var8 var5)) (and (and (and (and (= var4 var8) (= var3 var7)) (= var2 var6)) (= var1 var5)) (= var0 (next (getTSLL (read var8 var5)))))))) (inv_main18 var4 var3 var2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main34 var3 var2 var1 var0) (and (not (= var2 var0)) (and (is-O_TSLL (read var3 var0)) (= var2 (next (getTSLL (read var3 var0)))))))) (inv_main11 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main9 var5 var4 var3) (and (is-O_TSLL (read var5 var3)) (and (and (= var2 (write var5 var3 (O_TSLL (TSLL (next (getTSLL (read var5 var3))) (prev (getTSLL (read var5 var3))) 1)))) (= var1 var4)) (= var0 var3))))) (inv_main11 var2 var1 var0 var0))))
(assert (forall ((var0 Addr) (var1 Heap)) (or (not (and (inv_main4 var1 var0) (is-O_TSLL (read var1 var0)))) (inv_main5 (write var1 var0 (O_TSLL (TSLL (next (getTSLL (read var1 var0))) nullAddr (colour (getTSLL (read var1 var0)))))) var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main72 var3 var2 var1 var0) (and (is-O_TSLL (read var3 var0)) (not (= 0 (colour (getTSLL (read var3 var0)))))))) (inv_main73 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main78 var3 var2 var1 var0) (and (is-O_TSLL (read var3 var0)) (not (= 1 (colour (getTSLL (read var3 var0)))))))) (inv_main73 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (and (inv_main8 var2 var1 var0) (is-O_TSLL (read var2 var0)))) (inv_main9 (write var2 var0 (O_TSLL (TSLL (next (getTSLL (read var2 var0))) var1 (colour (getTSLL (read var2 var0)))))) var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main97 var8 var7 var6 var5) (and (is-O_TSLL (read var8 var6)) (and (and (and (and (= var4 var8) (= var3 var7)) (= var2 var6)) (= var1 var5)) (= var0 (next (getTSLL (read var8 var6)))))))) (inv_main101 (write var4 var2 defObj) var3 var2 var0))))
(assert (forall ((var0 TSLL) (var1 Heap)) (or (not (inv_main2 var1)) (inv_main3 (newHeap (alloc var1 (O_TSLL var0))) (newAddr (alloc var1 (O_TSLL var0)))))))
(assert (forall ((var0 TSLL) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Heap)) (or (not (and (inv_main5 var4 var3) (and (is-O_TSLL (read var4 var3)) (and (= var2 (write var4 var3 (O_TSLL (TSLL (next (getTSLL (read var4 var3))) (prev (getTSLL (read var4 var3))) 1)))) (= var1 var3))))) (inv_main7 (newHeap (alloc var2 (O_TSLL var0))) var1 (newAddr (alloc var2 (O_TSLL var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (and (inv_main7 var2 var1 var0) (is-O_TSLL (read var2 var0)))) (inv_main8 (write var2 var0 (O_TSLL (TSLL var1 (prev (getTSLL (read var2 var0))) (colour (getTSLL (read var2 var0)))))) var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main78 var3 var2 var1 var0) (and (is-O_TSLL (read var3 var0)) (= 1 (colour (getTSLL (read var3 var0))))))) (inv_main88 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main34 var3 var2 var1 var0) (and (= var2 var0) (and (is-O_TSLL (read var3 var0)) (= var2 (next (getTSLL (read var3 var0)))))))) (inv_main51 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main95 var3 var2 var1 var0) (and (is-O_TSLL (read var3 var1)) (= 0 (colour (getTSLL (read var3 var1))))))) (inv_main97 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main11 var4 var3 var2 var1) (and (not (= var3 var2)) (= var0 0)))) (inv_main57 var4 var3 var2 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main27 var3 var2 var1 var0) (and (is-O_TSLL (read var3 var0)) (is-O_TSLL (read var3 (next (getTSLL (read var3 var0)))))))) (inv_main29 (write var3 (next (getTSLL (read var3 var0))) (O_TSLL (TSLL (next (getTSLL (read var3 (next (getTSLL (read var3 var0)))))) var0 (colour (getTSLL (read var3 (next (getTSLL (read var3 var0))))))))) var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main21 var3 var2 var1 var0) (and (is-O_TSLL (read var3 var0)) (not (= 1 (colour (getTSLL (read var3 var0)))))))) (inv_main37 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main16 var4 var3 var2 var1 var0) (is-O_TSLL (read var4 var1)))) (inv_main15 (write var4 var1 (O_TSLL (TSLL var0 (prev (getTSLL (read var4 var1))) (colour (getTSLL (read var4 var1)))))) var3 var2 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main11 var4 var3 var2 var1) (and (= var3 var2) (= var0 0)))) (inv_main60 var4 var3 var2 var2))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main3 var1 var0) (not (is-O_TSLL (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main4 var1 var0) (not (is-O_TSLL (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main5 var1 var0) (not (is-O_TSLL (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main7 var2 var1 var0) (not (is-O_TSLL (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main8 var2 var1 var0) (not (is-O_TSLL (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main9 var2 var1 var0) (not (is-O_TSLL (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main16 var4 var3 var2 var1 var0) (not (is-O_TSLL (read var4 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main15 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main15 var3 var2 var1 var0) (and (is-O_TSLL (read var3 var0)) (not (is-O_TSLL (read var3 (next (getTSLL (read var3 var0)))))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main17 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main18 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main22 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main23 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main28 var4 var3 var2 var1 var0) (not (is-O_TSLL (read var4 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main27 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main27 var3 var2 var1 var0) (and (is-O_TSLL (read var3 var0)) (not (is-O_TSLL (read var3 (next (getTSLL (read var3 var0)))))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main29 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main30 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main32 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main21 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (inv_main37 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main34 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (inv_main44 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (inv_main51 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (inv_main60 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main57 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (inv_main67 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main72 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main74 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (inv_main81 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main78 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (inv_main88 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main73 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main95 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main97 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main101 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main98 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var1)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Heap)) (not (and (inv_main0 var2 var1) (not (= (read var2 var0) defObj))))))
(check-sat)
