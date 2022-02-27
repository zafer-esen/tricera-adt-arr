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
   (O_Addr (getAddr Addr))
   (O_TSLL (getTSLL TSLL))
   (defObj)
  )
  (
   (TSLL (next Addr) (prev Addr) (colour Int))
  )
))
(declare-fun inv_main0 (Heap Int) Bool)
(declare-fun inv_main11 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main15 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main16 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main17 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main18 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main2 (Heap) Bool)
(declare-fun inv_main21 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main22 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main23 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main26 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main27 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main28 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main29 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main3 (Heap Addr) Bool)
(declare-fun inv_main31 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main32 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main34 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main39 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main4 (Heap Addr) Bool)
(declare-fun inv_main43 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main48 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main5 (Heap Addr) Bool)
(declare-fun inv_main50 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main55 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main58 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main59 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main60 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main61 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main65 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main67 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main7 (Heap Addr Addr) Bool)
(declare-fun inv_main71 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main76 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main77 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main78 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main8 (Heap Addr Addr) Bool)
(declare-fun inv_main81 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main9 (Heap Addr Addr) Bool)
(assert (inv_main2 emptyHeap))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr)) (or (not (and (inv_main21 var2 var3 var0 var1) (not (= 1 (colour (getTSLL (read var2 var1))))))) (inv_main34 var2 var3 var0 var1))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 TSLL) (var3 Heap) (var4 Addr)) (or (not (and (inv_main5 var3 var4) (and (= var1 (write var3 var4 (O_TSLL (TSLL (next (getTSLL (read var3 var4))) (prev (getTSLL (read var3 var4))) 1)))) (= var0 var4)))) (inv_main7 (newHeap (alloc var1 (O_TSLL var2))) var0 (newAddr (alloc var1 (O_TSLL var2)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr)) (or (not (and (inv_main81 var4 var6 var1 var2) (and (and (and (and (= var0 var4) (= var7 var6)) (= var5 var1)) (= var8 var2)) (= var3 (next (getTSLL (read var4 var2))))))) (inv_main58 (write var0 var8 defObj) var7 var3 var8))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Heap)) (or (not (and (inv_main78 var9 var10 var3 var5) (and (and (and (and (and (= var8 var9) (= var4 var10)) (= var7 var3)) (= var6 var5)) (= var2 (next (getTSLL (read var9 var3))))) (and (and (and (= var12 (write var8 var7 defObj)) (= var11 var4)) (= var1 var7)) (= var0 var2))))) (inv_main58 var12 var11 var0 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr)) (or (not (and (inv_main60 var4 var7 var1 var2) (and (= var3 var0) (and (and (and (and (= var5 var4) (= var3 var7)) (= var8 var1)) (= var6 var2)) (= var0 (next (getTSLL (read var4 var2)))))))) (inv_main58 var5 var3 var8 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr)) (or (not (and (inv_main48 var2 var3 var0 var1) (and (= var3 var1) (= 1 (colour (getTSLL (read var2 var1))))))) (inv_main58 var2 var3 var0 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr)) (or (not (and (inv_main58 var2 var3 var0 var1) (not (= var3 var0)))) (inv_main76 var2 var3 var0 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr)) (or (not (inv_main26 var2 var3 var0 var1)) (inv_main28 (write var2 (next (getTSLL (read var2 var1))) (O_TSLL (TSLL (next (getTSLL (read var2 (next (getTSLL (read var2 var1)))))) var1 (colour (getTSLL (read var2 (next (getTSLL (read var2 var1))))))))) var3 var0 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr)) (or (not (and (inv_main58 var2 var3 var0 var1) (= var3 var0))) (inv_main0 var2 0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Heap) (var4 Addr)) (or (not (and (inv_main11 var3 var4 var0 var2) (and (= var4 var0) (= var1 0)))) (inv_main50 var3 var4 var0 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr)) (or (not (and (inv_main48 var2 var3 var0 var1) (not (= 1 (colour (getTSLL (read var2 var1))))))) (inv_main55 var2 var3 var0 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Heap) (var7 Addr) (var8 Addr)) (or (not (and (inv_main61 var5 var7 var0 var4) (and (not (= var8 var2)) (and (and (and (and (= var6 var5) (= var8 var7)) (= var1 var0)) (= var3 var4)) (= var2 (next (getTSLL (read var5 var4)))))))) (inv_main65 var6 var8 var1 var2))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr)) (or (not (inv_main7 var1 var2 var0)) (inv_main8 (write var1 var0 (O_TSLL (TSLL var2 (prev (getTSLL (read var1 var0))) (colour (getTSLL (read var1 var0)))))) var2 var0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Int) (var7 Addr) (var8 Addr)) (or (not (and (inv_main18 var5 var7 var0 var3) (and (not (= var6 0)) (and (and (and (= var1 (write var5 var3 (O_TSLL (TSLL var7 (prev (getTSLL (read var5 var3))) (colour (getTSLL (read var5 var3))))))) (= var2 var7)) (= var8 var0)) (= var4 var3))))) (inv_main22 var1 var2 var8 var4))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr)) (or (not (and (inv_main28 var4 var6 var1 var2) (and (and (and (and (= var3 var4) (= var8 var6)) (= var7 var1)) (= var0 var2)) (= var5 (next (getTSLL (read var4 var2))))))) (inv_main29 var3 var8 var7 var5))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr)) (or (not (and (inv_main59 var2 var3 var0 var1) (not (= 0 (colour (getTSLL (read var2 var1))))))) (inv_main60 var2 var3 var0 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr)) (or (not (and (inv_main65 var2 var3 var0 var1) (not (= 1 (colour (getTSLL (read var2 var1))))))) (inv_main60 var2 var3 var0 var1))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Heap) (var4 Addr)) (or (not (and (inv_main11 var3 var4 var0 var2) (and (not (= var4 var0)) (= var1 0)))) (inv_main48 var3 var4 var0 var0))))
(assert (forall ((var0 Addr) (var1 TSLL) (var2 Int) (var3 Addr) (var4 Heap) (var5 Addr)) (or (not (and (inv_main11 var4 var5 var0 var3) (not (= var2 0)))) (inv_main16 (newHeap (alloc var4 (O_TSLL var1))) var5 var0 var3 (newAddr (alloc var4 (O_TSLL var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr)) (or (not (and (inv_main76 var2 var3 var0 var1) (not (= 0 (colour (getTSLL (read var2 var0))))))) (inv_main78 var2 var3 var0 var1))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Addr)) (or (not (and (inv_main77 var6 var8 var1 var2) (and (and (and (and (= var0 var6) (= var3 var8)) (= var7 var1)) (= var4 var2)) (= var5 (next (getTSLL (read var6 var1))))))) (inv_main81 (write var0 var7 defObj) var3 var7 var5))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr)) (or (not (inv_main22 var2 var3 var0 var1)) (inv_main21 (write var2 var1 (O_TSLL (TSLL (next (getTSLL (read var2 var1))) (prev (getTSLL (read var2 var1))) 1))) var3 var0 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr)) (or (not (inv_main31 var2 var3 var0 var1)) (inv_main21 (write var2 var1 (O_TSLL (TSLL (next (getTSLL (read var2 var1))) (prev (getTSLL (read var2 var1))) 1))) var3 var0 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr)) (or (not (inv_main27 var2 var3 var0 var1 var4)) (inv_main26 (write var2 var1 (O_TSLL (TSLL var4 (prev (getTSLL (read var2 var1))) (colour (getTSLL (read var2 var1)))))) var3 var0 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr)) (or (not (and (inv_main32 var2 var3 var0 var1) (and (not (= var3 var1)) (= var3 (next (getTSLL (read var2 var1))))))) (inv_main11 var2 var3 var0 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Heap) (var4 Addr) (var5 Addr)) (or (not (and (inv_main9 var3 var5 var1) (and (and (= var2 (write var3 var1 (O_TSLL (TSLL (next (getTSLL (read var3 var1))) (prev (getTSLL (read var3 var1))) 1)))) (= var4 var5)) (= var0 var1)))) (inv_main11 var2 var4 var0 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Heap) (var7 Addr) (var8 Addr)) (or (not (and (inv_main61 var5 var7 var0 var4) (and (= var8 var2) (and (and (and (and (= var6 var5) (= var8 var7)) (= var1 var0)) (= var3 var4)) (= var2 (next (getTSLL (read var5 var4)))))))) (inv_main67 var6 var8 var1 var2))))
(assert (forall ((var0 Heap) (var1 Addr)) (or (not (inv_main3 var0 var1)) (inv_main4 (write var0 var1 (O_TSLL (TSLL nullAddr (prev (getTSLL (read var0 var1))) (colour (getTSLL (read var0 var1)))))) var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Heap)) (or (not (and (inv_main17 var6 var7 var1 var3) (and (and (and (and (= var8 var6) (= var0 var7)) (= var5 var1)) (= var2 var3)) (= var4 (next (getTSLL (read var6 var3))))))) (inv_main18 var8 var0 var5 var4))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr)) (or (not (and (inv_main32 var2 var3 var0 var1) (and (= var3 var1) (= var3 (next (getTSLL (read var2 var1))))))) (inv_main43 var2 var3 var0 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr)) (or (not (and (inv_main76 var2 var3 var0 var1) (= 0 (colour (getTSLL (read var2 var0)))))) (inv_main77 var2 var3 var0 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr)) (or (not (and (inv_main21 var2 var3 var0 var1) (= 1 (colour (getTSLL (read var2 var1)))))) (inv_main32 var2 var3 var0 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr)) (or (not (inv_main15 var2 var3 var0 var1)) (inv_main17 (write var2 (next (getTSLL (read var2 var1))) (O_TSLL (TSLL (next (getTSLL (read var2 (next (getTSLL (read var2 var1)))))) var1 (colour (getTSLL (read var2 (next (getTSLL (read var2 var1))))))))) var3 var0 var1))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr)) (or (not (inv_main8 var1 var2 var0)) (inv_main9 (write var1 var0 (O_TSLL (TSLL (next (getTSLL (read var1 var0))) var2 (colour (getTSLL (read var1 var0)))))) var2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr)) (or (not (and (inv_main32 var2 var3 var0 var1) (not (= var3 (next (getTSLL (read var2 var1))))))) (inv_main39 var2 var3 var0 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr)) (or (not (and (inv_main65 var2 var3 var0 var1) (= 1 (colour (getTSLL (read var2 var1)))))) (inv_main71 var2 var3 var0 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 TSLL) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Addr)) (or (not (and (inv_main23 var6 var7 var0 var3) (and (and (and (= var4 (write var6 var3 (O_TSLL (TSLL (next (getTSLL (read var6 var3))) (prev (getTSLL (read var6 var3))) 0)))) (= var8 var7)) (= var1 var0)) (= var5 var3)))) (inv_main27 (newHeap (alloc var4 (O_TSLL var2))) var8 var1 var5 (newAddr (alloc var4 (O_TSLL var2)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Int)) (or (not (and (inv_main18 var5 var6 var0 var3) (and (= var8 0) (and (and (and (= var1 (write var5 var3 (O_TSLL (TSLL var6 (prev (getTSLL (read var5 var3))) (colour (getTSLL (read var5 var3))))))) (= var2 var6)) (= var7 var0)) (= var4 var3))))) (inv_main23 var1 var2 var7 var4))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr)) (or (not (inv_main29 var2 var3 var0 var1)) (inv_main31 (write var2 var1 (O_TSLL (TSLL var3 (prev (getTSLL (read var2 var1))) (colour (getTSLL (read var2 var1)))))) var3 var0 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr)) (or (not (inv_main16 var2 var4 var0 var1 var3)) (inv_main15 (write var2 var1 (O_TSLL (TSLL var3 (prev (getTSLL (read var2 var1))) (colour (getTSLL (read var2 var1)))))) var4 var0 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr)) (or (not (and (inv_main60 var4 var7 var1 var2) (and (not (= var3 var0)) (and (and (and (and (= var5 var4) (= var3 var7)) (= var8 var1)) (= var6 var2)) (= var0 (next (getTSLL (read var4 var2)))))))) (inv_main59 var5 var3 var8 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr)) (or (not (and (inv_main48 var2 var3 var0 var1) (and (not (= var3 var1)) (= 1 (colour (getTSLL (read var2 var1))))))) (inv_main59 var2 var3 var0 var1))))
(assert (forall ((var0 TSLL) (var1 Heap)) (or (not (inv_main2 var1)) (inv_main3 (newHeap (alloc var1 (O_TSLL var0))) (newAddr (alloc var1 (O_TSLL var0)))))))
(assert (forall ((var0 Heap) (var1 Addr)) (or (not (inv_main4 var0 var1)) (inv_main5 (write var0 var1 (O_TSLL (TSLL (next (getTSLL (read var0 var1))) nullAddr (colour (getTSLL (read var0 var1)))))) var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr)) (or (not (and (inv_main59 var2 var3 var0 var1) (= 0 (colour (getTSLL (read var2 var1)))))) (inv_main61 var2 var3 var0 var1))))
(assert (forall ((var0 Heap) (var1 Addr)) (not (and (inv_main3 var0 var1) (not (is-O_TSLL (read var0 var1)))))))
(assert (forall ((var0 Heap) (var1 Addr)) (not (and (inv_main4 var0 var1) (not (is-O_TSLL (read var0 var1)))))))
(assert (forall ((var0 Heap) (var1 Addr)) (not (and (inv_main5 var0 var1) (not (is-O_TSLL (read var0 var1)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr)) (not (and (inv_main7 var1 var2 var0) (not (is-O_TSLL (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr)) (not (and (inv_main8 var1 var2 var0) (not (is-O_TSLL (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr)) (not (and (inv_main9 var1 var2 var0) (not (is-O_TSLL (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr)) (not (and (inv_main16 var2 var4 var0 var1 var3) (not (is-O_TSLL (read var2 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr)) (not (and (inv_main15 var2 var3 var0 var1) (not (is-O_TSLL (read var2 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr)) (not (and (inv_main15 var2 var3 var0 var1) (not (is-O_TSLL (read var2 (next (getTSLL (read var2 var1))))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr)) (not (and (inv_main17 var2 var3 var0 var1) (not (is-O_TSLL (read var2 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr)) (not (and (inv_main18 var2 var3 var0 var1) (not (is-O_TSLL (read var2 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr)) (not (and (inv_main22 var2 var3 var0 var1) (not (is-O_TSLL (read var2 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr)) (not (and (inv_main23 var2 var3 var0 var1) (not (is-O_TSLL (read var2 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr)) (not (and (inv_main27 var2 var3 var0 var1 var4) (not (is-O_TSLL (read var2 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr)) (not (and (inv_main26 var2 var3 var0 var1) (not (is-O_TSLL (read var2 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr)) (not (and (inv_main26 var2 var3 var0 var1) (not (is-O_TSLL (read var2 (next (getTSLL (read var2 var1))))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr)) (not (and (inv_main28 var2 var3 var0 var1) (not (is-O_TSLL (read var2 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr)) (not (and (inv_main29 var2 var3 var0 var1) (not (is-O_TSLL (read var2 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr)) (not (and (inv_main31 var2 var3 var0 var1) (not (is-O_TSLL (read var2 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr)) (not (and (inv_main21 var2 var3 var0 var1) (not (is-O_TSLL (read var2 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr)) (not (inv_main34 var2 var3 var0 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr)) (not (and (inv_main32 var2 var3 var0 var1) (not (is-O_TSLL (read var2 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr)) (not (inv_main39 var2 var3 var0 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr)) (not (inv_main43 var2 var3 var0 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr)) (not (inv_main50 var2 var3 var0 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr)) (not (and (inv_main48 var2 var3 var0 var1) (not (is-O_TSLL (read var2 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr)) (not (inv_main55 var2 var3 var0 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr)) (not (and (inv_main59 var2 var3 var0 var1) (not (is-O_TSLL (read var2 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr)) (not (and (inv_main61 var2 var3 var0 var1) (not (is-O_TSLL (read var2 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr)) (not (inv_main67 var2 var3 var0 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr)) (not (and (inv_main65 var2 var3 var0 var1) (not (is-O_TSLL (read var2 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr)) (not (inv_main71 var2 var3 var0 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr)) (not (and (inv_main60 var2 var3 var0 var1) (not (is-O_TSLL (read var2 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr)) (not (and (inv_main76 var2 var3 var0 var1) (not (is-O_TSLL (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr)) (not (and (inv_main77 var2 var3 var0 var1) (not (is-O_TSLL (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr)) (not (and (inv_main81 var2 var3 var0 var1) (not (is-O_TSLL (read var2 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr)) (not (and (inv_main78 var2 var3 var0 var1) (not (is-O_TSLL (read var2 var0)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Int)) (not (and (inv_main0 var0 var2) (not (= (read var0 var1) defObj))))))
(check-sat)
