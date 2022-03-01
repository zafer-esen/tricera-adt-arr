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
   (TSLL (next Addr) (colour Int))
  )
))
(declare-fun inv_main13 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main14 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main15 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main18 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main19 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main2 (Heap) Bool)
(declare-fun inv_main22 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main23 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main24 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main26 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main29 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main3 (Heap Addr) Bool)
(declare-fun inv_main31 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main36 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main4 (Heap Addr) Bool)
(declare-fun inv_main40 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main41 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main42 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main46 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main48 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main52 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main57 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main58 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main59 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main6 (Heap Addr Addr) Bool)
(declare-fun inv_main62 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main7 (Heap Addr Addr) Bool)
(declare-fun inv_main9 (Heap Addr Addr Addr) Bool)
(assert (inv_main2 emptyHeap))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main57 var3 var2 var1 var0) (and (is-O_TSLL (read var3 var1)) (= 0 (colour (getTSLL (read var3 var1))))))) (inv_main58 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main24 var3 var2 var1 var0) (is-O_TSLL (read var3 var0)))) (inv_main26 (write var3 var0 (O_TSLL (TSLL var2 (colour (getTSLL (read var3 var0)))))) var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main13 var8 var7 var6 var5) (and (is-O_TSLL (read var8 var5)) (and (and (and (and (= var4 var8) (= var3 var7)) (= var2 var6)) (= var1 var5)) (= var0 (next (getTSLL (read var8 var5)))))))) (inv_main15 var4 var3 var2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main42 var8 var7 var6 var5) (and (= var4 var3) (and (is-O_TSLL (read var8 var5)) (and (and (and (and (= var2 var8) (= var4 var7)) (= var1 var6)) (= var0 var5)) (= var3 (next (getTSLL (read var8 var5))))))))) (inv_main48 var2 var4 var1 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main15 var8 var7 var6 var5) (and (not (= var4 0)) (and (is-O_TSLL (read var8 var5)) (and (and (and (= var3 (write var8 var5 (O_TSLL (TSLL var7 (colour (getTSLL (read var8 var5))))))) (= var2 var7)) (= var1 var6)) (= var0 var5)))))) (inv_main18 var3 var2 var1 var0))))
(assert (forall ((var0 TSLL) (var1 Heap)) (or (not (inv_main2 var1)) (inv_main3 (newHeap (alloc var1 (O_TSLL var0))) (newAddr (alloc var1 (O_TSLL var0)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main9 var4 var3 var2 var1) (and (= var3 var2) (= var0 0)))) (inv_main31 var4 var3 var2 var2))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main9 var4 var3 var2 var1) (and (not (= var3 var2)) (= var0 0)))) (inv_main29 var4 var3 var2 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main42 var8 var7 var6 var5) (and (not (= var4 var3)) (and (is-O_TSLL (read var8 var5)) (and (and (and (and (= var2 var8) (= var4 var7)) (= var1 var6)) (= var0 var5)) (= var3 (next (getTSLL (read var8 var5))))))))) (inv_main46 var2 var4 var1 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main58 var8 var7 var6 var5) (and (is-O_TSLL (read var8 var6)) (and (and (and (and (= var4 var8) (= var3 var7)) (= var2 var6)) (= var1 var5)) (= var0 (next (getTSLL (read var8 var6)))))))) (inv_main62 (write var4 var2 defObj) var3 var2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main41 var8 var7 var6 var5) (and (not (= var4 var3)) (and (is-O_TSLL (read var8 var5)) (and (and (and (and (= var2 var8) (= var4 var7)) (= var1 var6)) (= var0 var5)) (= var3 (next (getTSLL (read var8 var5))))))))) (inv_main40 var2 var4 var1 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main29 var3 var2 var1 var0) (and (not (= var2 var0)) (and (is-O_TSLL (read var3 var0)) (= 1 (colour (getTSLL (read var3 var0)))))))) (inv_main40 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main29 var3 var2 var1 var0) (and (is-O_TSLL (read var3 var0)) (not (= 1 (colour (getTSLL (read var3 var0)))))))) (inv_main36 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main40 var3 var2 var1 var0) (and (is-O_TSLL (read var3 var0)) (not (= 0 (colour (getTSLL (read var3 var0)))))))) (inv_main41 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main46 var3 var2 var1 var0) (and (is-O_TSLL (read var3 var0)) (not (= 1 (colour (getTSLL (read var3 var0)))))))) (inv_main41 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (and (inv_main6 var2 var1 var0) (is-O_TSLL (read var2 var0)))) (inv_main7 (write var2 var0 (O_TSLL (TSLL var1 (colour (getTSLL (read var2 var0)))))) var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main23 var4 var3 var2 var1 var0) (is-O_TSLL (read var4 var1)))) (inv_main22 (write var4 var1 (O_TSLL (TSLL var0 (colour (getTSLL (read var4 var1)))))) var3 var2 var1))))
(assert (forall ((var0 TSLL) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main9 var5 var4 var3 var2) (not (= var1 0)))) (inv_main14 (newHeap (alloc var5 (O_TSLL var0))) var4 var3 var2 (newAddr (alloc var5 (O_TSLL var0)))))))
(assert (forall ((var0 TSLL) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Heap)) (or (not (and (inv_main4 var4 var3) (and (is-O_TSLL (read var4 var3)) (and (= var2 (write var4 var3 (O_TSLL (TSLL nullAddr (colour (getTSLL (read var4 var3))))))) (= var1 var3))))) (inv_main6 (newHeap (alloc var2 (O_TSLL var0))) var1 (newAddr (alloc var2 (O_TSLL var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main18 var3 var2 var1 var0) (is-O_TSLL (read var3 var0)))) (inv_main9 (write var3 var0 (O_TSLL (TSLL (next (getTSLL (read var3 var0))) 1))) var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main26 var3 var2 var1 var0) (is-O_TSLL (read var3 var0)))) (inv_main9 (write var3 var0 (O_TSLL (TSLL (next (getTSLL (read var3 var0))) 1))) var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main7 var5 var4 var3) (and (is-O_TSLL (read var5 var3)) (and (and (= var2 (write var5 var3 (O_TSLL (TSLL (next (getTSLL (read var5 var3))) 1)))) (= var1 var4)) (= var0 var3))))) (inv_main9 var2 var1 var0 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main22 var8 var7 var6 var5) (and (is-O_TSLL (read var8 var5)) (and (and (and (and (= var4 var8) (= var3 var7)) (= var2 var6)) (= var1 var5)) (= var0 (next (getTSLL (read var8 var5)))))))) (inv_main24 var4 var3 var2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main15 var8 var7 var6 var5) (and (= var4 0) (and (is-O_TSLL (read var8 var5)) (and (and (and (= var3 (write var8 var5 (O_TSLL (TSLL var7 (colour (getTSLL (read var8 var5))))))) (= var2 var7)) (= var1 var6)) (= var0 var5)))))) (inv_main19 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Heap)) (or (not (and (inv_main3 var1 var0) (is-O_TSLL (read var1 var0)))) (inv_main4 (write var1 var0 (O_TSLL (TSLL (next (getTSLL (read var1 var0))) 1))) var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main14 var4 var3 var2 var1 var0) (is-O_TSLL (read var4 var1)))) (inv_main13 (write var4 var1 (O_TSLL (TSLL var0 (colour (getTSLL (read var4 var1)))))) var3 var2 var1))))
(assert (forall ((var0 TSLL) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main19 var8 var7 var6 var5) (and (is-O_TSLL (read var8 var5)) (and (and (and (= var4 (write var8 var5 (O_TSLL (TSLL (next (getTSLL (read var8 var5))) 0)))) (= var3 var7)) (= var2 var6)) (= var1 var5))))) (inv_main23 (newHeap (alloc var4 (O_TSLL var0))) var3 var2 var1 (newAddr (alloc var4 (O_TSLL var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main46 var3 var2 var1 var0) (and (is-O_TSLL (read var3 var0)) (= 1 (colour (getTSLL (read var3 var0))))))) (inv_main52 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Heap)) (or (not (and (inv_main62 var12 var11 var10 var9) (and (and (not (= var8 var7)) (and (is-O_TSLL (read var12 var9)) (and (and (and (and (= var6 var12) (= var5 var11)) (= var4 var10)) (= var3 var9)) (= var2 (next (getTSLL (read var12 var9))))))) (and (and (and (= var1 (write var6 var3 defObj)) (= var8 var5)) (= var7 var2)) (= var0 var3))))) (inv_main57 var1 var8 var7 var0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Heap)) (or (not (and (inv_main59 var12 var11 var10 var9) (and (not (= var8 var7)) (and (and (is-O_TSLL (read var12 var10)) (and (and (and (and (= var6 var12) (= var5 var11)) (= var4 var10)) (= var3 var9)) (= var2 (next (getTSLL (read var12 var10)))))) (and (and (and (= var1 (write var6 var4 defObj)) (= var8 var5)) (= var0 var4)) (= var7 var2)))))) (inv_main57 var1 var8 var7 var7))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main41 var8 var7 var6 var5) (and (not (= var4 var3)) (and (= var4 var2) (and (is-O_TSLL (read var8 var5)) (and (and (and (and (= var1 var8) (= var4 var7)) (= var3 var6)) (= var0 var5)) (= var2 (next (getTSLL (read var8 var5)))))))))) (inv_main57 var1 var4 var3 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main29 var3 var2 var1 var0) (and (not (= var2 var1)) (and (= var2 var0) (and (is-O_TSLL (read var3 var0)) (= 1 (colour (getTSLL (read var3 var0))))))))) (inv_main57 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main57 var3 var2 var1 var0) (and (is-O_TSLL (read var3 var1)) (not (= 0 (colour (getTSLL (read var3 var1)))))))) (inv_main59 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main40 var3 var2 var1 var0) (and (is-O_TSLL (read var3 var0)) (= 0 (colour (getTSLL (read var3 var0))))))) (inv_main42 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main3 var1 var0) (not (is-O_TSLL (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main4 var1 var0) (not (is-O_TSLL (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main6 var2 var1 var0) (not (is-O_TSLL (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main7 var2 var1 var0) (not (is-O_TSLL (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main14 var4 var3 var2 var1 var0) (not (is-O_TSLL (read var4 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main13 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main15 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main18 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main19 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main23 var4 var3 var2 var1 var0) (not (is-O_TSLL (read var4 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main22 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main24 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main26 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (inv_main31 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main29 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (inv_main36 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main40 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main42 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (inv_main48 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main46 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (inv_main52 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main41 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main57 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main58 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main62 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main59 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var1)))))))
(check-sat)
