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
   (TSLL (next Addr) (opt Addr) (data Int))
  )
))
(declare-fun inv_main10 (Heap Addr) Bool)
(declare-fun inv_main11 (Heap Addr Addr) Bool)
(declare-fun inv_main12 (Heap Addr) Bool)
(declare-fun inv_main13 (Heap Addr) Bool)
(declare-fun inv_main15 (Heap Addr) Bool)
(declare-fun inv_main16 (Heap Addr) Bool)
(declare-fun inv_main17 (Heap Addr Addr) Bool)
(declare-fun inv_main2 (Heap) Bool)
(declare-fun inv_main21 (Heap Addr Addr) Bool)
(declare-fun inv_main22 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main23 (Heap Addr Addr) Bool)
(declare-fun inv_main26 (Heap Addr Addr) Bool)
(declare-fun inv_main3 (Heap Addr) Bool)
(declare-fun inv_main30 (Heap Addr Addr) Bool)
(declare-fun inv_main31 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main32 (Heap Addr Addr) Bool)
(declare-fun inv_main33 (Heap Addr Addr) Bool)
(declare-fun inv_main35 (Heap Addr Addr) Bool)
(declare-fun inv_main36 (Heap Addr Addr) Bool)
(declare-fun inv_main39 (Heap Addr Addr) Bool)
(declare-fun inv_main40 (Heap Addr Addr) Bool)
(declare-fun inv_main42 (Heap Addr Addr Int) Bool)
(declare-fun inv_main44 (Heap Addr Addr Int Addr Addr) Bool)
(declare-fun inv_main51 (Heap Addr Addr) Bool)
(declare-fun inv_main52 (Heap Addr Addr) Bool)
(declare-fun inv_main56 (Heap Addr Addr Int) Bool)
(declare-fun inv_main6 (Heap Addr) Bool)
(assert (inv_main2 emptyHeap))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Int) (var4 Addr) (var5 Heap)) (or (not (and (inv_main3 var5 var4) (and (= var3 0) (and (= var2 0) (and (and (is-O_TSLL (read var5 var4)) (is-O_TSLL (read var5 var4))) (and (= var1 (write var5 var4 (O_TSLL (TSLL nullAddr (opt (getTSLL (read var5 var4))) (data (getTSLL (read var5 var4))))))) (= var0 var4))))))) (inv_main13 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Int) (var4 Int) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main23 var7 var6 var5) (and (not (= var4 0)) (and (= var3 0) (and (and (is-O_TSLL (read var7 var5)) (is-O_TSLL (read var7 var5))) (and (and (= var2 (write var7 var5 (O_TSLL (TSLL nullAddr (opt (getTSLL (read var7 var5))) (data (getTSLL (read var7 var5))))))) (= var1 var6)) (= var0 var5))))))) (inv_main32 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Heap)) (or (not (and (inv_main12 var1 var0) (and (is-O_TSLL (read var1 var0)) (is-O_TSLL (read var1 var0))))) (inv_main15 (write var1 var0 (O_TSLL (TSLL (next (getTSLL (read var1 var0))) (opt (getTSLL (read var1 var0))) 1))) var0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Int) (var6 Int) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main42 var9 var8 var7 var6) (and (and (and (or (or (not (= var5 2)) (= var4 var3)) (not (= var2 nullAddr))) (not (= var4 var3))) (and (is-O_TSLL (read var9 var7)) (is-O_TSLL (read var9 (opt (getTSLL (read var9 var7))))))) (and (and (and (and (and (= var1 var9) (= var0 var8)) (= var3 var7)) (= var5 var6)) (= var4 (opt (getTSLL (read var9 var7))))) (= var2 (next (getTSLL (read var9 (opt (getTSLL (read var9 var7))))))))))) (inv_main44 var1 var0 var3 var5 var4 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (and (inv_main32 var2 var1 var0) (and (is-O_TSLL (read var2 var0)) (is-O_TSLL (read var2 var0))))) (inv_main35 (write var2 var0 (O_TSLL (TSLL (next (getTSLL (read var2 var0))) (opt (getTSLL (read var2 var0))) 1))) var1 var0))))
(assert (forall ((var0 TSLL) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main17 var4 var3 var2) (not (= var1 0)))) (inv_main22 (newHeap (alloc var4 (O_TSLL var0))) var3 var2 (newAddr (alloc var4 (O_TSLL var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (and (inv_main11 var2 var1 var0) (and (is-O_TSLL (read var2 var1)) (is-O_TSLL (read var2 var1))))) (inv_main10 (write var2 var1 (O_TSLL (TSLL (next (getTSLL (read var2 var1))) var0 (data (getTSLL (read var2 var1)))))) var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (and (inv_main30 var2 var1 var0) (and (and (is-O_TSLL (read var2 var0)) (is-O_TSLL (read var2 (opt (getTSLL (read var2 var0)))))) (is-O_TSLL (read var2 (opt (getTSLL (read var2 var0)))))))) (inv_main17 (write var2 (opt (getTSLL (read var2 var0))) (O_TSLL (TSLL nullAddr (opt (getTSLL (read var2 (opt (getTSLL (read var2 var0)))))) (data (getTSLL (read var2 (opt (getTSLL (read var2 var0))))))))) var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (and (inv_main35 var2 var1 var0) (and (is-O_TSLL (read var2 var0)) (is-O_TSLL (read var2 var0))))) (inv_main17 (write var2 var0 (O_TSLL (TSLL (next (getTSLL (read var2 var0))) var0 (data (getTSLL (read var2 var0)))))) var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (and (inv_main36 var2 var1 var0) (and (is-O_TSLL (read var2 var0)) (is-O_TSLL (read var2 var0))))) (inv_main17 (write var2 var0 (O_TSLL (TSLL (next (getTSLL (read var2 var0))) var0 (data (getTSLL (read var2 var0)))))) var1 var0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Heap)) (or (not (and (inv_main10 var3 var2) (and (and (and (is-O_TSLL (read var3 var2)) (is-O_TSLL (read var3 (opt (getTSLL (read var3 var2)))))) (is-O_TSLL (read var3 (opt (getTSLL (read var3 var2)))))) (and (= var1 (write var3 (opt (getTSLL (read var3 var2))) (O_TSLL (TSLL nullAddr (opt (getTSLL (read var3 (opt (getTSLL (read var3 var2)))))) (data (getTSLL (read var3 (opt (getTSLL (read var3 var2)))))))))) (= var0 var2))))) (inv_main17 var1 var0 var0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Heap)) (or (not (and (inv_main15 var3 var2) (and (and (is-O_TSLL (read var3 var2)) (is-O_TSLL (read var3 var2))) (and (= var1 (write var3 var2 (O_TSLL (TSLL (next (getTSLL (read var3 var2))) var2 (data (getTSLL (read var3 var2))))))) (= var0 var2))))) (inv_main17 var1 var0 var0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Heap)) (or (not (and (inv_main16 var3 var2) (and (and (is-O_TSLL (read var3 var2)) (is-O_TSLL (read var3 var2))) (and (= var1 (write var3 var2 (O_TSLL (TSLL (next (getTSLL (read var3 var2))) var2 (data (getTSLL (read var3 var2))))))) (= var0 var2))))) (inv_main17 var1 var0 var0))))
(assert (forall ((var0 TSLL) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Heap)) (or (not (and (inv_main6 var4 var3) (and (and (is-O_TSLL (read var4 var3)) (is-O_TSLL (read var4 var3))) (and (= var2 (write var4 var3 (O_TSLL (TSLL (next (getTSLL (read var4 var3))) (opt (getTSLL (read var4 var3))) 2)))) (= var1 var3))))) (inv_main11 (newHeap (alloc var2 (O_TSLL var0))) var1 (newAddr (alloc var2 (O_TSLL var0)))))))
(assert (forall ((var0 TSLL) (var1 Heap)) (or (not (inv_main2 var1)) (inv_main3 (newHeap (alloc var1 (O_TSLL var0))) (newAddr (alloc var1 (O_TSLL var0)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Int) (var4 Addr) (var5 Heap)) (or (not (and (inv_main3 var5 var4) (and (not (= var3 0)) (and (= var2 0) (and (and (is-O_TSLL (read var5 var4)) (is-O_TSLL (read var5 var4))) (and (= var1 (write var5 var4 (O_TSLL (TSLL nullAddr (opt (getTSLL (read var5 var4))) (data (getTSLL (read var5 var4))))))) (= var0 var4))))))) (inv_main12 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Int) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main23 var6 var5 var4) (and (not (= var3 0)) (and (and (is-O_TSLL (read var6 var4)) (is-O_TSLL (read var6 var4))) (and (and (= var2 (write var6 var4 (O_TSLL (TSLL nullAddr (opt (getTSLL (read var6 var4))) (data (getTSLL (read var6 var4))))))) (= var1 var5)) (= var0 var4)))))) (inv_main26 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (and (inv_main39 var2 var1 var0) (is-O_TSLL (read var2 var0)))) (inv_main42 var2 var1 var0 (data (getTSLL (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Int) (var4 Int) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main23 var7 var6 var5) (and (= var4 0) (and (= var3 0) (and (and (is-O_TSLL (read var7 var5)) (is-O_TSLL (read var7 var5))) (and (and (= var2 (write var7 var5 (O_TSLL (TSLL nullAddr (opt (getTSLL (read var7 var5))) (data (getTSLL (read var7 var5))))))) (= var1 var6)) (= var0 var5))))))) (inv_main33 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main51 var6 var5 var4) (and (is-O_TSLL (read var6 var4)) (and (and (and (= var3 var6) (= var2 var5)) (= var1 var4)) (= var0 (next (getTSLL (read var6 var4)))))))) (inv_main52 var3 var2 var0))))
(assert (forall ((var0 TSLL) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main26 var6 var5 var4) (and (and (is-O_TSLL (read var6 var4)) (is-O_TSLL (read var6 var4))) (and (and (= var3 (write var6 var4 (O_TSLL (TSLL (next (getTSLL (read var6 var4))) (opt (getTSLL (read var6 var4))) 2)))) (= var2 var5)) (= var1 var4))))) (inv_main31 (newHeap (alloc var3 (O_TSLL var0))) var2 var1 (newAddr (alloc var3 (O_TSLL var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main22 var3 var2 var1 var0) (and (is-O_TSLL (read var3 var1)) (is-O_TSLL (read var3 var1))))) (inv_main21 (write var3 var1 (O_TSLL (TSLL var0 (opt (getTSLL (read var3 var1))) (data (getTSLL (read var3 var1)))))) var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main21 var6 var5 var4) (and (is-O_TSLL (read var6 var4)) (and (and (and (= var3 var6) (= var2 var5)) (= var1 var4)) (= var0 (next (getTSLL (read var6 var4)))))))) (inv_main23 var3 var2 var0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Int) (var6 Int) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main42 var9 var8 var7 var6) (and (and (or (and (and (= var5 2) (not (= var4 var3))) (= var2 nullAddr)) (= var4 var3)) (and (is-O_TSLL (read var9 var7)) (is-O_TSLL (read var9 (opt (getTSLL (read var9 var7))))))) (and (and (and (and (and (= var1 var9) (= var0 var8)) (= var3 var7)) (= var5 var6)) (= var4 (opt (getTSLL (read var9 var7))))) (= var2 (next (getTSLL (read var9 (opt (getTSLL (read var9 var7))))))))))) (inv_main40 var1 var0 var3))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Addr) (var4 Heap)) (or (not (and (inv_main3 var4 var3) (and (not (= var2 0)) (and (and (is-O_TSLL (read var4 var3)) (is-O_TSLL (read var4 var3))) (and (= var1 (write var4 var3 (O_TSLL (TSLL nullAddr (opt (getTSLL (read var4 var3))) (data (getTSLL (read var4 var3))))))) (= var0 var3)))))) (inv_main6 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (and (inv_main33 var2 var1 var0) (and (is-O_TSLL (read var2 var0)) (is-O_TSLL (read var2 var0))))) (inv_main36 (write var2 var0 (O_TSLL (TSLL (next (getTSLL (read var2 var0))) (opt (getTSLL (read var2 var0))) 0))) var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main31 var3 var2 var1 var0) (and (is-O_TSLL (read var3 var1)) (is-O_TSLL (read var3 var1))))) (inv_main30 (write var3 var1 (O_TSLL (TSLL (next (getTSLL (read var3 var1))) var0 (data (getTSLL (read var3 var1)))))) var2 var1))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Int) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main56 var10 var9 var8 var7) (and (and (not (= var6 nullAddr)) (and (is-O_TSLL (read var10 var9)) (and (and (and (= var5 (write var10 (opt (getTSLL (read var10 var9))) defObj)) (= var4 var9)) (= var3 var8)) (= var2 var7)))) (and (and (= var1 (write var5 var4 defObj)) (= var0 var4)) (= var6 var3))))) (inv_main51 var1 var6 var6))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Int) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main52 var9 var8 var7) (and (and (not (= var6 nullAddr)) (and (and (not (= var5 2)) (is-O_TSLL (read var9 var8))) (and (and (and (= var4 var9) (= var3 var8)) (= var2 var7)) (= var5 (data (getTSLL (read var9 var8))))))) (and (and (= var1 (write var4 var3 defObj)) (= var0 var3)) (= var6 var2))))) (inv_main51 var1 var6 var6))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main40 var6 var5 var4) (and (not (= var3 nullAddr)) (and (= var2 nullAddr) (and (is-O_TSLL (read var6 var4)) (and (and (and (= var1 var6) (= var3 var5)) (= var0 var4)) (= var2 (next (getTSLL (read var6 var4)))))))))) (inv_main51 var1 var3 var3))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main17 var3 var2 var1) (and (not (= var2 nullAddr)) (and (= var2 nullAddr) (= var0 0))))) (inv_main51 var3 var2 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Int) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main52 var6 var5 var4) (and (and (= var3 2) (is-O_TSLL (read var6 var5))) (and (and (and (= var2 var6) (= var1 var5)) (= var0 var4)) (= var3 (data (getTSLL (read var6 var5)))))))) (inv_main56 var2 var1 var0 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main40 var6 var5 var4) (and (not (= var3 nullAddr)) (and (is-O_TSLL (read var6 var4)) (and (and (and (= var2 var6) (= var1 var5)) (= var0 var4)) (= var3 (next (getTSLL (read var6 var4))))))))) (inv_main39 var2 var1 var3))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main17 var3 var2 var1) (and (not (= var2 nullAddr)) (= var0 0)))) (inv_main39 var3 var2 var2))))
(assert (forall ((var0 Addr) (var1 Heap)) (or (not (and (inv_main13 var1 var0) (and (is-O_TSLL (read var1 var0)) (is-O_TSLL (read var1 var0))))) (inv_main16 (write var1 var0 (O_TSLL (TSLL (next (getTSLL (read var1 var0))) (opt (getTSLL (read var1 var0))) 0))) var0))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main3 var1 var0) (not (is-O_TSLL (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main3 var1 var0) (and (is-O_TSLL (read var1 var0)) (not (is-O_TSLL (read var1 var0))))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main6 var1 var0) (not (is-O_TSLL (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main6 var1 var0) (and (is-O_TSLL (read var1 var0)) (not (is-O_TSLL (read var1 var0))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main11 var2 var1 var0) (not (is-O_TSLL (read var2 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main11 var2 var1 var0) (and (is-O_TSLL (read var2 var1)) (not (is-O_TSLL (read var2 var1))))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main10 var1 var0) (not (is-O_TSLL (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main10 var1 var0) (and (is-O_TSLL (read var1 var0)) (not (is-O_TSLL (read var1 (opt (getTSLL (read var1 var0)))))))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main10 var1 var0) (and (and (is-O_TSLL (read var1 var0)) (is-O_TSLL (read var1 (opt (getTSLL (read var1 var0)))))) (not (is-O_TSLL (read var1 (opt (getTSLL (read var1 var0)))))))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main12 var1 var0) (not (is-O_TSLL (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main12 var1 var0) (and (is-O_TSLL (read var1 var0)) (not (is-O_TSLL (read var1 var0))))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main15 var1 var0) (not (is-O_TSLL (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main15 var1 var0) (and (is-O_TSLL (read var1 var0)) (not (is-O_TSLL (read var1 var0))))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main13 var1 var0) (not (is-O_TSLL (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main13 var1 var0) (and (is-O_TSLL (read var1 var0)) (not (is-O_TSLL (read var1 var0))))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main16 var1 var0) (not (is-O_TSLL (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main16 var1 var0) (and (is-O_TSLL (read var1 var0)) (not (is-O_TSLL (read var1 var0))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main22 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main22 var3 var2 var1 var0) (and (is-O_TSLL (read var3 var1)) (not (is-O_TSLL (read var3 var1))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main21 var2 var1 var0) (not (is-O_TSLL (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main23 var2 var1 var0) (not (is-O_TSLL (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main23 var2 var1 var0) (and (is-O_TSLL (read var2 var0)) (not (is-O_TSLL (read var2 var0))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main26 var2 var1 var0) (not (is-O_TSLL (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main26 var2 var1 var0) (and (is-O_TSLL (read var2 var0)) (not (is-O_TSLL (read var2 var0))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main31 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main31 var3 var2 var1 var0) (and (is-O_TSLL (read var3 var1)) (not (is-O_TSLL (read var3 var1))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main30 var2 var1 var0) (not (is-O_TSLL (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main30 var2 var1 var0) (and (is-O_TSLL (read var2 var0)) (not (is-O_TSLL (read var2 (opt (getTSLL (read var2 var0)))))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main30 var2 var1 var0) (and (and (is-O_TSLL (read var2 var0)) (is-O_TSLL (read var2 (opt (getTSLL (read var2 var0)))))) (not (is-O_TSLL (read var2 (opt (getTSLL (read var2 var0)))))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main32 var2 var1 var0) (not (is-O_TSLL (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main32 var2 var1 var0) (and (is-O_TSLL (read var2 var0)) (not (is-O_TSLL (read var2 var0))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main35 var2 var1 var0) (not (is-O_TSLL (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main35 var2 var1 var0) (and (is-O_TSLL (read var2 var0)) (not (is-O_TSLL (read var2 var0))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main33 var2 var1 var0) (not (is-O_TSLL (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main33 var2 var1 var0) (and (is-O_TSLL (read var2 var0)) (not (is-O_TSLL (read var2 var0))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main36 var2 var1 var0) (not (is-O_TSLL (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main36 var2 var1 var0) (and (is-O_TSLL (read var2 var0)) (not (is-O_TSLL (read var2 var0))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main39 var2 var1 var0) (not (is-O_TSLL (read var2 var0)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main42 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var1)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main42 var3 var2 var1 var0) (and (is-O_TSLL (read var3 var1)) (not (is-O_TSLL (read var3 (opt (getTSLL (read var3 var1)))))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap)) (not (inv_main44 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main40 var2 var1 var0) (not (is-O_TSLL (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main51 var2 var1 var0) (not (is-O_TSLL (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main52 var2 var1 var0) (not (is-O_TSLL (read var2 var1)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main56 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var2)))))))
(check-sat)
