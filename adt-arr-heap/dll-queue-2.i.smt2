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
   (TSLL (next Addr) (prev Addr) (data Int))
  )
))
(declare-fun inv_main101 (Heap Addr Addr Int) Bool)
(declare-fun inv_main105 (Heap Addr Addr Int) Bool)
(declare-fun inv_main108 (Heap Addr Addr Int) Bool)
(declare-fun inv_main111 (Heap Addr Addr Int) Bool)
(declare-fun inv_main113 (Heap Addr Addr Int) Bool)
(declare-fun inv_main12 (Heap Addr Addr Int) Bool)
(declare-fun inv_main121 (Heap Addr Addr Int) Bool)
(declare-fun inv_main13 (Heap Addr Addr Int Addr) Bool)
(declare-fun inv_main14 (Heap Addr Addr Int) Bool)
(declare-fun inv_main15 (Heap Addr Addr Int) Bool)
(declare-fun inv_main18 (Heap Addr Addr Int) Bool)
(declare-fun inv_main19 (Heap Addr Addr Int) Bool)
(declare-fun inv_main2 (Heap) Bool)
(declare-fun inv_main22 (Heap Addr Addr Int) Bool)
(declare-fun inv_main25 (Heap Addr Addr Int) Bool)
(declare-fun inv_main3 (Heap Addr) Bool)
(declare-fun inv_main30 (Heap Addr Addr Int) Bool)
(declare-fun inv_main34 (Heap Addr Addr Int) Bool)
(declare-fun inv_main39 (Heap Addr Addr Int) Bool)
(declare-fun inv_main4 (Heap Addr) Bool)
(declare-fun inv_main42 (Heap Addr Addr Int) Bool)
(declare-fun inv_main45 (Heap Addr Addr Int) Bool)
(declare-fun inv_main47 (Heap Addr Addr Int) Bool)
(declare-fun inv_main5 (Heap Addr) Bool)
(declare-fun inv_main51 (Heap Addr Addr Int) Bool)
(declare-fun inv_main55 (Heap Addr Addr Int) Bool)
(declare-fun inv_main58 (Heap Addr Addr Int) Bool)
(declare-fun inv_main60 (Heap Addr Addr Int) Bool)
(declare-fun inv_main63 (Heap Addr Addr Int) Bool)
(declare-fun inv_main65 (Heap Addr Addr Int) Bool)
(declare-fun inv_main70 (Heap Addr Addr Int) Bool)
(declare-fun inv_main74 (Heap Addr Addr Int) Bool)
(declare-fun inv_main77 (Heap Addr Addr Int) Bool)
(declare-fun inv_main79 (Heap Addr Addr Int) Bool)
(declare-fun inv_main8 (Heap Addr Addr Int) Bool)
(declare-fun inv_main82 (Heap Addr Addr Int) Bool)
(declare-fun inv_main84 (Heap Addr Addr Int) Bool)
(declare-fun inv_main88 (Heap Addr Addr Int) Bool)
(declare-fun inv_main90 (Heap Addr Addr Int) Bool)
(declare-fun inv_main94 (Heap Addr Addr Int) Bool)
(declare-fun inv_main96 (Heap Addr Addr Int) Bool)
(assert (inv_main2 emptyHeap))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Int) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main45 var8 var7 var6 var5) (and (and (= var4 nullAddr) (is-O_TSLL (read var8 var7))) (and (and (and (and (= var3 var8) (= var2 var7)) (= var1 var6)) (= var0 var5)) (= var4 (next (getTSLL (read var8 var7)))))))) (inv_main51 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Int) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main82 var8 var7 var6 var5) (and (and (= var4 nullAddr) (and (is-O_TSLL (read var8 var7)) (is-O_TSLL (read var8 (next (getTSLL (read var8 var7))))))) (and (and (and (and (= var3 var8) (= var2 var7)) (= var1 var6)) (= var0 var5)) (= var4 (next (getTSLL (read var8 (next (getTSLL (read var8 var7))))))))))) (inv_main90 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main55 var3 var2 var1 var0) (and (not (= var2 nullAddr)) (= var0 3)))) (inv_main77 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Int) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main88 var8 var7 var6 var5) (and (and (= var4 nullAddr) (and (and (is-O_TSLL (read var8 var7)) (is-O_TSLL (read var8 (next (getTSLL (read var8 var7)))))) (is-O_TSLL (read var8 (next (getTSLL (read var8 (next (getTSLL (read var8 var7)))))))))) (and (and (and (and (= var3 var8) (= var2 var7)) (= var1 var6)) (= var0 var5)) (= var4 (next (getTSLL (read var8 (next (getTSLL (read var8 (next (getTSLL (read var8 var7)))))))))))))) (inv_main96 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Int) (var4 Int) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main15 var7 var6 var5 var4) (and (<= 0 (+ var3 (- 2))) (and (not (= var3 1)) (and (and (not (= var3 0)) (is-O_TSLL (read var7 var5))) (and (and (and (= var2 (write var7 var5 (O_TSLL (TSLL nullAddr (prev (getTSLL (read var7 var5))) (data (getTSLL (read var7 var5))))))) (= var1 var6)) (= var0 var5)) (= var3 var4))))))) (inv_main25 var2 var1 var0 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Int) (var4 Int) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main15 var7 var6 var5 var4) (and (and (= var3 0) (is-O_TSLL (read var7 var5))) (and (and (and (= var2 (write var7 var5 (O_TSLL (TSLL nullAddr (prev (getTSLL (read var7 var5))) (data (getTSLL (read var7 var5))))))) (= var1 var6)) (= var0 var5)) (= var3 var4))))) (inv_main19 var2 var1 var0 var3))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main42 var3 var2 var1 var0) (not (= var0 2)))) (inv_main55 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Int) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main63 var8 var7 var6 var5) (and (and (not (= var4 nullAddr)) (and (is-O_TSLL (read var8 var7)) (is-O_TSLL (read var8 (next (getTSLL (read var8 var7))))))) (and (and (and (and (= var3 var8) (= var2 var7)) (= var1 var6)) (= var0 var5)) (= var4 (next (getTSLL (read var8 (next (getTSLL (read var8 var7))))))))))) (inv_main55 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Heap)) (or (not (and (inv_main3 var1 var0) (is-O_TSLL (read var1 var0)))) (inv_main4 (write var1 var0 (O_TSLL (TSLL nullAddr (prev (getTSLL (read var1 var0))) (data (getTSLL (read var1 var0)))))) var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Int) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main82 var8 var7 var6 var5) (and (and (not (= var4 nullAddr)) (and (is-O_TSLL (read var8 var7)) (is-O_TSLL (read var8 (next (getTSLL (read var8 var7))))))) (and (and (and (and (= var3 var8) (= var2 var7)) (= var1 var6)) (= var0 var5)) (= var4 (next (getTSLL (read var8 (next (getTSLL (read var8 var7))))))))))) (inv_main88 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main8 var4 var3 var2 var1) (and (not (= var3 nullAddr)) (and (= var1 1) (and (not (= var3 nullAddr)) (= var0 0)))))) (inv_main45 var4 var3 var2 var1))))
(assert (forall ((var0 Addr) (var1 Heap)) (or (not (and (inv_main4 var1 var0) (is-O_TSLL (read var1 var0)))) (inv_main5 (write var1 var0 (O_TSLL (TSLL (next (getTSLL (read var1 var0))) nullAddr (data (getTSLL (read var1 var0)))))) var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Int) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main63 var8 var7 var6 var5) (and (and (= var4 nullAddr) (and (is-O_TSLL (read var8 var7)) (is-O_TSLL (read var8 (next (getTSLL (read var8 var7))))))) (and (and (and (and (= var3 var8) (= var2 var7)) (= var1 var6)) (= var0 var5)) (= var4 (next (getTSLL (read var8 (next (getTSLL (read var8 var7))))))))))) (inv_main70 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main8 var4 var3 var2 var1) (and (= var3 nullAddr) (and (= var1 1) (and (not (= var3 nullAddr)) (= var0 0)))))) (inv_main47 var4 var3 var2 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Int) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main77 var8 var7 var6 var5) (and (and (= var4 nullAddr) (is-O_TSLL (read var8 var7))) (and (and (and (and (= var3 var8) (= var2 var7)) (= var1 var6)) (= var0 var5)) (= var4 (next (getTSLL (read var8 var7)))))))) (inv_main84 var3 var2 var1 var0))))
(assert (forall ((var0 TSLL) (var1 Int) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main8 var5 var4 var3 var2) (not (= var1 0)))) (inv_main13 (newHeap (alloc var5 (O_TSLL var0))) var4 var3 var2 (newAddr (alloc var5 (O_TSLL var0)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Int) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main77 var8 var7 var6 var5) (and (and (not (= var4 nullAddr)) (is-O_TSLL (read var8 var7))) (and (and (and (and (= var3 var8) (= var2 var7)) (= var1 var6)) (= var0 var5)) (= var4 (next (getTSLL (read var8 var7)))))))) (inv_main82 var3 var2 var1 var0))))
(assert (forall ((var0 TSLL) (var1 Heap)) (or (not (inv_main2 var1)) (inv_main3 (newHeap (alloc var1 (O_TSLL var0))) (newAddr (alloc var1 (O_TSLL var0)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Int) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main94 var8 var7 var6 var5) (and (and (= var4 3) (and (and (and (is-O_TSLL (read var8 var7)) (is-O_TSLL (read var8 (next (getTSLL (read var8 var7)))))) (is-O_TSLL (read var8 (next (getTSLL (read var8 (next (getTSLL (read var8 var7))))))))) (is-O_TSLL (read var8 (next (getTSLL (read var8 (next (getTSLL (read var8 (next (getTSLL (read var8 var7))))))))))))) (and (and (and (and (= var3 var8) (= var2 var7)) (= var1 var6)) (= var0 var5)) (= var4 (data (getTSLL (read var8 (next (getTSLL (read var8 (next (getTSLL (read var8 (next (getTSLL (read var8 var7))))))))))))))))) (inv_main101 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Int) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main74 var8 var7 var6 var5) (and (is-O_TSLL (read var8 var7)) (and (and (and (and (= var4 var8) (= var3 var7)) (= var2 var6)) (= var1 var5)) (= var0 (next (getTSLL (read var8 var7)))))))) (inv_main105 var4 var3 var0 var1))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Int) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main111 var8 var7 var6 var5) (and (is-O_TSLL (read var8 var6)) (and (and (and (and (= var4 var8) (= var3 var7)) (= var2 var6)) (= var1 var5)) (= var0 (next (getTSLL (read var8 var6)))))))) (inv_main105 var4 var3 var0 var1))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main8 var4 var3 var2 var1) (and (= var3 nullAddr) (= var0 0)))) (inv_main39 var4 var3 var2 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main42 var3 var2 var1 var0) (and (not (= var2 nullAddr)) (= var0 2)))) (inv_main58 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Int) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main88 var8 var7 var6 var5) (and (and (not (= var4 nullAddr)) (and (and (is-O_TSLL (read var8 var7)) (is-O_TSLL (read var8 (next (getTSLL (read var8 var7)))))) (is-O_TSLL (read var8 (next (getTSLL (read var8 (next (getTSLL (read var8 var7)))))))))) (and (and (and (and (= var3 var8) (= var2 var7)) (= var1 var6)) (= var0 var5)) (= var4 (next (getTSLL (read var8 (next (getTSLL (read var8 (next (getTSLL (read var8 var7)))))))))))))) (inv_main94 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Int) (var6 Addr) (var7 Addr) (var8 Heap) (var9 Int) (var10 Int) (var11 Addr) (var12 Addr) (var13 Heap)) (or (not (and (inv_main108 var13 var12 var11 var10) (and (and (= var9 0) (and (and (not (= var10 0)) (is-O_TSLL (read var13 var11))) (and (and (and (and (= var8 var13) (= var7 var12)) (= var6 var11)) (= var5 var10)) (= var4 (data (getTSLL (read var13 var11))))))) (and (and (and (and (= var3 var8) (= var2 var7)) (= var1 var6)) (= var0 var5)) (or (and (<= 0 (+ var4 (- 1))) (= var9 1)) (and (not (<= 0 (+ var4 (- 1)))) (= var9 0))))))) (inv_main113 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main8 var4 var3 var2 var1) (and (not (= var1 1)) (and (not (= var3 nullAddr)) (= var0 0))))) (inv_main42 var4 var3 var2 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Int) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main45 var8 var7 var6 var5) (and (and (not (= var4 nullAddr)) (is-O_TSLL (read var8 var7))) (and (and (and (and (= var3 var8) (= var2 var7)) (= var1 var6)) (= var0 var5)) (= var4 (next (getTSLL (read var8 var7)))))))) (inv_main42 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main19 var7 var6 var5 var4) (and (is-O_TSLL (read var7 var5)) (and (and (and (= var3 (write var7 var5 (O_TSLL (TSLL (next (getTSLL (read var7 var5))) (prev (getTSLL (read var7 var5))) 1)))) (= var2 var6)) (= var1 var5)) (= var0 var4))))) (inv_main18 var3 var2 var1 1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main22 var7 var6 var5 var4) (and (is-O_TSLL (read var7 var5)) (and (and (and (= var3 (write var7 var5 (O_TSLL (TSLL (next (getTSLL (read var7 var5))) (prev (getTSLL (read var7 var5))) 2)))) (= var2 var6)) (= var1 var5)) (= var0 var4))))) (inv_main18 var3 var2 var1 2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Int) (var4 Int) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main15 var7 var6 var5 var4) (and (not (<= 0 (+ var3 (- 2)))) (and (not (= var3 1)) (and (and (not (= var3 0)) (is-O_TSLL (read var7 var5))) (and (and (and (= var2 (write var7 var5 (O_TSLL (TSLL nullAddr (prev (getTSLL (read var7 var5))) (data (getTSLL (read var7 var5))))))) (= var1 var6)) (= var0 var5)) (= var3 var4))))))) (inv_main18 var2 var1 var0 var3))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main25 var7 var6 var5 var4) (and (is-O_TSLL (read var7 var5)) (and (and (and (= var3 (write var7 var5 (O_TSLL (TSLL (next (getTSLL (read var7 var5))) (prev (getTSLL (read var7 var5))) 3)))) (= var2 var6)) (= var1 var5)) (= var0 var4))))) (inv_main18 var3 var2 var1 3))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main13 var4 var3 var2 var1 var0) (is-O_TSLL (read var4 var2)))) (inv_main12 (write var4 var2 (O_TSLL (TSLL var0 (prev (getTSLL (read var4 var2))) (data (getTSLL (read var4 var2)))))) var3 var2 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main55 var3 var2 var1 var0) (and (= var2 nullAddr) (= var0 3)))) (inv_main79 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main105 var3 var2 var1 var0) (and (not (= var2 nullAddr)) (= var1 nullAddr)))) (inv_main121 var3 var2 var2 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main105 var4 var3 var2 var1) (and (not (= var3 nullAddr)) (and (= var0 0) (not (= var2 nullAddr)))))) (inv_main121 var4 var3 var3 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Int) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Int) (var10 Addr) (var11 Addr) (var12 Heap)) (or (not (and (inv_main121 var12 var11 var10 var9) (and (and (not (= var8 nullAddr)) (and (is-O_TSLL (read var12 var11)) (and (and (and (and (= var7 var12) (= var6 var11)) (= var5 var10)) (= var4 var9)) (= var3 (next (getTSLL (read var12 var11))))))) (and (and (and (= var2 (write var7 var5 defObj)) (= var8 var3)) (= var1 var5)) (= var0 var4))))) (inv_main121 var2 var8 var8 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main12 var3 var2 var1 var0) (and (is-O_TSLL (read var3 var1)) (is-O_TSLL (read var3 (next (getTSLL (read var3 var1)))))))) (inv_main14 (write var3 (next (getTSLL (read var3 var1))) (O_TSLL (TSLL (next (getTSLL (read var3 (next (getTSLL (read var3 var1)))))) var1 (data (getTSLL (read var3 (next (getTSLL (read var3 var1))))))))) var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main18 var3 var2 var1 var0) (= var2 nullAddr))) (inv_main30 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Int) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main14 var8 var7 var6 var5) (and (is-O_TSLL (read var8 var6)) (and (and (and (and (= var4 var8) (= var3 var7)) (= var2 var6)) (= var1 var5)) (= var0 (next (getTSLL (read var8 var6)))))))) (inv_main15 var4 var3 var0 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Int) (var4 Int) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main15 var7 var6 var5 var4) (and (= var3 1) (and (and (not (= var3 0)) (is-O_TSLL (read var7 var5))) (and (and (and (= var2 (write var7 var5 (O_TSLL (TSLL nullAddr (prev (getTSLL (read var7 var5))) (data (getTSLL (read var7 var5))))))) (= var1 var6)) (= var0 var5)) (= var3 var4)))))) (inv_main22 var2 var1 var0 var3))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main42 var3 var2 var1 var0) (and (= var2 nullAddr) (= var0 2)))) (inv_main60 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main18 var3 var2 var1 var0) (and (not (= var1 nullAddr)) (not (= var2 nullAddr))))) (inv_main8 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Heap)) (or (not (and (inv_main5 var3 var2) (and (is-O_TSLL (read var3 var2)) (and (= var1 (write var3 var2 (O_TSLL (TSLL (next (getTSLL (read var3 var2))) (prev (getTSLL (read var3 var2))) 0)))) (= var0 var2))))) (inv_main8 var1 var0 var0 0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main105 var4 var3 var2 var1) (and (not (= var0 0)) (not (= var2 nullAddr))))) (inv_main108 var4 var3 var2 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Int) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main58 var8 var7 var6 var5) (and (and (= var4 nullAddr) (is-O_TSLL (read var8 var7))) (and (and (and (and (= var3 var8) (= var2 var7)) (= var1 var6)) (= var0 var5)) (= var4 (next (getTSLL (read var8 var7)))))))) (inv_main65 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main18 var3 var2 var1 var0) (and (= var1 nullAddr) (not (= var2 nullAddr))))) (inv_main34 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main108 var3 var2 var1 var0) (= var0 0))) (inv_main111 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Int) (var6 Addr) (var7 Addr) (var8 Heap) (var9 Int) (var10 Int) (var11 Addr) (var12 Addr) (var13 Heap)) (or (not (and (inv_main108 var13 var12 var11 var10) (and (and (not (= var9 0)) (and (and (not (= var10 0)) (is-O_TSLL (read var13 var11))) (and (and (and (and (= var8 var13) (= var7 var12)) (= var6 var11)) (= var5 var10)) (= var4 (data (getTSLL (read var13 var11))))))) (and (and (and (and (= var3 var8) (= var2 var7)) (= var1 var6)) (= var0 var5)) (or (and (<= 0 (+ var4 (- 1))) (= var9 1)) (and (not (<= 0 (+ var4 (- 1)))) (= var9 0))))))) (inv_main111 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main55 var3 var2 var1 var0) (not (= var0 3)))) (inv_main74 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Int) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main94 var8 var7 var6 var5) (and (and (not (= var4 3)) (and (and (and (is-O_TSLL (read var8 var7)) (is-O_TSLL (read var8 (next (getTSLL (read var8 var7)))))) (is-O_TSLL (read var8 (next (getTSLL (read var8 (next (getTSLL (read var8 var7))))))))) (is-O_TSLL (read var8 (next (getTSLL (read var8 (next (getTSLL (read var8 (next (getTSLL (read var8 var7))))))))))))) (and (and (and (and (= var3 var8) (= var2 var7)) (= var1 var6)) (= var0 var5)) (= var4 (data (getTSLL (read var8 (next (getTSLL (read var8 (next (getTSLL (read var8 (next (getTSLL (read var8 var7))))))))))))))))) (inv_main74 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Int) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main58 var8 var7 var6 var5) (and (and (not (= var4 nullAddr)) (is-O_TSLL (read var8 var7))) (and (and (and (and (= var3 var8) (= var2 var7)) (= var1 var6)) (= var0 var5)) (= var4 (next (getTSLL (read var8 var7)))))))) (inv_main63 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main3 var1 var0) (not (is-O_TSLL (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main4 var1 var0) (not (is-O_TSLL (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main5 var1 var0) (not (is-O_TSLL (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main13 var4 var3 var2 var1 var0) (not (is-O_TSLL (read var4 var2)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main12 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var1)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main12 var3 var2 var1 var0) (and (is-O_TSLL (read var3 var1)) (not (is-O_TSLL (read var3 (next (getTSLL (read var3 var1)))))))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main14 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var1)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main15 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var1)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main19 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var1)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main22 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var1)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main25 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var1)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (inv_main30 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (inv_main34 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (inv_main39 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (inv_main47 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main45 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var2)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (inv_main51 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (inv_main60 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main58 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var2)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (inv_main65 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main63 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var2)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main63 var3 var2 var1 var0) (and (is-O_TSLL (read var3 var2)) (not (is-O_TSLL (read var3 (next (getTSLL (read var3 var2)))))))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (inv_main70 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (inv_main79 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main77 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var2)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (inv_main84 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main82 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var2)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main82 var3 var2 var1 var0) (and (is-O_TSLL (read var3 var2)) (not (is-O_TSLL (read var3 (next (getTSLL (read var3 var2)))))))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (inv_main90 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main88 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var2)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main88 var3 var2 var1 var0) (and (is-O_TSLL (read var3 var2)) (not (is-O_TSLL (read var3 (next (getTSLL (read var3 var2)))))))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main88 var3 var2 var1 var0) (and (and (is-O_TSLL (read var3 var2)) (is-O_TSLL (read var3 (next (getTSLL (read var3 var2)))))) (not (is-O_TSLL (read var3 (next (getTSLL (read var3 (next (getTSLL (read var3 var2))))))))))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (inv_main96 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main94 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var2)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main94 var3 var2 var1 var0) (and (is-O_TSLL (read var3 var2)) (not (is-O_TSLL (read var3 (next (getTSLL (read var3 var2)))))))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main94 var3 var2 var1 var0) (and (and (is-O_TSLL (read var3 var2)) (is-O_TSLL (read var3 (next (getTSLL (read var3 var2)))))) (not (is-O_TSLL (read var3 (next (getTSLL (read var3 (next (getTSLL (read var3 var2))))))))))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main94 var3 var2 var1 var0) (and (and (and (is-O_TSLL (read var3 var2)) (is-O_TSLL (read var3 (next (getTSLL (read var3 var2)))))) (is-O_TSLL (read var3 (next (getTSLL (read var3 (next (getTSLL (read var3 var2))))))))) (not (is-O_TSLL (read var3 (next (getTSLL (read var3 (next (getTSLL (read var3 (next (getTSLL (read var3 var2)))))))))))))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (inv_main101 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main74 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var2)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main108 var3 var2 var1 var0) (and (not (= var0 0)) (not (is-O_TSLL (read var3 var1))))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (inv_main113 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main111 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var1)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main121 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var2)))))))
(check-sat)
