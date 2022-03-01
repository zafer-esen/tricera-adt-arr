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
(declare-fun inv_main101 (Heap Addr Addr Int Addr) Bool)
(declare-fun inv_main11 (Heap Addr Addr Int) Bool)
(declare-fun inv_main12 (Heap Addr Addr Int Addr) Bool)
(declare-fun inv_main13 (Heap Addr Addr Int) Bool)
(declare-fun inv_main2 (Heap) Bool)
(declare-fun inv_main20 (Heap Addr Addr Int) Bool)
(declare-fun inv_main21 (Heap Addr Addr Int) Bool)
(declare-fun inv_main25 (Heap Addr Addr Int) Bool)
(declare-fun inv_main28 (Heap Addr Addr Int) Bool)
(declare-fun inv_main29 (Heap Addr Addr Int) Bool)
(declare-fun inv_main3 (Heap Addr) Bool)
(declare-fun inv_main30 (Heap Addr Addr Int) Bool)
(declare-fun inv_main31 (Heap Addr Addr Int Addr) Bool)
(declare-fun inv_main34 (Heap Addr Addr Int) Bool)
(declare-fun inv_main36 (Heap Addr Addr Int) Bool)
(declare-fun inv_main4 (Heap Addr) Bool)
(declare-fun inv_main42 (Heap Addr Addr Int) Bool)
(declare-fun inv_main46 (Heap Addr Addr Int) Bool)
(declare-fun inv_main49 (Heap Addr Addr Int) Bool)
(declare-fun inv_main53 (Heap Addr Addr Int Addr) Bool)
(declare-fun inv_main54 (Heap Addr Addr Int Addr) Bool)
(declare-fun inv_main55 (Heap Addr Addr Int Addr) Bool)
(declare-fun inv_main57 (Heap Addr Addr Int Addr) Bool)
(declare-fun inv_main58 (Heap Addr Addr Int Addr) Bool)
(declare-fun inv_main60 (Heap Addr Addr Int Addr) Bool)
(declare-fun inv_main61 (Heap Addr Addr Int Addr Addr) Bool)
(declare-fun inv_main63 (Heap Addr Addr Int Addr) Bool)
(declare-fun inv_main64 (Heap Addr Addr Int Addr) Bool)
(declare-fun inv_main65 (Heap Addr Addr Int Addr) Bool)
(declare-fun inv_main68 (Heap Addr Addr Int Addr) Bool)
(declare-fun inv_main7 (Heap Addr Addr Int) Bool)
(declare-fun inv_main72 (Heap Addr Addr Int Addr) Bool)
(declare-fun inv_main76 (Heap Addr Addr Int Addr) Bool)
(declare-fun inv_main78 (Heap Addr Addr Int Addr) Bool)
(declare-fun inv_main83 (Heap Addr Addr Int Addr) Bool)
(declare-fun inv_main84 (Heap Addr Addr Int Addr) Bool)
(declare-fun inv_main88 (Heap Addr Addr Int Addr) Bool)
(declare-fun inv_main92 (Heap Addr Addr Int Addr) Bool)
(declare-fun inv_main94 (Heap Addr Addr Int Addr) Bool)
(assert (inv_main2 emptyHeap))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Int) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main42 var8 var7 var6 var5) (and (is-O_TSLL (read var8 var6)) (and (and (and (and (= var4 var8) (= var3 var7)) (= var2 var6)) (= var1 var5)) (= var0 (next (getTSLL (read var8 var6)))))))) (inv_main46 var4 var3 var0 var1))))
(assert (forall ((var0 TSLL) (var1 Heap)) (or (not (inv_main2 var1)) (inv_main3 (newHeap (alloc var1 (O_TSLL var0))) (newAddr (alloc var1 (O_TSLL var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Int) (var6 Addr) (var7 Int) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main68 var10 var9 var8 var7 var6) (and (not (= var5 0)) (and (and (= var4 0) (is-O_TSLL (read var10 var8))) (and (and (and (and (and (= var3 var10) (= var2 var9)) (= var1 var8)) (= var5 var7)) (= var0 var6)) (= var4 (data (getTSLL (read var10 var8))))))))) (inv_main78 var3 var2 var1 var5 var0))))
(assert (forall ((var0 Addr) (var1 Heap)) (or (not (and (inv_main3 var1 var0) (is-O_TSLL (read var1 var0)))) (inv_main4 (write var1 var0 (O_TSLL (TSLL nullAddr (data (getTSLL (read var1 var0)))))) var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Int) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main83 var10 var9 var8 var7 var6) (and (is-O_TSLL (read var10 var8)) (and (and (and (and (and (= var5 var10) (= var4 var9)) (= var3 var8)) (= var2 var7)) (= var1 var6)) (= var0 (data (getTSLL (read var10 var8)))))))) (inv_main84 var5 var4 var3 var0 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main20 var3 var2 var1 var0) (is-O_TSLL (read var3 var1)))) (inv_main7 (write var3 var1 (O_TSLL (TSLL (next (getTSLL (read var3 var1))) 1))) var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main21 var3 var2 var1 var0) (is-O_TSLL (read var3 var1)))) (inv_main7 (write var3 var1 (O_TSLL (TSLL (next (getTSLL (read var3 var1))) 0))) var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Heap)) (or (not (and (inv_main4 var3 var2) (and (is-O_TSLL (read var3 var2)) (and (= var1 (write var3 var2 (O_TSLL (TSLL (next (getTSLL (read var3 var2))) 0)))) (= var0 var2))))) (inv_main7 var1 var0 var0 0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main58 var4 var3 var2 var1 var0) (is-O_TSLL (read var4 var2)))) (inv_main61 var4 var3 var2 var1 var0 (next (getTSLL (read var4 var2)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Int) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main55 var10 var9 var8 var7 var6) (and (and (not (= var5 nullAddr)) (is-O_TSLL (read var10 var8))) (and (and (and (and (and (= var4 var10) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var0 var6)) (= var5 (next (getTSLL (read var10 var8)))))))) (inv_main58 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main31 var4 var3 var2 var1 var0) (= var0 nullAddr))) (inv_main29 var4 var3 var2 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Int) (var6 Addr) (var7 Addr) (var8 Heap) (var9 Int) (var10 Addr) (var11 Int) (var12 Addr) (var13 Addr) (var14 Heap)) (or (not (and (inv_main31 var14 var13 var12 var11 var10) (and (and (= var9 0) (and (and (and (not (= var10 nullAddr)) (is-O_TSLL (read var14 var12))) (is-O_TSLL (read var14 (next (getTSLL (read var14 var12)))))) (and (and (and (and (= var8 var14) (= var7 var13)) (= var6 var12)) (= var5 var11)) (= var4 (data (getTSLL (read var14 (next (getTSLL (read var14 var12)))))))))) (and (and (and (and (= var3 var8) (= var2 var7)) (= var1 var6)) (= var0 var5)) (or (and (= var4 0) (= var9 1)) (and (not (= var4 0)) (= var9 0))))))) (inv_main29 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Int) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main46 var8 var7 var6 var5) (and (and (= var4 1) (is-O_TSLL (read var8 var6))) (and (and (and (and (= var3 var8) (= var2 var7)) (= var1 var6)) (= var0 var5)) (= var4 (data (getTSLL (read var8 var6)))))))) (inv_main29 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Int) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main30 var8 var7 var6 var5) (and (and (not (= var4 0)) (is-O_TSLL (read var8 var6))) (and (and (and (and (= var3 var8) (= var2 var7)) (= var1 var6)) (= var0 var5)) (= var4 (data (getTSLL (read var8 var6)))))))) (inv_main36 var3 var2 var1 var0))))
(assert (forall ((var0 TSLL) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Int) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main29 var9 var8 var7 var6) (and (and (= var5 nullAddr) (is-O_TSLL (read var9 var7))) (and (and (and (and (= var4 var9) (= var3 var8)) (= var2 var7)) (= var1 var6)) (= var5 (next (getTSLL (read var9 var7)))))))) (inv_main53 (newHeap (alloc var4 (O_TSLL var0))) var3 var2 var1 (newAddr (alloc var4 (O_TSLL var0)))))))
(assert (forall ((var0 TSLL) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Int) (var7 Int) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main29 var10 var9 var8 var7) (and (= var6 0) (and (and (not (= var5 nullAddr)) (is-O_TSLL (read var10 var8))) (and (and (and (and (= var4 var10) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var5 (next (getTSLL (read var10 var8))))))))) (inv_main53 (newHeap (alloc var4 (O_TSLL var0))) var3 var2 var1 (newAddr (alloc var4 (O_TSLL var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Int) (var6 Addr) (var7 Int) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main68 var10 var9 var8 var7 var6) (and (= var5 0) (and (and (= var4 0) (is-O_TSLL (read var10 var8))) (and (and (and (and (and (= var3 var10) (= var2 var9)) (= var1 var8)) (= var5 var7)) (= var0 var6)) (= var4 (data (getTSLL (read var10 var8))))))))) (inv_main76 var3 var2 var1 var5 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main7 var4 var3 var2 var1) (and (= nullAddr var3) (and (= var0 0) (not (= var1 0)))))) (inv_main25 var4 var3 var3 var1))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main64 var4 var3 var2 var1 var0) (not (= var2 nullAddr)))) (inv_main83 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Int) (var4 Int) (var5 Int) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main13 var8 var7 var6 var5) (and (= var4 0) (and (= var3 0) (and (is-O_TSLL (read var8 var6)) (and (and (and (= var2 (write var8 var6 (O_TSLL (TSLL nullAddr (data (getTSLL (read var8 var6))))))) (= var1 var7)) (= var0 var6)) (= var4 var5))))))) (inv_main21 var2 var1 var0 var4))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main61 var5 var4 var3 var2 var1 var0) (is-O_TSLL (read var5 var1)))) (inv_main60 (write var5 var1 (O_TSLL (TSLL var0 (data (getTSLL (read var5 var1)))))) var4 var3 var2 var1))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Int) (var6 Addr) (var7 Int) (var8 Addr) (var9 Addr) (var10 Heap) (var11 Int) (var12 Addr) (var13 Int) (var14 Addr) (var15 Addr) (var16 Heap)) (or (not (and (inv_main63 var16 var15 var14 var13 var12) (and (and (not (= var11 0)) (and (and (not (= var14 nullAddr)) (is-O_TSLL (read var16 var14))) (and (and (and (and (and (= var10 var16) (= var9 var15)) (= var8 var14)) (= var7 var13)) (= var6 var12)) (= var5 (data (getTSLL (read var16 var14))))))) (and (and (and (and (and (= var4 var10) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var0 var6)) (or (and (not (= var5 1)) (= var11 1)) (and (= var5 1) (= var11 0))))))) (inv_main65 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Int) (var6 Addr) (var7 Int) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main68 var10 var9 var8 var7 var6) (and (and (not (= var5 0)) (is-O_TSLL (read var10 var8))) (and (and (and (and (and (= var4 var10) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var0 var6)) (= var5 (data (getTSLL (read var10 var8)))))))) (inv_main72 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main12 var4 var3 var2 var1 var0) (is-O_TSLL (read var4 var2)))) (inv_main11 (write var4 var2 (O_TSLL (TSLL var0 (data (getTSLL (read var4 var2)))))) var3 var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Int) (var6 Addr) (var7 Int) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main84 var10 var9 var8 var7 var6) (and (not (= var5 1)) (and (and (= var4 1) (is-O_TSLL (read var10 var8))) (and (and (and (and (and (= var3 var10) (= var2 var9)) (= var1 var8)) (= var5 var7)) (= var0 var6)) (= var4 (data (getTSLL (read var10 var8))))))))) (inv_main94 var3 var2 var1 var5 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Int) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main92 var10 var9 var8 var7 var6) (and (is-O_TSLL (read var10 var8)) (and (and (and (and (and (= var5 var10) (= var4 var9)) (= var3 var8)) (= var2 var7)) (= var1 var6)) (= var0 (next (getTSLL (read var10 var8)))))))) (inv_main64 var5 var4 var0 var2 var1))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main63 var4 var3 var2 var1 var0) (= var2 nullAddr))) (inv_main64 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Int) (var6 Addr) (var7 Int) (var8 Addr) (var9 Addr) (var10 Heap) (var11 Int) (var12 Addr) (var13 Int) (var14 Addr) (var15 Addr) (var16 Heap)) (or (not (and (inv_main63 var16 var15 var14 var13 var12) (and (and (= var11 0) (and (and (not (= var14 nullAddr)) (is-O_TSLL (read var16 var14))) (and (and (and (and (and (= var10 var16) (= var9 var15)) (= var8 var14)) (= var7 var13)) (= var6 var12)) (= var5 (data (getTSLL (read var16 var14))))))) (and (and (and (and (and (= var4 var10) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var0 var6)) (or (and (not (= var5 1)) (= var11 1)) (and (= var5 1) (= var11 0))))))) (inv_main64 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Int) (var6 Int) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main29 var9 var8 var7 var6) (and (not (= var5 0)) (and (and (not (= var4 nullAddr)) (is-O_TSLL (read var9 var7))) (and (and (and (and (= var3 var9) (= var2 var8)) (= var1 var7)) (= var0 var6)) (= var4 (next (getTSLL (read var9 var7))))))))) (inv_main42 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Int) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main34 var8 var7 var6 var5) (and (is-O_TSLL (read var8 var6)) (and (and (and (and (= var4 var8) (= var3 var7)) (= var2 var6)) (= var1 var5)) (= var0 (next (getTSLL (read var8 var6)))))))) (inv_main28 var4 var3 var0 var1))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main7 var4 var3 var2 var1) (and (not (= nullAddr var3)) (and (= var0 0) (not (= var1 0)))))) (inv_main28 var4 var3 var3 0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main53 var4 var3 var2 var1 var0) (is-O_TSLL (read var4 var0)))) (inv_main54 (write var4 var0 (O_TSLL (TSLL (next (getTSLL (read var4 var0))) 1))) var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Int) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main13 var8 var7 var6 var5) (and (not (= var4 0)) (and (is-O_TSLL (read var8 var6)) (and (and (and (= var3 (write var8 var6 (O_TSLL (TSLL nullAddr (data (getTSLL (read var8 var6))))))) (= var2 var7)) (= var1 var6)) (= var0 var5)))))) (inv_main20 var3 var2 var1 1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Int) (var4 Int) (var5 Int) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main13 var8 var7 var6 var5) (and (not (= var4 0)) (and (= var3 0) (and (is-O_TSLL (read var8 var6)) (and (and (and (= var2 (write var8 var6 (O_TSLL (TSLL nullAddr (data (getTSLL (read var8 var6))))))) (= var1 var7)) (= var0 var6)) (= var4 var5))))))) (inv_main20 var2 var1 var0 var4))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Int) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main65 var10 var9 var8 var7 var6) (and (is-O_TSLL (read var10 var8)) (and (and (and (and (and (= var5 var10) (= var4 var9)) (= var3 var8)) (= var2 var7)) (= var1 var6)) (= var0 (data (getTSLL (read var10 var8)))))))) (inv_main68 var5 var4 var3 var0 var1))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Int) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main11 var8 var7 var6 var5) (and (is-O_TSLL (read var8 var6)) (and (and (and (and (= var4 var8) (= var3 var7)) (= var2 var6)) (= var1 var5)) (= var0 (next (getTSLL (read var8 var6)))))))) (inv_main13 var4 var3 var0 var1))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main64 var4 var3 var2 var1 var0) (and (not (= var3 nullAddr)) (= var2 nullAddr)))) (inv_main101 var4 var3 var3 var1 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Int) (var7 Addr) (var8 Addr) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Int) (var13 Addr) (var14 Addr) (var15 Heap)) (or (not (and (inv_main101 var15 var14 var13 var12 var11) (and (and (not (= var10 nullAddr)) (and (is-O_TSLL (read var15 var13)) (and (and (and (and (and (= var9 var15) (= var8 var14)) (= var7 var13)) (= var6 var12)) (= var5 var11)) (= var4 (next (getTSLL (read var15 var13))))))) (and (and (and (and (= var3 (write var9 var8 defObj)) (= var2 var8)) (= var10 var4)) (= var1 var6)) (= var0 var5))))) (inv_main101 var3 var10 var10 var1 var0))))
(assert (forall ((var0 TSLL) (var1 Int) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main7 var5 var4 var3 var2) (or (not (= var1 0)) (= var2 0)))) (inv_main12 (newHeap (alloc var5 (O_TSLL var0))) var4 var3 var2 (newAddr (alloc var5 (O_TSLL var0)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Int) (var6 Addr) (var7 Addr) (var8 Heap) (var9 Int) (var10 Addr) (var11 Int) (var12 Addr) (var13 Addr) (var14 Heap)) (or (not (and (inv_main31 var14 var13 var12 var11 var10) (and (and (not (= var9 0)) (and (and (and (not (= var10 nullAddr)) (is-O_TSLL (read var14 var12))) (is-O_TSLL (read var14 (next (getTSLL (read var14 var12)))))) (and (and (and (and (= var8 var14) (= var7 var13)) (= var6 var12)) (= var5 var11)) (= var4 (data (getTSLL (read var14 (next (getTSLL (read var14 var12)))))))))) (and (and (and (and (= var3 var8) (= var2 var7)) (= var1 var6)) (= var0 var5)) (or (and (= var4 0) (= var9 1)) (and (not (= var4 0)) (= var9 0))))))) (inv_main30 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Int) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main46 var8 var7 var6 var5) (and (and (not (= var4 1)) (is-O_TSLL (read var8 var6))) (and (and (and (and (= var3 var8) (= var2 var7)) (= var1 var6)) (= var0 var5)) (= var4 (data (getTSLL (read var8 var6)))))))) (inv_main49 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Int) (var6 Addr) (var7 Int) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main84 var10 var9 var8 var7 var6) (and (and (not (= var5 1)) (is-O_TSLL (read var10 var8))) (and (and (and (and (and (= var4 var10) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var0 var6)) (= var5 (data (getTSLL (read var10 var8)))))))) (inv_main88 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Int) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main55 var10 var9 var8 var7 var6) (and (and (= var5 nullAddr) (is-O_TSLL (read var10 var8))) (and (and (and (and (and (= var4 var10) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var0 var6)) (= var5 (next (getTSLL (read var10 var8)))))))) (inv_main57 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Int) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main76 var10 var9 var8 var7 var6) (and (is-O_TSLL (read var10 var8)) (and (and (and (and (and (= var5 var10) (= var4 var9)) (= var3 var8)) (= var2 var7)) (= var1 var6)) (= var0 (next (getTSLL (read var10 var8)))))))) (inv_main63 var5 var4 var0 var2 var1))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Int) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main57 var9 var8 var7 var6 var5) (and (is-O_TSLL (read var9 var7)) (and (and (and (and (= var4 (write var9 var7 (O_TSLL (TSLL var5 (data (getTSLL (read var9 var7))))))) (= var3 var8)) (= var2 var7)) (= var1 var6)) (= var0 var5))))) (inv_main63 var4 var3 var3 0 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Int) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main60 var9 var8 var7 var6 var5) (and (is-O_TSLL (read var9 var7)) (and (and (and (and (= var4 (write var9 var7 (O_TSLL (TSLL var5 (data (getTSLL (read var9 var7))))))) (= var3 var8)) (= var2 var7)) (= var1 var6)) (= var0 var5))))) (inv_main63 var4 var3 var3 0 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main28 var3 var2 var1 var0) (is-O_TSLL (read var3 var1)))) (inv_main31 var3 var2 var1 var0 (next (getTSLL (read var3 var1)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Int) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main30 var8 var7 var6 var5) (and (and (= var4 0) (is-O_TSLL (read var8 var6))) (and (and (and (and (= var3 var8) (= var2 var7)) (= var1 var6)) (= var0 var5)) (= var4 (data (getTSLL (read var8 var6)))))))) (inv_main34 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Int) (var6 Addr) (var7 Int) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main84 var10 var9 var8 var7 var6) (and (= var5 1) (and (and (= var4 1) (is-O_TSLL (read var10 var8))) (and (and (and (and (and (= var3 var10) (= var2 var9)) (= var1 var8)) (= var5 var7)) (= var0 var6)) (= var4 (data (getTSLL (read var10 var8))))))))) (inv_main92 var3 var2 var1 var5 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main54 var4 var3 var2 var1 var0) (is-O_TSLL (read var4 var0)))) (inv_main55 (write var4 var0 (O_TSLL (TSLL nullAddr (data (getTSLL (read var4 var0)))))) var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main3 var1 var0) (not (is-O_TSLL (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main4 var1 var0) (not (is-O_TSLL (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main12 var4 var3 var2 var1 var0) (not (is-O_TSLL (read var4 var2)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main11 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var1)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main13 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var1)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main20 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var1)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main21 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var1)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (inv_main25 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main28 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var1)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main31 var4 var3 var2 var1 var0) (and (not (= var0 nullAddr)) (not (is-O_TSLL (read var4 var2))))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main31 var4 var3 var2 var1 var0) (and (and (not (= var0 nullAddr)) (is-O_TSLL (read var4 var2))) (not (is-O_TSLL (read var4 (next (getTSLL (read var4 var2)))))))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main30 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var1)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (inv_main36 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main34 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var1)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main29 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var1)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main42 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var1)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main46 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var1)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (inv_main49 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main53 var4 var3 var2 var1 var0) (not (is-O_TSLL (read var4 var0)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main54 var4 var3 var2 var1 var0) (not (is-O_TSLL (read var4 var0)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main55 var4 var3 var2 var1 var0) (not (is-O_TSLL (read var4 var2)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main57 var4 var3 var2 var1 var0) (not (is-O_TSLL (read var4 var2)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main58 var4 var3 var2 var1 var0) (not (is-O_TSLL (read var4 var2)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap)) (not (and (inv_main61 var5 var4 var3 var2 var1 var0) (not (is-O_TSLL (read var5 var1)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main60 var4 var3 var2 var1 var0) (not (is-O_TSLL (read var4 var2)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main63 var4 var3 var2 var1 var0) (and (not (= var2 nullAddr)) (not (is-O_TSLL (read var4 var2))))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main65 var4 var3 var2 var1 var0) (not (is-O_TSLL (read var4 var2)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main68 var4 var3 var2 var1 var0) (not (is-O_TSLL (read var4 var2)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap)) (not (inv_main72 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap)) (not (inv_main78 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main76 var4 var3 var2 var1 var0) (not (is-O_TSLL (read var4 var2)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main83 var4 var3 var2 var1 var0) (not (is-O_TSLL (read var4 var2)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main84 var4 var3 var2 var1 var0) (not (is-O_TSLL (read var4 var2)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap)) (not (inv_main88 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap)) (not (inv_main94 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main92 var4 var3 var2 var1 var0) (not (is-O_TSLL (read var4 var2)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main101 var4 var3 var2 var1 var0) (not (is-O_TSLL (read var4 var2)))))))
(check-sat)
