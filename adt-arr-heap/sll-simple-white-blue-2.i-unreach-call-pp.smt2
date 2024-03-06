(set-logic HORN)
(set-info :source |
    Benchmark: 
    Output by Princess (http://www.philipp.ruemmer.org/princess.shtml)
|)
(declare-heap Heap Addr HeapObject
 defObj
 ((HeapObject 0) (TSLL 0)) (
  (
   (O_Int (getInt Int))
   (O_UInt (getUInt Int))
   (O_Addr (getAddr Addr))
   (O_AddrRange (getAddrRange AddrRange))
   (O_TSLL (getTSLL TSLL))
   (defObj)
  )
  (
   (TSLL (|TSLL::next| Addr) (|TSLL::data| Int))
  )
))
(declare-fun _Glue29 (Heap Addr Addr Addr HeapObject) Bool)
(declare-fun _Glue24 (Heap Addr Addr HeapObject) Bool)
(declare-fun Inv_Heap_exp_exp (Addr Addr Int) Bool)
(declare-fun _Glue7 (Heap Addr Addr Addr HeapObject) Bool)
(declare-fun _Glue0_exp_exp (Addr Addr Addr Int Addr Heap Addr HeapObject) Bool)
(declare-fun _Glue25_exp_exp (Addr Addr Addr Int Addr Heap Addr HeapObject) Bool)
(declare-fun _Glue32 (Heap Addr Addr HeapObject) Bool)
(declare-fun _Glue22 (Addr Addr Heap HeapObject) Bool)
(declare-fun inv_main_12 (Heap Addr Addr) Bool)
(declare-fun _Glue27 (Addr Addr Addr Addr Heap HeapObject) Bool)
(declare-fun _Glue33 (Addr Addr Heap Addr HeapObject) Bool)
(declare-fun _Glue8 (Addr Addr Addr Heap Addr HeapObject) Bool)
(declare-fun inv_main_23 (Heap Addr) Bool)
(declare-fun _Glue18 (Addr Addr Heap HeapObject) Bool)
(declare-fun _Glue5 (Addr Addr Addr Addr Heap Addr HeapObject) Bool)
(declare-fun _Glue2 (Addr Addr Addr Addr Addr Heap HeapObject) Bool)
(declare-fun _Glue30 (Addr Addr Addr Heap Addr HeapObject) Bool)
(declare-fun _Glue15 (Heap Addr Addr HeapObject) Bool)
(declare-fun _Glue10 (Addr Addr Addr Heap HeapObject) Bool)
(declare-fun _Glue20 (Heap Addr HeapObject) Bool)
(declare-fun _Glue12 (Heap Addr HeapObject) Bool)
(declare-fun inv_main1003_2 (Heap Addr Addr) Bool)
(declare-fun inv_main_20 (Heap Addr) Bool)
(declare-fun _Glue4 (Heap Addr Addr Addr Addr HeapObject) Bool)
(declare-fun _Glue13 (Addr Heap Addr HeapObject) Bool)
(assert (forall ((var0 AllocResHeap) (var1 Int) (var2 Addr) (var3 HeapObject) (var4 TSLL) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main1003_2 var7 var6 var5) (and (and (= (O_TSLL var4) var3) (= (TSLL var2 var1) var4)) (= (alloc var7 var3) var0)))) (Inv_Heap_exp_exp (newAddr var0) var2 var1))))
(assert (forall ((var0 AllocResHeap) (var1 Heap) (var2 HeapObject) (var3 TSLL) (var4 HeapObject) (var5 TSLL) (var6 Addr) (var7 Addr) (var8 Heap) (var9 Int) (var10 Addr) (var11 Addr)) (or (not (and (and (Inv_Heap_exp_exp var11 var10 var9) (inv_main1003_2 var8 var7 var6)) (and (and (and (and (and (and (= (O_TSLL var5) var4) (= (O_TSLL var3) var2)) (= (AllocResHeap var1 var11) var0)) (= (TSLL var10 var9) var5)) (= (read var1 var11) var4)) (valid var1 var11)) (= (alloc var8 var2) var0)))) (_Glue22 var7 var11 var1 var4))))
(assert (forall ((var0 AllocResHeap) (var1 HeapObject) (var2 TSLL) (var3 HeapObject) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main1003_2 var8 var7 var6) (and (and (and (and (= (read var5 var4) var3) (not (valid var5 var4))) (= (O_TSLL var2) var1)) (= (AllocResHeap var5 var4) var0)) (= (alloc var8 var1) var0)))) (_Glue22 var7 var4 var5 var3))))
(assert (forall ((var0 Int) (var1 Addr) (var2 TSLL) (var3 HeapObject) (var4 Heap) (var5 Addr) (var6 Addr)) (or (not (and (_Glue22 var6 var5 var4 var3) (and (and (and (= (getTSLL var3) var2) (= (|TSLL::next| var2) var1)) (valid var4 var5)) (= var0 1)))) (Inv_Heap_exp_exp var5 var1 var0))))
(assert (forall ((var0 TSLL) (var1 Heap) (var2 HeapObject) (var3 TSLL) (var4 Addr) (var5 HeapObject) (var6 TSLL) (var7 HeapObject) (var8 Heap) (var9 Addr) (var10 Int) (var11 Addr) (var12 Addr)) (or (not (and (and (Inv_Heap_exp_exp var12 var11 var10) (_Glue22 var9 var12 var8 var7)) (and (and (and (and (and (and (and (and (= (O_TSLL var6) var5) (= (TSLL var4 1) var3)) (= (O_TSLL var3) var2)) (= (TSLL var11 var10) var6)) (= (read var1 var12) var5)) (valid var1 var12)) (= (getTSLL var7) var0)) (= (|TSLL::next| var0) var4)) (= (write var8 var12 var2) var1)))) (_Glue24 var1 var9 var12 var5))))
(assert (forall ((var0 HeapObject) (var1 TSLL) (var2 Addr) (var3 TSLL) (var4 HeapObject) (var5 Heap) (var6 HeapObject) (var7 Heap) (var8 Addr) (var9 Addr)) (or (not (and (_Glue22 var9 var8 var7 var6) (and (and (and (and (and (and (= (read var5 var8) var4) (not (valid var5 var8))) (= (getTSLL var6) var3)) (= (|TSLL::next| var3) var2)) (= (TSLL var2 1) var1)) (= (O_TSLL var1) var0)) (= (write var7 var8 var0) var5)))) (_Glue24 var5 var9 var8 var4))))
(assert (forall ((var0 Int) (var1 TSLL) (var2 HeapObject) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (_Glue24 var5 var4 var3 var2) (and (and (= (getTSLL var2) var1) (= (|TSLL::data| var1) var0)) (valid var5 var3)))) (Inv_Heap_exp_exp var3 var4 var0))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 TSLL) (var3 Int) (var4 TSLL) (var5 HeapObject) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (_Glue24 var8 var7 var6 var5) (and (and (and (and (= (getTSLL var5) var4) (= (|TSLL::data| var4) var3)) (= (TSLL var7 var3) var2)) (= (O_TSLL var2) var1)) (= (write var8 var6 var1) var0)))) (inv_main_20 var0 var6))))
(assert (forall ((var0 Addr) (var1 HeapObject) (var2 TSLL) (var3 Heap) (var4 Addr) (var5 Addr)) (or (not (and (and (Inv_Heap_exp_exp var5 var4 1) (inv_main_23 var3 var5)) (and (and (and (and (and (= (O_TSLL var2) var1) (= (TSLL var4 1) var2)) (= nullAddr var0)) (= (read var3 var5) var1)) (not (= var5 var0))) (valid var3 var5)))) (inv_main_23 var3 var4))))
(assert (forall ((var0 Addr) (var1 TSLL) (var2 HeapObject) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main_23 var5 var4) (and (and (and (and (and (and (= nullAddr var3) (= (read var5 var4) var2)) (= (getTSLL var2) var1)) (= (|TSLL::data| var1) 1)) (= (|TSLL::next| var1) var0)) (not (= var4 var3))) (not (valid var5 var4))))) (inv_main_23 var5 var0))))
(assert (forall ((var0 AllocResHeap) (var1 Int) (var2 Addr) (var3 HeapObject) (var4 TSLL) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main1003_2 var7 var6 var5) (and (and (= (O_TSLL var4) var3) (= (TSLL var2 var1) var4)) (= (alloc var7 var3) var0)))) (Inv_Heap_exp_exp (newAddr var0) var2 var1))))
(assert (forall ((var0 AllocResHeap) (var1 Addr) (var2 Heap) (var3 HeapObject) (var4 TSLL) (var5 HeapObject) (var6 TSLL) (var7 Addr) (var8 Heap) (var9 Int) (var10 Addr) (var11 Addr)) (or (not (and (and (Inv_Heap_exp_exp var11 var10 var9) (inv_main1003_2 var8 var7 var11)) (and (and (and (and (and (and (= (O_TSLL var6) var5) (= (O_TSLL var4) var3)) (= (AllocResHeap var2 var1) var0)) (= (TSLL var10 var9) var6)) (= (read var2 var11) var5)) (valid var2 var11)) (= (alloc var8 var3) var0)))) (_Glue10 var11 var7 var1 var2 var5))))
(assert (forall ((var0 AllocResHeap) (var1 Addr) (var2 HeapObject) (var3 TSLL) (var4 HeapObject) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main1003_2 var8 var7 var6) (and (and (and (and (= (read var5 var6) var4) (not (valid var5 var6))) (= (O_TSLL var3) var2)) (= (AllocResHeap var5 var1) var0)) (= (alloc var8 var2) var0)))) (_Glue10 var6 var7 var1 var5 var4))))
(assert (forall ((var0 Int) (var1 TSLL) (var2 HeapObject) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr)) (or (not (and (_Glue10 var6 var5 var4 var3 var2) (and (and (= (getTSLL var2) var1) (= (|TSLL::data| var1) var0)) (valid var3 var6)))) (Inv_Heap_exp_exp var6 var4 var0))))
(assert (forall ((var0 TSLL) (var1 Heap) (var2 HeapObject) (var3 TSLL) (var4 Int) (var5 HeapObject) (var6 TSLL) (var7 HeapObject) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Int) (var12 Addr) (var13 Addr)) (or (not (and (and (Inv_Heap_exp_exp var13 var12 var11) (_Glue10 var13 var10 var9 var8 var7)) (and (and (and (and (and (and (and (and (= (O_TSLL var6) var5) (= (TSLL var9 var4) var3)) (= (O_TSLL var3) var2)) (= (TSLL var12 var11) var6)) (= (read var1 var13) var5)) (valid var1 var13)) (= (getTSLL var7) var0)) (= (|TSLL::data| var0) var4)) (= (write var8 var13 var2) var1)))) (_Glue12 var1 var10 var5))))
(assert (forall ((var0 HeapObject) (var1 TSLL) (var2 Int) (var3 TSLL) (var4 HeapObject) (var5 Heap) (var6 HeapObject) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Addr)) (or (not (and (_Glue10 var10 var9 var8 var7 var6) (and (and (and (and (and (and (= (read var5 var10) var4) (not (valid var5 var10))) (= (getTSLL var6) var3)) (= (|TSLL::data| var3) var2)) (= (TSLL var8 var2) var1)) (= (O_TSLL var1) var0)) (= (write var7 var10 var0) var5)))) (_Glue12 var5 var9 var4))))
(assert (forall ((var0 TSLL) (var1 HeapObject) (var2 TSLL) (var3 HeapObject) (var4 Addr) (var5 Heap) (var6 Int) (var7 Addr) (var8 Addr)) (or (not (and (and (Inv_Heap_exp_exp var8 var7 var6) (_Glue12 var5 var4 var3)) (and (and (and (and (and (= (O_TSLL var2) var1) (= (TSLL var7 var6) var2)) (= (getTSLL var3) var0)) (= (|TSLL::next| var0) var8)) (= (read var5 var8) var1)) (valid var5 var8)))) (_Glue13 var4 var5 var8 var1))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 TSLL) (var3 HeapObject) (var4 Addr) (var5 Heap)) (or (not (and (_Glue12 var5 var4 var3) (and (and (and (= (getTSLL var3) var2) (= (|TSLL::next| var2) var1)) (= (read var5 var1) var0)) (not (valid var5 var1))))) (_Glue13 var4 var5 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 TSLL) (var3 HeapObject) (var4 Addr) (var5 Heap) (var6 Addr)) (or (not (and (_Glue13 var6 var5 var4 var3) (and (and (and (= (getTSLL var3) var2) (= (|TSLL::next| var2) var1)) (valid var5 var4)) (= var0 0)))) (Inv_Heap_exp_exp var4 var1 var0))))
(assert (forall ((var0 TSLL) (var1 Heap) (var2 HeapObject) (var3 TSLL) (var4 Addr) (var5 HeapObject) (var6 TSLL) (var7 HeapObject) (var8 Heap) (var9 Addr) (var10 Int) (var11 Addr) (var12 Addr)) (or (not (and (and (Inv_Heap_exp_exp var12 var11 var10) (_Glue13 var9 var8 var12 var7)) (and (and (and (and (and (and (and (and (= (O_TSLL var6) var5) (= (TSLL var4 0) var3)) (= (O_TSLL var3) var2)) (= (TSLL var11 var10) var6)) (= (read var1 var12) var5)) (valid var1 var12)) (= (getTSLL var7) var0)) (= (|TSLL::next| var0) var4)) (= (write var8 var12 var2) var1)))) (_Glue15 var1 var9 var12 var5))))
(assert (forall ((var0 HeapObject) (var1 TSLL) (var2 Addr) (var3 TSLL) (var4 HeapObject) (var5 Heap) (var6 HeapObject) (var7 Addr) (var8 Heap) (var9 Addr)) (or (not (and (_Glue13 var9 var8 var7 var6) (and (and (and (and (and (and (= (read var5 var7) var4) (not (valid var5 var7))) (= (getTSLL var6) var3)) (= (|TSLL::next| var3) var2)) (= (TSLL var2 0) var1)) (= (O_TSLL var1) var0)) (= (write var8 var7 var0) var5)))) (_Glue15 var5 var9 var7 var4))))
(assert (forall ((var0 Addr) (var1 Int) (var2 TSLL) (var3 HeapObject) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (_Glue15 var6 var5 var4 var3) (and (and (and (= (getTSLL var3) var2) (= (|TSLL::data| var2) var1)) (= nullAddr var0)) (valid var6 var4)))) (Inv_Heap_exp_exp var4 var0 var1))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 TSLL) (var3 Addr) (var4 Int) (var5 TSLL) (var6 HeapObject) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (_Glue15 var9 var8 var7 var6) (and (and (and (and (and (= (getTSLL var6) var5) (= (|TSLL::data| var5) var4)) (= nullAddr var3)) (= (TSLL var3 var4) var2)) (= (O_TSLL var2) var1)) (= (write var9 var7 var1) var0)))) (inv_main1003_2 var0 var8 var7))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 HeapObject) (var5 TSLL) (var6 Addr) (var7 Heap) (var8 Int) (var9 Addr) (var10 Addr)) (or (not (and (and (Inv_Heap_exp_exp var10 var9 var8) (inv_main_12 var7 var6 var10)) (and (and (and (and (= (O_TSLL var5) var4) (= (TSLL var9 var8) var5)) (= nullAddr var3)) (= (read var7 var10) var4)) (valid var7 var10)))) (_Glue0_exp_exp var2 var3 var1 var0 var6 var7 var10 var4))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 HeapObject) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main_12 var7 var6 var5) (and (and (= nullAddr var4) (= (read var7 var5) var3)) (not (valid var7 var5))))) (_Glue0_exp_exp var2 var4 var1 var0 var6 var7 var5 var3))))
(assert (forall ((var0 AllocResHeap) (var1 Addr) (var2 TSLL) (var3 HeapObject) (var4 TSLL) (var5 HeapObject) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Int) (var10 Addr) (var11 Addr) (var12 Addr)) (or (not (and (_Glue0_exp_exp var12 var11 var10 var9 var8 var7 var6 var5) (and (and (and (and (and (= (O_TSLL var4) var3) (= (TSLL var10 var9) var4)) (= (getTSLL var5) var2)) (= (|TSLL::next| var2) var1)) (= (alloc var7 var3) var0)) (not (= var1 var11))))) (Inv_Heap_exp_exp (newAddr var0) var10 var9))))
(assert (forall ((var0 Addr) (var1 TSLL) (var2 HeapObject) (var3 TSLL) (var4 AllocResHeap) (var5 Addr) (var6 Heap) (var7 HeapObject) (var8 TSLL) (var9 HeapObject) (var10 Heap) (var11 Addr) (var12 Int) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Int) (var17 Addr) (var18 Addr)) (or (not (and (and (Inv_Heap_exp_exp var18 var17 var16) (_Glue0_exp_exp var15 var14 var13 var12 var11 var10 var18 var9)) (and (and (and (and (and (and (and (and (and (and (= (O_TSLL var8) var7) (= (AllocResHeap var6 var5) var4)) (= (O_TSLL var3) var2)) (= (TSLL var17 var16) var8)) (= (TSLL var13 var12) var3)) (= (read var6 var18) var7)) (valid var6 var18)) (= (getTSLL var9) var1)) (= (|TSLL::next| var1) var0)) (not (= var0 var14))) (= (alloc var10 var2) var4)))) (_Glue2 var0 var15 var11 var18 var5 var6 var7))))
(assert (forall ((var0 Addr) (var1 TSLL) (var2 HeapObject) (var3 HeapObject) (var4 TSLL) (var5 AllocResHeap) (var6 Addr) (var7 Heap) (var8 HeapObject) (var9 Addr) (var10 Heap) (var11 Addr) (var12 Int) (var13 Addr) (var14 Addr) (var15 Addr)) (or (not (and (_Glue0_exp_exp var15 var14 var13 var12 var11 var10 var9 var8) (and (and (and (and (and (and (and (and (= (AllocResHeap var7 var6) var5) (= (O_TSLL var4) var3)) (= (TSLL var13 var12) var4)) (= (read var7 var9) var2)) (not (valid var7 var9))) (= (getTSLL var8) var1)) (= (|TSLL::next| var1) var0)) (not (= var0 var14))) (= (alloc var10 var3) var5)))) (_Glue2 var0 var15 var11 var9 var6 var7 var2))))
(assert (forall ((var0 Int) (var1 TSLL) (var2 HeapObject) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr)) (or (not (and (_Glue2 var8 var7 var6 var5 var4 var3 var2) (and (and (= (getTSLL var2) var1) (= (|TSLL::data| var1) var0)) (valid var3 var5)))) (Inv_Heap_exp_exp var5 var4 var0))))
(assert (forall ((var0 TSLL) (var1 Heap) (var2 HeapObject) (var3 TSLL) (var4 Int) (var5 HeapObject) (var6 TSLL) (var7 HeapObject) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Int) (var14 Addr) (var15 Addr)) (or (not (and (and (Inv_Heap_exp_exp var15 var14 var13) (_Glue2 var12 var11 var10 var15 var9 var8 var7)) (and (and (and (and (and (and (and (and (= (O_TSLL var6) var5) (= (TSLL var9 var4) var3)) (= (O_TSLL var3) var2)) (= (TSLL var14 var13) var6)) (= (read var1 var15) var5)) (valid var1 var15)) (= (getTSLL var7) var0)) (= (|TSLL::data| var0) var4)) (= (write var8 var15 var2) var1)))) (_Glue4 var1 var12 var11 var10 var15 var5))))
(assert (forall ((var0 HeapObject) (var1 TSLL) (var2 Int) (var3 TSLL) (var4 HeapObject) (var5 Heap) (var6 HeapObject) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr)) (or (not (and (_Glue2 var12 var11 var10 var9 var8 var7 var6) (and (and (and (and (and (and (= (read var5 var9) var4) (not (valid var5 var9))) (= (getTSLL var6) var3)) (= (|TSLL::data| var3) var2)) (= (TSLL var8 var2) var1)) (= (O_TSLL var1) var0)) (= (write var7 var9 var0) var5)))) (_Glue4 var5 var12 var11 var10 var9 var4))))
(assert (forall ((var0 TSLL) (var1 HeapObject) (var2 TSLL) (var3 HeapObject) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap) (var9 Int) (var10 Addr) (var11 Addr)) (or (not (and (and (Inv_Heap_exp_exp var11 var10 var9) (_Glue4 var8 var7 var6 var5 var4 var3)) (and (and (and (and (and (= (O_TSLL var2) var1) (= (TSLL var10 var9) var2)) (= (getTSLL var3) var0)) (= (|TSLL::next| var0) var11)) (= (read var8 var11) var1)) (valid var8 var11)))) (_Glue5 var4 var5 var6 var7 var8 var11 var1))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 TSLL) (var3 HeapObject) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (_Glue4 var8 var7 var6 var5 var4 var3) (and (and (and (= (getTSLL var3) var2) (= (|TSLL::next| var2) var1)) (= (read var8 var1) var0)) (not (valid var8 var1))))) (_Glue5 var4 var5 var6 var7 var8 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 TSLL) (var3 HeapObject) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr)) (or (not (and (_Glue5 var9 var8 var7 var6 var5 var4 var3) (and (and (and (= (getTSLL var3) var2) (= (|TSLL::next| var2) var1)) (valid var5 var4)) (= var0 1)))) (Inv_Heap_exp_exp var4 var1 var0))))
(assert (forall ((var0 TSLL) (var1 Heap) (var2 HeapObject) (var3 TSLL) (var4 Addr) (var5 HeapObject) (var6 TSLL) (var7 HeapObject) (var8 Addr) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Int) (var14 Addr) (var15 Addr)) (or (not (and (and (Inv_Heap_exp_exp var15 var14 var13) (_Glue5 var15 var12 var11 var10 var9 var8 var7)) (and (and (and (and (and (and (and (and (= (O_TSLL var6) var5) (= (TSLL var4 1) var3)) (= (O_TSLL var3) var2)) (= (TSLL var14 var13) var6)) (= (read var1 var15) var5)) (valid var1 var15)) (= (getTSLL var7) var0)) (= (|TSLL::next| var0) var4)) (= (write var9 var8 var2) var1)))) (_Glue7 var1 var12 var11 var10 var5))))
(assert (forall ((var0 HeapObject) (var1 TSLL) (var2 Addr) (var3 TSLL) (var4 HeapObject) (var5 Heap) (var6 HeapObject) (var7 Addr) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr)) (or (not (and (_Glue5 var12 var11 var10 var9 var8 var7 var6) (and (and (and (and (and (and (= (read var5 var12) var4) (not (valid var5 var12))) (= (getTSLL var6) var3)) (= (|TSLL::next| var3) var2)) (= (TSLL var2 1) var1)) (= (O_TSLL var1) var0)) (= (write var8 var7 var0) var5)))) (_Glue7 var5 var11 var10 var9 var4))))
(assert (forall ((var0 TSLL) (var1 HeapObject) (var2 TSLL) (var3 HeapObject) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Int) (var9 Addr) (var10 Addr)) (or (not (and (and (Inv_Heap_exp_exp var10 var9 var8) (_Glue7 var7 var6 var5 var4 var3)) (and (and (and (and (and (= (O_TSLL var2) var1) (= (TSLL var9 var8) var2)) (= (getTSLL var3) var0)) (= (|TSLL::next| var0) var10)) (= (read var7 var10) var1)) (valid var7 var10)))) (_Glue8 var4 var5 var6 var7 var10 var1))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 TSLL) (var3 HeapObject) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (_Glue7 var7 var6 var5 var4 var3) (and (and (and (= (getTSLL var3) var2) (= (|TSLL::next| var2) var1)) (= (read var7 var1) var0)) (not (valid var7 var1))))) (_Glue8 var4 var5 var6 var7 var1 var0))))
(assert (forall ((var0 Int) (var1 TSLL) (var2 HeapObject) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr)) (or (not (and (_Glue8 var6 var5 var5 var4 var3 var2) (and (and (= (getTSLL var2) var1) (= (|TSLL::data| var1) var0)) (valid var4 var3)))) (Inv_Heap_exp_exp var3 var6 var0))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 TSLL) (var3 Int) (var4 TSLL) (var5 HeapObject) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Addr)) (or (not (and (_Glue8 var9 var8 var8 var7 var6 var5) (and (and (and (and (= (getTSLL var5) var4) (= (|TSLL::data| var4) var3)) (= (TSLL var9 var3) var2)) (= (O_TSLL var2) var1)) (= (write var7 var6 var1) var0)))) (inv_main_20 var0 var8))))
(assert (forall ((var0 HeapObject) (var1 TSLL) (var2 Heap) (var3 Addr) (var4 Addr)) (or (not (and (and (Inv_Heap_exp_exp var4 var3 1) (inv_main_20 var2 var4)) (and (and (and (= (O_TSLL var1) var0) (= (TSLL var3 1) var1)) (= (read var2 var4) var0)) (valid var2 var4)))) (inv_main_23 var2 var3))))
(assert (forall ((var0 Addr) (var1 TSLL) (var2 HeapObject) (var3 Addr) (var4 Heap)) (or (not (and (inv_main_20 var4 var3) (and (and (and (and (= (read var4 var3) var2) (= (getTSLL var2) var1)) (= (|TSLL::data| var1) 1)) (= (|TSLL::next| var1) var0)) (not (valid var4 var3))))) (inv_main_23 var4 var0))))
(assert (forall ((var0 Addr) (var1 HeapObject) (var2 TSLL) (var3 Addr) (var4 Heap) (var5 Int) (var6 Addr) (var7 Addr)) (or (not (and (and (Inv_Heap_exp_exp var7 var6 var5) (inv_main_12 var4 var3 var7)) (and (and (and (and (and (= (O_TSLL var2) var1) (= (TSLL var6 var5) var2)) (not (= var6 var0))) (= (read var4 var7) var1)) (= nullAddr var0)) (valid var4 var7)))) (inv_main_12 var4 var3 var6))))
(assert (forall ((var0 TSLL) (var1 HeapObject) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main_12 var6 var5 var4) (and (and (and (and (and (not (= var3 var2)) (= (read var6 var4) var1)) (= (getTSLL var1) var0)) (= (|TSLL::next| var0) var3)) (= nullAddr var2)) (not (valid var6 var4))))) (inv_main_12 var6 var5 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main1003_2 var3 var2 var1) (= var0 var2))) (inv_main_12 var3 var0 var2))))
(assert (forall ((var0 Addr) (var1 HeapObject) (var2 TSLL) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr)) (not (and (and (Inv_Heap_exp_exp var6 var5 var4) (inv_main_23 var3 var6)) (and (and (and (and (and (and (= (O_TSLL var2) var1) (= (TSLL var5 var4) var2)) (not (= var6 var0))) (not (= var4 1))) (= nullAddr var0)) (= (read var3 var6) var1)) (valid var3 var6))))))
(assert (forall ((var0 TSLL) (var1 HeapObject) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap)) (not (and (inv_main_23 var5 var4) (and (and (and (and (and (and (not (= var4 var3)) (not (= var2 1))) (= nullAddr var3)) (= (read var5 var4) var1)) (= (getTSLL var1) var0)) (= (|TSLL::data| var0) var2)) (not (valid var5 var4)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 HeapObject) (var5 TSLL) (var6 Addr) (var7 Heap) (var8 Int) (var9 Addr) (var10 Addr)) (or (not (and (and (Inv_Heap_exp_exp var10 var9 var8) (inv_main_12 var7 var6 var10)) (and (and (and (= (O_TSLL var5) var4) (= (TSLL var9 var8) var5)) (= (read var7 var10) var4)) (valid var7 var10)))) (_Glue25_exp_exp var3 var2 var1 var0 var6 var7 var10 var4))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 HeapObject) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main_12 var7 var6 var5) (and (= (read var7 var5) var4) (not (valid var7 var5))))) (_Glue25_exp_exp var3 var2 var1 var0 var6 var7 var5 var4))))
(assert (forall ((var0 AllocResHeap) (var1 TSLL) (var2 HeapObject) (var3 TSLL) (var4 HeapObject) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Int) (var9 Addr) (var10 Addr) (var11 Addr)) (or (not (and (_Glue25_exp_exp var11 var10 var9 var8 var7 var6 var5 var4) (and (and (and (and (and (= (O_TSLL var3) var2) (= (TSLL var9 var8) var3)) (= nullAddr var10)) (= (getTSLL var4) var1)) (= (|TSLL::next| var1) var10)) (= (alloc var6 var2) var0)))) (Inv_Heap_exp_exp (newAddr var0) var9 var8))))
(assert (forall ((var0 TSLL) (var1 HeapObject) (var2 TSLL) (var3 AllocResHeap) (var4 Addr) (var5 Heap) (var6 HeapObject) (var7 TSLL) (var8 HeapObject) (var9 Heap) (var10 Addr) (var11 Int) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Int) (var16 Addr) (var17 Addr)) (or (not (and (and (Inv_Heap_exp_exp var17 var16 var15) (_Glue25_exp_exp var14 var13 var12 var11 var10 var9 var17 var8)) (and (and (and (and (and (and (and (and (and (and (= (O_TSLL var7) var6) (= (AllocResHeap var5 var4) var3)) (= (O_TSLL var2) var1)) (= (TSLL var16 var15) var7)) (= (TSLL var12 var11) var2)) (= (read var5 var17) var6)) (valid var5 var17)) (= nullAddr var13)) (= (getTSLL var8) var0)) (= (|TSLL::next| var0) var13)) (= (alloc var9 var1) var3)))) (_Glue27 var14 var10 var17 var4 var5 var6))))
(assert (forall ((var0 TSLL) (var1 HeapObject) (var2 HeapObject) (var3 TSLL) (var4 AllocResHeap) (var5 Addr) (var6 Heap) (var7 HeapObject) (var8 Addr) (var9 Heap) (var10 Addr) (var11 Int) (var12 Addr) (var13 Addr) (var14 Addr)) (or (not (and (_Glue25_exp_exp var14 var13 var12 var11 var10 var9 var8 var7) (and (and (and (and (and (and (and (and (= (AllocResHeap var6 var5) var4) (= (O_TSLL var3) var2)) (= (TSLL var12 var11) var3)) (= (read var6 var8) var1)) (not (valid var6 var8))) (= nullAddr var13)) (= (getTSLL var7) var0)) (= (|TSLL::next| var0) var13)) (= (alloc var9 var2) var4)))) (_Glue27 var14 var10 var8 var5 var6 var1))))
(assert (forall ((var0 Int) (var1 TSLL) (var2 HeapObject) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr)) (or (not (and (_Glue27 var7 var6 var5 var4 var3 var2) (and (and (= (getTSLL var2) var1) (= (|TSLL::data| var1) var0)) (valid var3 var5)))) (Inv_Heap_exp_exp var5 var4 var0))))
(assert (forall ((var0 TSLL) (var1 Heap) (var2 HeapObject) (var3 TSLL) (var4 Int) (var5 HeapObject) (var6 TSLL) (var7 HeapObject) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Int) (var13 Addr) (var14 Addr)) (or (not (and (and (Inv_Heap_exp_exp var14 var13 var12) (_Glue27 var11 var10 var14 var9 var8 var7)) (and (and (and (and (and (and (and (and (= (O_TSLL var6) var5) (= (TSLL var9 var4) var3)) (= (O_TSLL var3) var2)) (= (TSLL var13 var12) var6)) (= (read var1 var14) var5)) (valid var1 var14)) (= (getTSLL var7) var0)) (= (|TSLL::data| var0) var4)) (= (write var8 var14 var2) var1)))) (_Glue29 var1 var11 var10 var14 var5))))
(assert (forall ((var0 HeapObject) (var1 TSLL) (var2 Int) (var3 TSLL) (var4 HeapObject) (var5 Heap) (var6 HeapObject) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr)) (or (not (and (_Glue27 var11 var10 var9 var8 var7 var6) (and (and (and (and (and (and (= (read var5 var9) var4) (not (valid var5 var9))) (= (getTSLL var6) var3)) (= (|TSLL::data| var3) var2)) (= (TSLL var8 var2) var1)) (= (O_TSLL var1) var0)) (= (write var7 var9 var0) var5)))) (_Glue29 var5 var11 var10 var9 var4))))
(assert (forall ((var0 TSLL) (var1 HeapObject) (var2 TSLL) (var3 HeapObject) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Int) (var9 Addr) (var10 Addr)) (or (not (and (and (Inv_Heap_exp_exp var10 var9 var8) (_Glue29 var7 var6 var5 var4 var3)) (and (and (and (and (and (= (O_TSLL var2) var1) (= (TSLL var9 var8) var2)) (= (getTSLL var3) var0)) (= (|TSLL::next| var0) var10)) (= (read var7 var10) var1)) (valid var7 var10)))) (_Glue30 var4 var5 var6 var7 var10 var1))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 TSLL) (var3 HeapObject) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (_Glue29 var7 var6 var5 var4 var3) (and (and (and (= (getTSLL var3) var2) (= (|TSLL::next| var2) var1)) (= (read var7 var1) var0)) (not (valid var7 var1))))) (_Glue30 var4 var5 var6 var7 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 TSLL) (var3 HeapObject) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr)) (or (not (and (_Glue30 var8 var7 var6 var5 var4 var3) (and (and (and (= (getTSLL var3) var2) (= (|TSLL::next| var2) var1)) (valid var5 var4)) (= var0 1)))) (Inv_Heap_exp_exp var4 var1 var0))))
(assert (forall ((var0 TSLL) (var1 Heap) (var2 HeapObject) (var3 TSLL) (var4 Addr) (var5 HeapObject) (var6 TSLL) (var7 HeapObject) (var8 Addr) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Int) (var13 Addr) (var14 Addr)) (or (not (and (and (Inv_Heap_exp_exp var14 var13 var12) (_Glue30 var14 var11 var10 var9 var8 var7)) (and (and (and (and (and (and (and (and (= (O_TSLL var6) var5) (= (TSLL var4 1) var3)) (= (O_TSLL var3) var2)) (= (TSLL var13 var12) var6)) (= (read var1 var14) var5)) (valid var1 var14)) (= (getTSLL var7) var0)) (= (|TSLL::next| var0) var4)) (= (write var9 var8 var2) var1)))) (_Glue32 var1 var11 var10 var5))))
(assert (forall ((var0 HeapObject) (var1 TSLL) (var2 Addr) (var3 TSLL) (var4 HeapObject) (var5 Heap) (var6 HeapObject) (var7 Addr) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Addr)) (or (not (and (_Glue30 var11 var10 var9 var8 var7 var6) (and (and (and (and (and (and (= (read var5 var11) var4) (not (valid var5 var11))) (= (getTSLL var6) var3)) (= (|TSLL::next| var3) var2)) (= (TSLL var2 1) var1)) (= (O_TSLL var1) var0)) (= (write var8 var7 var0) var5)))) (_Glue32 var5 var10 var9 var4))))
(assert (forall ((var0 TSLL) (var1 HeapObject) (var2 TSLL) (var3 HeapObject) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Int) (var8 Addr) (var9 Addr)) (or (not (and (and (Inv_Heap_exp_exp var9 var8 var7) (_Glue32 var6 var5 var4 var3)) (and (and (and (and (and (= (O_TSLL var2) var1) (= (TSLL var8 var7) var2)) (= (getTSLL var3) var0)) (= (|TSLL::next| var0) var9)) (= (read var6 var9) var1)) (valid var6 var9)))) (_Glue33 var4 var5 var6 var9 var1))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 TSLL) (var3 HeapObject) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (_Glue32 var6 var5 var4 var3) (and (and (and (= (getTSLL var3) var2) (= (|TSLL::next| var2) var1)) (= (read var6 var1) var0)) (not (valid var6 var1))))) (_Glue33 var4 var5 var6 var1 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 TSLL) (var3 HeapObject) (var4 Addr) (var5 Heap) (var6 Addr)) (or (not (and (_Glue33 var6 var6 var5 var4 var3) (and (and (and (= (getTSLL var3) var2) (= (|TSLL::data| var2) var1)) (= nullAddr var0)) (valid var5 var4)))) (Inv_Heap_exp_exp var4 var0 var1))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 TSLL) (var3 Addr) (var4 Int) (var5 TSLL) (var6 HeapObject) (var7 Addr) (var8 Heap) (var9 Addr)) (or (not (and (_Glue33 var9 var9 var8 var7 var6) (and (and (and (and (and (= (getTSLL var6) var5) (= (|TSLL::data| var5) var4)) (= nullAddr var3)) (= (TSLL var3 var4) var2)) (= (O_TSLL var2) var1)) (= (write var8 var7 var1) var0)))) (inv_main_20 var0 var9))))
(assert (forall ((var0 HeapObject) (var1 TSLL) (var2 Heap) (var3 Int) (var4 Addr) (var5 Addr)) (or (not (and (and (Inv_Heap_exp_exp var5 var4 var3) (inv_main_20 var2 var5)) (and (and (and (and (= (O_TSLL var1) var0) (= (TSLL var4 var3) var1)) (= (read var2 var5) var0)) (not (= var3 1))) (valid var2 var5)))) (inv_main_20 var2 var4))))
(assert (forall ((var0 Addr) (var1 Int) (var2 TSLL) (var3 HeapObject) (var4 Addr) (var5 Heap)) (or (not (and (inv_main_20 var5 var4) (and (and (and (and (and (= (read var5 var4) var3) (= (getTSLL var3) var2)) (= (|TSLL::data| var2) var1)) (= (|TSLL::next| var2) var0)) (not (= var1 1))) (not (valid var5 var4))))) (inv_main_20 var5 var0))))
(assert (forall ((var0 AllocResHeap) (var1 Heap) (var2 Int) (var3 Addr) (var4 HeapObject) (var5 TSLL)) (or (not (and (and (and (= (O_TSLL var5) var4) (= (TSLL var3 var2) var5)) (= (alloc var1 var4) var0)) (= emptyHeap var1))) (Inv_Heap_exp_exp (newAddr var0) var3 var2))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 HeapObject) (var3 TSLL) (var4 AllocResHeap) (var5 Heap) (var6 HeapObject) (var7 TSLL) (var8 Int) (var9 Addr) (var10 Addr)) (or (not (and (Inv_Heap_exp_exp var10 var9 var8) (and (and (and (and (and (and (and (and (= (O_TSLL var7) var6) (= (AllocResHeap var5 var10) var4)) (= (O_TSLL var3) var2)) (= (TSLL var9 var8) var7)) (= (read var5 var10) var6)) (valid var5 var10)) (= (alloc var1 var2) var4)) (= nullAddr var0)) (= emptyHeap var1)))) (_Glue18 var10 var0 var5 var6))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 HeapObject) (var3 TSLL) (var4 AllocResHeap) (var5 HeapObject) (var6 Addr) (var7 Heap)) (or (not (and (and (and (and (and (and (= (read var7 var6) var5) (not (valid var7 var6))) (= (AllocResHeap var7 var6) var4)) (= (O_TSLL var3) var2)) (= (alloc var1 var2) var4)) (= nullAddr var0)) (= emptyHeap var1))) (_Glue18 var6 var0 var7 var5))))
(assert (forall ((var0 Int) (var1 TSLL) (var2 HeapObject) (var3 Heap) (var4 Addr) (var5 Addr)) (or (not (and (_Glue18 var5 var4 var3 var2) (and (and (= (getTSLL var2) var1) (= (|TSLL::data| var1) var0)) (valid var3 var5)))) (Inv_Heap_exp_exp var5 var4 var0))))
(assert (forall ((var0 TSLL) (var1 Heap) (var2 HeapObject) (var3 TSLL) (var4 Int) (var5 HeapObject) (var6 TSLL) (var7 HeapObject) (var8 Heap) (var9 Addr) (var10 Int) (var11 Addr) (var12 Addr)) (or (not (and (and (Inv_Heap_exp_exp var12 var11 var10) (_Glue18 var12 var9 var8 var7)) (and (and (and (and (and (and (and (and (= (O_TSLL var6) var5) (= (TSLL var9 var4) var3)) (= (O_TSLL var3) var2)) (= (TSLL var11 var10) var6)) (= (read var1 var12) var5)) (valid var1 var12)) (= (getTSLL var7) var0)) (= (|TSLL::data| var0) var4)) (= (write var8 var12 var2) var1)))) (_Glue20 var1 var12 var5))))
(assert (forall ((var0 HeapObject) (var1 TSLL) (var2 Int) (var3 TSLL) (var4 HeapObject) (var5 Heap) (var6 HeapObject) (var7 Heap) (var8 Addr) (var9 Addr)) (or (not (and (_Glue18 var9 var8 var7 var6) (and (and (and (and (and (and (= (read var5 var9) var4) (not (valid var5 var9))) (= (getTSLL var6) var3)) (= (|TSLL::data| var3) var2)) (= (TSLL var8 var2) var1)) (= (O_TSLL var1) var0)) (= (write var7 var9 var0) var5)))) (_Glue20 var5 var9 var4))))
(assert (forall ((var0 Int) (var1 Addr) (var2 TSLL) (var3 HeapObject) (var4 Addr) (var5 Heap)) (or (not (and (_Glue20 var5 var4 var3) (and (and (and (= (getTSLL var3) var2) (= (|TSLL::next| var2) var1)) (valid var5 var4)) (= var0 0)))) (Inv_Heap_exp_exp var4 var1 var0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 HeapObject) (var3 TSLL) (var4 Addr) (var5 TSLL) (var6 HeapObject) (var7 Addr) (var8 Heap)) (or (not (and (_Glue20 var8 var7 var6) (and (and (and (and (and (= (getTSLL var6) var5) (= (|TSLL::next| var5) var4)) (= (TSLL var4 0) var3)) (= (O_TSLL var3) var2)) (= (write var8 var7 var2) var1)) (= var0 var7)))) (inv_main1003_2 var1 var7 var0))))
(check-sat)
