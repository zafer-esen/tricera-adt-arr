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
   (TSLL (|TSLL::next| Addr) (|TSLL::colour| Int))
  )
))
(declare-fun _Glue16 (Addr Addr Addr Heap HeapObject) Bool)
(declare-fun _Glue6_exp_exp (Heap Addr Addr Int Addr Addr HeapObject) Bool)
(declare-fun _Glue24 (Addr Addr Heap HeapObject) Bool)
(declare-fun _Glue9 (Addr Addr Addr Addr Heap HeapObject) Bool)
(declare-fun _Glue1_exp_exp (Addr Addr Addr Int Addr Heap HeapObject) Bool)
(declare-fun _Glue19 (Addr Heap Addr HeapObject) Bool)
(declare-fun _Glue26 (Heap Addr HeapObject) Bool)
(declare-fun _Glue11 (Heap Addr Addr HeapObject) Bool)
(declare-fun _Glue12 (Addr Addr Heap Addr HeapObject) Bool)
(declare-fun _Glue3_exp_exp (Heap Addr Addr Int HeapObject) Bool)
(declare-fun inv_main_17 (Heap Addr) Bool)
(declare-fun inv_main1049_12 () Bool)
(declare-fun _Glue29 (Addr Heap HeapObject) Bool)
(declare-fun _Glue30 (Heap Addr HeapObject) Bool)
(declare-fun _Glue28 (Heap Addr HeapObject) Bool)
(declare-fun _Glue21 (Heap Addr Addr HeapObject) Bool)
(declare-fun inv_main1010_2 (Heap Addr Addr) Bool)
(declare-fun _Glue27 (Addr Heap HeapObject) Bool)
(declare-fun _Glue18 (Heap Addr HeapObject) Bool)
(declare-fun _Glue14 (Heap Addr Addr HeapObject) Bool)
(declare-fun Inv_Heap_exp_exp (Addr Addr Int) Bool)
(declare-fun _Glue4_exp_exp (Addr Int Addr Heap Addr HeapObject) Bool)
(assert (forall ((var0 Addr) (var1 HeapObject) (var2 TSLL) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr)) (or (not (and (and (Inv_Heap_exp_exp var6 var5 var4) (inv_main_17 var3 var6)) (and (and (and (and (and (= (O_TSLL var2) var1) (= (TSLL var5 var4) var2)) (= nullAddr var0)) (not (= var0 var6))) (= (read var3 var6) var1)) (valid var3 var6)))) (_Glue27 var0 var3 var1))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main_17 var3 var2) (and (and (and (= nullAddr var1) (not (= var1 var2))) (= (read var3 var2) var0)) (not (valid var3 var2))))) (_Glue27 var1 var3 var0))))
(assert (forall ((var0 TSLL) (var1 HeapObject) (var2 TSLL) (var3 HeapObject) (var4 Heap) (var5 Addr) (var6 Int) (var7 Addr) (var8 Addr)) (or (not (and (and (Inv_Heap_exp_exp var8 var7 var6) (_Glue27 var5 var4 var3)) (and (and (and (and (and (and (= (O_TSLL var2) var1) (= (TSLL var7 var6) var2)) (= (getTSLL var3) var0)) (= (|TSLL::colour| var0) 0)) (= (|TSLL::next| var0) var8)) (= (read var4 var8) var1)) (valid var4 var8)))) (_Glue28 var4 var5 var1))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 TSLL) (var3 HeapObject) (var4 Heap) (var5 Addr)) (or (not (and (_Glue27 var5 var4 var3) (and (and (and (and (= (getTSLL var3) var2) (= (|TSLL::colour| var2) 0)) (= (|TSLL::next| var2) var1)) (= (read var4 var1) var0)) (not (valid var4 var1))))) (_Glue28 var4 var5 var0))))
(assert (forall ((var0 TSLL) (var1 HeapObject) (var2 TSLL) (var3 HeapObject) (var4 Heap) (var5 Int) (var6 Addr) (var7 Addr)) (or (not (and (and (Inv_Heap_exp_exp var7 var6 var5) (_Glue28 var4 var6 var3)) (and (and (and (and (and (= (O_TSLL var2) var1) (= (TSLL var6 var5) var2)) (= (getTSLL var3) var0)) (= (|TSLL::next| var0) var7)) (= (read var4 var7) var1)) (valid var4 var7)))) inv_main1049_12)))
(assert (forall ((var0 TSLL) (var1 HeapObject) (var2 Addr) (var3 TSLL) (var4 HeapObject) (var5 Addr) (var6 Heap)) (or (not (and (_Glue28 var6 var5 var4) (and (and (and (and (and (= (getTSLL var4) var3) (= (|TSLL::next| var3) var2)) (= (read var6 var2) var1)) (= (getTSLL var1) var0)) (= (|TSLL::next| var0) var5)) (not (valid var6 var2))))) inv_main1049_12)))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main1010_2 var2 var1 var0) (= nullAddr var1)))))
(assert (forall ((var0 AllocResHeap) (var1 Int) (var2 Addr) (var3 HeapObject) (var4 TSLL) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main1010_2 var7 var6 var5) (and (and (= (O_TSLL var4) var3) (= (TSLL var2 var1) var4)) (= (alloc var7 var3) var0)))) (Inv_Heap_exp_exp (newAddr var0) var2 var1))))
(assert (forall ((var0 AllocResHeap) (var1 Addr) (var2 Heap) (var3 HeapObject) (var4 TSLL) (var5 HeapObject) (var6 TSLL) (var7 Addr) (var8 Heap) (var9 Int) (var10 Addr) (var11 Addr)) (or (not (and (and (Inv_Heap_exp_exp var11 var10 var9) (inv_main1010_2 var8 var7 var11)) (and (and (and (and (and (and (= (O_TSLL var6) var5) (= (O_TSLL var4) var3)) (= (AllocResHeap var2 var1) var0)) (= (TSLL var10 var9) var6)) (= (read var2 var11) var5)) (valid var2 var11)) (= (alloc var8 var3) var0)))) (_Glue16 var11 var7 var1 var2 var5))))
(assert (forall ((var0 AllocResHeap) (var1 Addr) (var2 HeapObject) (var3 TSLL) (var4 HeapObject) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main1010_2 var8 var7 var6) (and (and (and (and (= (read var5 var6) var4) (not (valid var5 var6))) (= (O_TSLL var3) var2)) (= (AllocResHeap var5 var1) var0)) (= (alloc var8 var2) var0)))) (_Glue16 var6 var7 var1 var5 var4))))
(assert (forall ((var0 Int) (var1 TSLL) (var2 HeapObject) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr)) (or (not (and (_Glue16 var6 var5 var4 var3 var2) (and (and (= (getTSLL var2) var1) (= (|TSLL::colour| var1) var0)) (valid var3 var6)))) (Inv_Heap_exp_exp var6 var4 var0))))
(assert (forall ((var0 TSLL) (var1 Heap) (var2 HeapObject) (var3 TSLL) (var4 Int) (var5 HeapObject) (var6 TSLL) (var7 HeapObject) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Int) (var12 Addr) (var13 Addr)) (or (not (and (and (Inv_Heap_exp_exp var13 var12 var11) (_Glue16 var13 var10 var9 var8 var7)) (and (and (and (and (and (and (and (and (= (O_TSLL var6) var5) (= (TSLL var9 var4) var3)) (= (O_TSLL var3) var2)) (= (TSLL var12 var11) var6)) (= (read var1 var13) var5)) (valid var1 var13)) (= (getTSLL var7) var0)) (= (|TSLL::colour| var0) var4)) (= (write var8 var13 var2) var1)))) (_Glue18 var1 var10 var5))))
(assert (forall ((var0 HeapObject) (var1 TSLL) (var2 Int) (var3 TSLL) (var4 HeapObject) (var5 Heap) (var6 HeapObject) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Addr)) (or (not (and (_Glue16 var10 var9 var8 var7 var6) (and (and (and (and (and (and (= (read var5 var10) var4) (not (valid var5 var10))) (= (getTSLL var6) var3)) (= (|TSLL::colour| var3) var2)) (= (TSLL var8 var2) var1)) (= (O_TSLL var1) var0)) (= (write var7 var10 var0) var5)))) (_Glue18 var5 var9 var4))))
(assert (forall ((var0 TSLL) (var1 HeapObject) (var2 TSLL) (var3 HeapObject) (var4 Addr) (var5 Heap) (var6 Int) (var7 Addr) (var8 Addr)) (or (not (and (and (Inv_Heap_exp_exp var8 var7 var6) (_Glue18 var5 var4 var3)) (and (and (and (and (and (= (O_TSLL var2) var1) (= (TSLL var7 var6) var2)) (= (getTSLL var3) var0)) (= (|TSLL::next| var0) var8)) (= (read var5 var8) var1)) (valid var5 var8)))) (_Glue19 var4 var5 var8 var1))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 TSLL) (var3 HeapObject) (var4 Addr) (var5 Heap)) (or (not (and (_Glue18 var5 var4 var3) (and (and (and (= (getTSLL var3) var2) (= (|TSLL::next| var2) var1)) (= (read var5 var1) var0)) (not (valid var5 var1))))) (_Glue19 var4 var5 var1 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 TSLL) (var3 HeapObject) (var4 Addr) (var5 Heap) (var6 Addr)) (or (not (and (_Glue19 var6 var5 var4 var3) (and (and (and (= (getTSLL var3) var2) (= (|TSLL::colour| var2) var1)) (= nullAddr var0)) (valid var5 var4)))) (Inv_Heap_exp_exp var4 var0 var1))))
(assert (forall ((var0 TSLL) (var1 Heap) (var2 HeapObject) (var3 TSLL) (var4 Int) (var5 Addr) (var6 HeapObject) (var7 TSLL) (var8 HeapObject) (var9 Heap) (var10 Addr) (var11 Int) (var12 Addr) (var13 Addr)) (or (not (and (and (Inv_Heap_exp_exp var13 var12 var11) (_Glue19 var10 var9 var13 var8)) (and (and (and (and (and (and (and (and (and (= (O_TSLL var7) var6) (= (TSLL var5 var4) var3)) (= (O_TSLL var3) var2)) (= (TSLL var12 var11) var7)) (= (read var1 var13) var6)) (valid var1 var13)) (= (getTSLL var8) var0)) (= (|TSLL::colour| var0) var4)) (= nullAddr var5)) (= (write var9 var13 var2) var1)))) (_Glue21 var1 var10 var13 var6))))
(assert (forall ((var0 HeapObject) (var1 TSLL) (var2 Addr) (var3 Int) (var4 TSLL) (var5 HeapObject) (var6 Heap) (var7 HeapObject) (var8 Addr) (var9 Heap) (var10 Addr)) (or (not (and (_Glue19 var10 var9 var8 var7) (and (and (and (and (and (and (and (= (read var6 var8) var5) (not (valid var6 var8))) (= (getTSLL var7) var4)) (= (|TSLL::colour| var4) var3)) (= nullAddr var2)) (= (TSLL var2 var3) var1)) (= (O_TSLL var1) var0)) (= (write var9 var8 var0) var6)))) (_Glue21 var6 var10 var8 var5))))
(assert (forall ((var0 Int) (var1 Addr) (var2 TSLL) (var3 HeapObject) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (_Glue21 var6 var5 var4 var3) (and (and (and (= (getTSLL var3) var2) (= (|TSLL::next| var2) var1)) (valid var6 var4)) (= var0 1)))) (Inv_Heap_exp_exp var4 var1 var0))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 TSLL) (var3 Addr) (var4 TSLL) (var5 HeapObject) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (_Glue21 var8 var7 var6 var5) (and (and (and (and (= (getTSLL var5) var4) (= (|TSLL::next| var4) var3)) (= (TSLL var3 1) var2)) (= (O_TSLL var2) var1)) (= (write var8 var6 var1) var0)))) (inv_main1010_2 var0 var7 var6))))
(assert (forall ((var0 Addr) (var1 HeapObject) (var2 TSLL) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr)) (or (not (and (and (Inv_Heap_exp_exp var6 var5 1) (inv_main1010_2 var4 var6 var3)) (and (and (and (and (and (= (O_TSLL var2) var1) (= (TSLL var5 1) var2)) (not (= var0 var6))) (= nullAddr var0)) (= (read var4 var6) var1)) (valid var4 var6)))) (inv_main_17 var4 var6))))
(assert (forall ((var0 TSLL) (var1 HeapObject) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main1010_2 var5 var4 var3) (and (and (and (and (and (not (= var2 var4)) (= nullAddr var2)) (= (read var5 var4) var1)) (= (getTSLL var1) var0)) (= (|TSLL::colour| var0) 1)) (not (valid var5 var4))))) (inv_main_17 var5 var4))))
(assert (forall ((var0 HeapObject) (var1 TSLL) (var2 Heap) (var3 Int) (var4 Addr) (var5 Addr)) (or (not (and (and (Inv_Heap_exp_exp var5 var4 var3) (inv_main_17 var2 var5)) (and (and (and (and (and (and (= (O_TSLL var1) var0) (= (TSLL var4 var3) var1)) (not (= var4 var5))) (not (= 0 var3))) (= nullAddr var4)) (= (read var2 var5) var0)) (valid var2 var5)))) inv_main1049_12)))
(assert (forall ((var0 TSLL) (var1 HeapObject) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main_17 var5 var4) (and (and (and (and (and (and (and (not (= var3 var4)) (not (= 0 var2))) (= nullAddr var3)) (= (read var5 var4) var1)) (= (getTSLL var1) var0)) (= (|TSLL::colour| var0) var2)) (= (|TSLL::next| var0) var3)) (not (valid var5 var4))))) inv_main1049_12)))
(assert (not inv_main1049_12))
(assert (forall ((var0 AllocResHeap) (var1 Heap) (var2 Int) (var3 Addr) (var4 HeapObject) (var5 TSLL)) (or (not (and (and (and (= (O_TSLL var5) var4) (= (TSLL var3 var2) var5)) (= (alloc var1 var4) var0)) (= emptyHeap var1))) (Inv_Heap_exp_exp (newAddr var0) var3 var2))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 HeapObject) (var3 TSLL) (var4 AllocResHeap) (var5 Heap) (var6 HeapObject) (var7 TSLL) (var8 Int) (var9 Addr) (var10 Addr)) (or (not (and (Inv_Heap_exp_exp var10 var9 var8) (and (and (and (and (and (and (and (and (= (O_TSLL var7) var6) (= (AllocResHeap var5 var10) var4)) (= (O_TSLL var3) var2)) (= (TSLL var9 var8) var7)) (= (read var5 var10) var6)) (valid var5 var10)) (= (alloc var1 var2) var4)) (= nullAddr var0)) (= emptyHeap var1)))) (_Glue24 var10 var0 var5 var6))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 HeapObject) (var3 TSLL) (var4 AllocResHeap) (var5 HeapObject) (var6 Addr) (var7 Heap)) (or (not (and (and (and (and (and (and (= (read var7 var6) var5) (not (valid var7 var6))) (= (AllocResHeap var7 var6) var4)) (= (O_TSLL var3) var2)) (= (alloc var1 var2) var4)) (= nullAddr var0)) (= emptyHeap var1))) (_Glue24 var6 var0 var7 var5))))
(assert (forall ((var0 Int) (var1 TSLL) (var2 HeapObject) (var3 Heap) (var4 Addr) (var5 Addr)) (or (not (and (_Glue24 var5 var4 var3 var2) (and (and (= (getTSLL var2) var1) (= (|TSLL::colour| var1) var0)) (valid var3 var5)))) (Inv_Heap_exp_exp var5 var4 var0))))
(assert (forall ((var0 TSLL) (var1 Heap) (var2 HeapObject) (var3 TSLL) (var4 Int) (var5 HeapObject) (var6 TSLL) (var7 HeapObject) (var8 Heap) (var9 Addr) (var10 Int) (var11 Addr) (var12 Addr)) (or (not (and (and (Inv_Heap_exp_exp var12 var11 var10) (_Glue24 var12 var9 var8 var7)) (and (and (and (and (and (and (and (and (= (O_TSLL var6) var5) (= (TSLL var9 var4) var3)) (= (O_TSLL var3) var2)) (= (TSLL var11 var10) var6)) (= (read var1 var12) var5)) (valid var1 var12)) (= (getTSLL var7) var0)) (= (|TSLL::colour| var0) var4)) (= (write var8 var12 var2) var1)))) (_Glue26 var1 var12 var5))))
(assert (forall ((var0 HeapObject) (var1 TSLL) (var2 Int) (var3 TSLL) (var4 HeapObject) (var5 Heap) (var6 HeapObject) (var7 Heap) (var8 Addr) (var9 Addr)) (or (not (and (_Glue24 var9 var8 var7 var6) (and (and (and (and (and (and (= (read var5 var9) var4) (not (valid var5 var9))) (= (getTSLL var6) var3)) (= (|TSLL::colour| var3) var2)) (= (TSLL var8 var2) var1)) (= (O_TSLL var1) var0)) (= (write var7 var9 var0) var5)))) (_Glue26 var5 var9 var4))))
(assert (forall ((var0 Int) (var1 Addr) (var2 TSLL) (var3 HeapObject) (var4 Addr) (var5 Heap)) (or (not (and (_Glue26 var5 var4 var3) (and (and (and (= (getTSLL var3) var2) (= (|TSLL::next| var2) var1)) (valid var5 var4)) (= var0 1)))) (Inv_Heap_exp_exp var4 var1 var0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 HeapObject) (var3 TSLL) (var4 Addr) (var5 TSLL) (var6 HeapObject) (var7 Addr) (var8 Heap)) (or (not (and (_Glue26 var8 var7 var6) (and (and (and (and (and (= (getTSLL var6) var5) (= (|TSLL::next| var5) var4)) (= (TSLL var4 1) var3)) (= (O_TSLL var3) var2)) (= (write var8 var7 var2) var1)) (= var0 var7)))) (inv_main1010_2 var1 var7 var0))))
(assert (forall ((var0 Addr) (var1 HeapObject) (var2 TSLL) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr)) (or (not (and (and (Inv_Heap_exp_exp var6 var5 var4) (inv_main_17 var3 var6)) (and (and (and (and (and (and (and (= (O_TSLL var2) var1) (= (TSLL var5 var4) var2)) (not (= var0 var6))) (not (= 0 var4))) (not (= var5 var0))) (= nullAddr var0)) (= (read var3 var6) var1)) (valid var3 var6)))) (inv_main_17 var3 var5))))
(assert (forall ((var0 TSLL) (var1 HeapObject) (var2 Addr) (var3 Int) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main_17 var6 var5) (and (and (and (and (and (and (and (and (not (= var4 var5)) (not (= 0 var3))) (not (= var2 var4))) (= nullAddr var4)) (= (read var6 var5) var1)) (= (getTSLL var1) var0)) (= (|TSLL::colour| var0) var3)) (= (|TSLL::next| var0) var2)) (not (valid var6 var5))))) (inv_main_17 var6 var2))))
(assert (forall ((var0 AllocResHeap) (var1 Int) (var2 Addr) (var3 HeapObject) (var4 TSLL) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main1010_2 var7 var6 var5) (and (and (= (O_TSLL var4) var3) (= (TSLL var2 var1) var4)) (= (alloc var7 var3) var0)))) (Inv_Heap_exp_exp (newAddr var0) var2 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 AllocResHeap) (var3 Addr) (var4 Heap) (var5 HeapObject) (var6 TSLL) (var7 HeapObject) (var8 TSLL) (var9 Addr) (var10 Heap) (var11 Int) (var12 Addr) (var13 Addr)) (or (not (and (and (Inv_Heap_exp_exp var13 var12 var11) (inv_main1010_2 var10 var9 var13)) (and (and (and (and (and (and (= (O_TSLL var8) var7) (= (O_TSLL var6) var5)) (= (AllocResHeap var4 var3) var2)) (= (TSLL var12 var11) var8)) (= (read var4 var13) var7)) (valid var4 var13)) (= (alloc var10 var5) var2)))) (_Glue1_exp_exp var13 var9 var1 var0 var3 var4 var7))))
(assert (forall ((var0 Int) (var1 Addr) (var2 HeapObject) (var3 AllocResHeap) (var4 Addr) (var5 Heap) (var6 HeapObject) (var7 TSLL) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main1010_2 var10 var9 var8) (and (and (and (and (= (O_TSLL var7) var6) (= (AllocResHeap var5 var4) var3)) (= (read var5 var8) var2)) (not (valid var5 var8))) (= (alloc var10 var6) var3)))) (_Glue1_exp_exp var8 var9 var1 var0 var4 var5 var2))))
(assert (forall ((var0 Int) (var1 TSLL) (var2 HeapObject) (var3 Heap) (var4 Addr) (var5 Int) (var6 Addr) (var7 Addr) (var8 Addr)) (or (not (and (_Glue1_exp_exp var8 var7 var6 var5 var4 var3 var2) (and (and (= (getTSLL var2) var1) (= (|TSLL::colour| var1) var0)) (valid var3 var8)))) (Inv_Heap_exp_exp var8 var4 var0))))
(assert (forall ((var0 TSLL) (var1 Heap) (var2 HeapObject) (var3 TSLL) (var4 Int) (var5 HeapObject) (var6 TSLL) (var7 HeapObject) (var8 Heap) (var9 Addr) (var10 Int) (var11 Addr) (var12 Addr) (var13 Int) (var14 Addr) (var15 Addr)) (or (not (and (and (Inv_Heap_exp_exp var15 var14 var13) (_Glue1_exp_exp var15 var12 var11 var10 var9 var8 var7)) (and (and (and (and (and (and (and (and (= (O_TSLL var6) var5) (= (TSLL var9 var4) var3)) (= (O_TSLL var3) var2)) (= (TSLL var14 var13) var6)) (= (read var1 var15) var5)) (= (getTSLL var7) var0)) (= (|TSLL::colour| var0) var4)) (= (write var8 var15 var2) var1)) (valid var1 var15)))) (_Glue3_exp_exp var1 var12 var11 var10 var5))))
(assert (forall ((var0 TSLL) (var1 HeapObject) (var2 Heap) (var3 HeapObject) (var4 TSLL) (var5 Int) (var6 HeapObject) (var7 Heap) (var8 Addr) (var9 Int) (var10 Addr) (var11 Addr) (var12 Addr)) (or (not (and (_Glue1_exp_exp var12 var11 var10 var9 var8 var7 var6) (and (and (and (and (and (and (= (TSLL var8 var5) var4) (= (O_TSLL var4) var3)) (= (read var2 var12) var1)) (= (getTSLL var6) var0)) (= (|TSLL::colour| var0) var5)) (= (write var7 var12 var3) var2)) (not (valid var2 var12))))) (_Glue3_exp_exp var2 var11 var10 var9 var1))))
(assert (forall ((var0 TSLL) (var1 HeapObject) (var2 TSLL) (var3 HeapObject) (var4 Int) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Int) (var9 Addr) (var10 Addr)) (or (not (and (and (Inv_Heap_exp_exp var10 var9 var8) (_Glue3_exp_exp var7 var6 var5 var4 var3)) (and (and (and (and (and (= (O_TSLL var2) var1) (= (TSLL var9 var8) var2)) (= (getTSLL var3) var0)) (= (|TSLL::next| var0) var10)) (= (read var7 var10) var1)) (valid var7 var10)))) (_Glue4_exp_exp var5 var4 var6 var7 var10 var1))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 TSLL) (var3 HeapObject) (var4 Int) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (_Glue3_exp_exp var7 var6 var5 var4 var3) (and (and (and (= (getTSLL var3) var2) (= (|TSLL::next| var2) var1)) (= (read var7 var1) var0)) (not (valid var7 var1))))) (_Glue4_exp_exp var5 var4 var6 var7 var1 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 TSLL) (var3 HeapObject) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Int) (var8 Addr)) (or (not (and (_Glue4_exp_exp var8 var7 var6 var5 var4 var3) (and (and (and (= (getTSLL var3) var2) (= (|TSLL::colour| var2) var1)) (= nullAddr var0)) (valid var5 var4)))) (Inv_Heap_exp_exp var4 var0 var1))))
(assert (forall ((var0 TSLL) (var1 Heap) (var2 HeapObject) (var3 TSLL) (var4 Int) (var5 Addr) (var6 HeapObject) (var7 TSLL) (var8 HeapObject) (var9 Heap) (var10 Addr) (var11 Int) (var12 Addr) (var13 Int) (var14 Addr) (var15 Addr)) (or (not (and (and (Inv_Heap_exp_exp var15 var14 var13) (_Glue4_exp_exp var12 var11 var10 var9 var15 var8)) (and (and (and (and (and (and (and (and (and (= (O_TSLL var7) var6) (= (TSLL var5 var4) var3)) (= (O_TSLL var3) var2)) (= (TSLL var14 var13) var7)) (= (read var1 var15) var6)) (= (getTSLL var8) var0)) (= (|TSLL::colour| var0) var4)) (= nullAddr var5)) (= (write var9 var15 var2) var1)) (valid var1 var15)))) (_Glue6_exp_exp var1 var5 var12 var11 var10 var15 var6))))
(assert (forall ((var0 TSLL) (var1 HeapObject) (var2 Heap) (var3 HeapObject) (var4 TSLL) (var5 Int) (var6 Addr) (var7 HeapObject) (var8 Addr) (var9 Heap) (var10 Addr) (var11 Int) (var12 Addr)) (or (not (and (_Glue4_exp_exp var12 var11 var10 var9 var8 var7) (and (and (and (and (and (and (and (= (TSLL var6 var5) var4) (= (O_TSLL var4) var3)) (= (read var2 var8) var1)) (= (getTSLL var7) var0)) (= (|TSLL::colour| var0) var5)) (= nullAddr var6)) (= (write var9 var8 var3) var2)) (not (valid var2 var8))))) (_Glue6_exp_exp var2 var6 var12 var11 var10 var8 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 TSLL) (var3 HeapObject) (var4 Addr) (var5 Addr) (var6 Int) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (_Glue6_exp_exp var9 var8 var7 var6 var5 var4 var3) (and (and (and (= (getTSLL var3) var2) (= (|TSLL::next| var2) var1)) (valid var9 var4)) (= var0 0)))) (Inv_Heap_exp_exp var4 var1 var0))))
(assert (forall ((var0 TSLL) (var1 AllocResHeap) (var2 Heap) (var3 HeapObject) (var4 TSLL) (var5 Addr) (var6 HeapObject) (var7 TSLL) (var8 HeapObject) (var9 Addr) (var10 Addr) (var11 Int) (var12 Addr) (var13 Addr) (var14 Heap)) (or (not (and (_Glue6_exp_exp var14 var13 var12 var11 var10 var9 var8) (and (and (and (and (and (and (and (= (O_TSLL var7) var6) (= (TSLL var5 0) var4)) (= (O_TSLL var4) var3)) (= (TSLL var12 var11) var7)) (= (alloc var2 var6) var1)) (= (getTSLL var8) var0)) (= (|TSLL::next| var0) var5)) (= (write var14 var9 var3) var2)))) (Inv_Heap_exp_exp (newAddr var1) var12 var11))))
(assert (forall ((var0 TSLL) (var1 Heap) (var2 HeapObject) (var3 TSLL) (var4 Addr) (var5 HeapObject) (var6 TSLL) (var7 AllocResHeap) (var8 Addr) (var9 Heap) (var10 HeapObject) (var11 TSLL) (var12 HeapObject) (var13 Addr) (var14 Int) (var15 Addr) (var16 Addr) (var17 Heap) (var18 Int) (var19 Addr) (var20 Addr)) (or (not (and (and (Inv_Heap_exp_exp var20 var19 var18) (_Glue6_exp_exp var17 var16 var15 var14 var13 var20 var12)) (and (and (and (and (and (and (and (and (and (and (and (and (= (O_TSLL var11) var10) (= (AllocResHeap var9 var8) var7)) (= (O_TSLL var6) var5)) (= (TSLL var4 0) var3)) (= (O_TSLL var3) var2)) (= (TSLL var19 var18) var11)) (= (TSLL var15 var14) var6)) (= (read var9 var20) var10)) (valid var9 var20)) (= (alloc var1 var5) var7)) (= (getTSLL var12) var0)) (= (|TSLL::next| var0) var4)) (= (write var17 var20 var2) var1)))) (_Glue9 var20 var13 var16 var8 var9 var10))))
(assert (forall ((var0 TSLL) (var1 Heap) (var2 HeapObject) (var3 HeapObject) (var4 TSLL) (var5 Addr) (var6 HeapObject) (var7 TSLL) (var8 AllocResHeap) (var9 Addr) (var10 Heap) (var11 HeapObject) (var12 Addr) (var13 Addr) (var14 Int) (var15 Addr) (var16 Addr) (var17 Heap)) (or (not (and (_Glue6_exp_exp var17 var16 var15 var14 var13 var12 var11) (and (and (and (and (and (and (and (and (and (and (= (AllocResHeap var10 var9) var8) (= (O_TSLL var7) var6)) (= (TSLL var5 0) var4)) (= (O_TSLL var4) var3)) (= (TSLL var15 var14) var7)) (= (read var10 var12) var2)) (not (valid var10 var12))) (= (alloc var1 var6) var8)) (= (getTSLL var11) var0)) (= (|TSLL::next| var0) var5)) (= (write var17 var12 var3) var1)))) (_Glue9 var12 var13 var16 var9 var10 var2))))
(assert (forall ((var0 Int) (var1 TSLL) (var2 HeapObject) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr)) (or (not (and (_Glue9 var7 var6 var5 var4 var3 var2) (and (and (= (getTSLL var2) var1) (= (|TSLL::colour| var1) var0)) (valid var3 var7)))) (Inv_Heap_exp_exp var7 var4 var0))))
(assert (forall ((var0 TSLL) (var1 Heap) (var2 HeapObject) (var3 TSLL) (var4 Int) (var5 HeapObject) (var6 TSLL) (var7 HeapObject) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Int) (var13 Addr) (var14 Addr)) (or (not (and (and (Inv_Heap_exp_exp var14 var13 var12) (_Glue9 var14 var11 var10 var9 var8 var7)) (and (and (and (and (and (and (and (and (= (O_TSLL var6) var5) (= (TSLL var9 var4) var3)) (= (O_TSLL var3) var2)) (= (TSLL var13 var12) var6)) (= (read var1 var14) var5)) (valid var1 var14)) (= (getTSLL var7) var0)) (= (|TSLL::colour| var0) var4)) (= (write var8 var14 var2) var1)))) (_Glue11 var1 var11 var10 var5))))
(assert (forall ((var0 HeapObject) (var1 TSLL) (var2 Int) (var3 TSLL) (var4 HeapObject) (var5 Heap) (var6 HeapObject) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr)) (or (not (and (_Glue9 var11 var10 var9 var8 var7 var6) (and (and (and (and (and (and (= (read var5 var11) var4) (not (valid var5 var11))) (= (getTSLL var6) var3)) (= (|TSLL::colour| var3) var2)) (= (TSLL var8 var2) var1)) (= (O_TSLL var1) var0)) (= (write var7 var11 var0) var5)))) (_Glue11 var5 var10 var9 var4))))
(assert (forall ((var0 TSLL) (var1 HeapObject) (var2 TSLL) (var3 HeapObject) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Int) (var8 Addr) (var9 Addr)) (or (not (and (and (Inv_Heap_exp_exp var9 var8 var7) (_Glue11 var6 var5 var4 var3)) (and (and (and (and (and (= (O_TSLL var2) var1) (= (TSLL var8 var7) var2)) (= (getTSLL var3) var0)) (= (|TSLL::next| var0) var9)) (= (read var6 var9) var1)) (valid var6 var9)))) (_Glue12 var4 var5 var6 var9 var1))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 TSLL) (var3 HeapObject) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (_Glue11 var6 var5 var4 var3) (and (and (and (= (getTSLL var3) var2) (= (|TSLL::next| var2) var1)) (= (read var6 var1) var0)) (not (valid var6 var1))))) (_Glue12 var4 var5 var6 var1 var0))))
(assert (forall ((var0 Int) (var1 TSLL) (var2 HeapObject) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr)) (or (not (and (_Glue12 var6 var5 var4 var3 var2) (and (and (= (getTSLL var2) var1) (= (|TSLL::colour| var1) var0)) (valid var4 var3)))) (Inv_Heap_exp_exp var3 var6 var0))))
(assert (forall ((var0 TSLL) (var1 Heap) (var2 HeapObject) (var3 TSLL) (var4 Int) (var5 HeapObject) (var6 TSLL) (var7 HeapObject) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Int) (var12 Addr) (var13 Addr)) (or (not (and (and (Inv_Heap_exp_exp var13 var12 var11) (_Glue12 var10 var9 var8 var13 var7)) (and (and (and (and (and (and (and (and (= (O_TSLL var6) var5) (= (TSLL var10 var4) var3)) (= (O_TSLL var3) var2)) (= (TSLL var12 var11) var6)) (= (read var1 var13) var5)) (valid var1 var13)) (= (getTSLL var7) var0)) (= (|TSLL::colour| var0) var4)) (= (write var8 var13 var2) var1)))) (_Glue14 var1 var9 var13 var5))))
(assert (forall ((var0 HeapObject) (var1 TSLL) (var2 Int) (var3 TSLL) (var4 HeapObject) (var5 Heap) (var6 HeapObject) (var7 Addr) (var8 Heap) (var9 Addr) (var10 Addr)) (or (not (and (_Glue12 var10 var9 var8 var7 var6) (and (and (and (and (and (and (= (read var5 var7) var4) (not (valid var5 var7))) (= (getTSLL var6) var3)) (= (|TSLL::colour| var3) var2)) (= (TSLL var10 var2) var1)) (= (O_TSLL var1) var0)) (= (write var8 var7 var0) var5)))) (_Glue14 var5 var9 var7 var4))))
(assert (forall ((var0 Int) (var1 Addr) (var2 TSLL) (var3 HeapObject) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (_Glue14 var6 var5 var4 var3) (and (and (and (= (getTSLL var3) var2) (= (|TSLL::next| var2) var1)) (valid var6 var4)) (= var0 1)))) (Inv_Heap_exp_exp var4 var1 var0))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 TSLL) (var3 Addr) (var4 TSLL) (var5 HeapObject) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (_Glue14 var8 var7 var6 var5) (and (and (and (and (= (getTSLL var5) var4) (= (|TSLL::next| var4) var3)) (= (TSLL var3 1) var2)) (= (O_TSLL var2) var1)) (= (write var8 var6 var1) var0)))) (inv_main1010_2 var0 var7 var6))))
(assert (forall ((var0 Addr) (var1 HeapObject) (var2 TSLL) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr)) (or (not (and (and (Inv_Heap_exp_exp var6 var5 var4) (inv_main_17 var3 var6)) (and (and (and (and (and (= (O_TSLL var2) var1) (= (TSLL var5 var4) var2)) (= nullAddr var0)) (not (= var0 var6))) (= (read var3 var6) var1)) (valid var3 var6)))) (_Glue29 var0 var3 var1))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main_17 var3 var2) (and (and (and (= nullAddr var1) (not (= var1 var2))) (= (read var3 var2) var0)) (not (valid var3 var2))))) (_Glue29 var1 var3 var0))))
(assert (forall ((var0 TSLL) (var1 HeapObject) (var2 TSLL) (var3 HeapObject) (var4 Heap) (var5 Addr) (var6 Int) (var7 Addr) (var8 Addr)) (or (not (and (and (Inv_Heap_exp_exp var8 var7 var6) (_Glue29 var5 var4 var3)) (and (and (and (and (and (and (= (O_TSLL var2) var1) (= (TSLL var7 var6) var2)) (= (getTSLL var3) var0)) (= (|TSLL::colour| var0) 0)) (= (|TSLL::next| var0) var8)) (= (read var4 var8) var1)) (valid var4 var8)))) (_Glue30 var4 var5 var1))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 TSLL) (var3 HeapObject) (var4 Heap) (var5 Addr)) (or (not (and (_Glue29 var5 var4 var3) (and (and (and (and (= (getTSLL var3) var2) (= (|TSLL::colour| var2) 0)) (= (|TSLL::next| var2) var1)) (= (read var4 var1) var0)) (not (valid var4 var1))))) (_Glue30 var4 var5 var0))))
(assert (forall ((var0 TSLL) (var1 HeapObject) (var2 TSLL) (var3 HeapObject) (var4 Addr) (var5 Heap) (var6 Int) (var7 Addr) (var8 Addr)) (or (not (and (and (Inv_Heap_exp_exp var8 var7 var6) (_Glue30 var5 var4 var3)) (and (and (and (and (and (and (= (O_TSLL var2) var1) (= (TSLL var7 var6) var2)) (= (getTSLL var3) var0)) (= (|TSLL::next| var0) var8)) (= (read var5 var8) var1)) (not (= var7 var4))) (valid var5 var8)))) (inv_main_17 var5 var7))))
(assert (forall ((var0 Addr) (var1 TSLL) (var2 HeapObject) (var3 Addr) (var4 TSLL) (var5 HeapObject) (var6 Addr) (var7 Heap)) (or (not (and (_Glue30 var7 var6 var5) (and (and (and (and (and (and (= (getTSLL var5) var4) (= (|TSLL::next| var4) var3)) (= (read var7 var3) var2)) (= (getTSLL var2) var1)) (= (|TSLL::next| var1) var0)) (not (= var0 var6))) (not (valid var7 var3))))) (inv_main_17 var7 var0))))
(assert (forall ((var0 Addr) (var1 HeapObject) (var2 TSLL) (var3 Addr) (var4 Heap) (var5 Int) (var6 Addr) (var7 Addr)) (not (and (and (Inv_Heap_exp_exp var7 var6 var5) (inv_main1010_2 var4 var7 var3)) (and (and (and (and (and (and (= (O_TSLL var2) var1) (= (TSLL var6 var5) var2)) (not (= var0 var7))) (not (= 1 var5))) (= nullAddr var0)) (= (read var4 var7) var1)) (valid var4 var7))))))
(assert (forall ((var0 TSLL) (var1 HeapObject) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap)) (not (and (inv_main1010_2 var6 var5 var4) (and (and (and (and (and (and (not (= var3 var5)) (not (= 1 var2))) (= nullAddr var3)) (= (read var6 var5) var1)) (= (getTSLL var1) var0)) (= (|TSLL::colour| var0) var2)) (not (valid var6 var5)))))))
(check-sat)
