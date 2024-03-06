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
(declare-fun inv_main_17 (Heap Addr Addr) Bool)
(declare-fun _Glue33 (Heap Addr Addr HeapObject) Bool)
(declare-fun inv_main_20 (Heap Addr) Bool)
(declare-fun _Glue0 (HeapObject Addr Heap Addr HeapObject) Bool)
(declare-fun _Glue2 (Addr Heap Addr HeapObject) Bool)
(declare-fun _Glue7_exp_exp (Heap Addr Addr Int HeapObject) Bool)
(declare-fun inv_main1010_2 (Heap Addr Addr) Bool)
(declare-fun _Glue28 (Addr Addr Addr Heap HeapObject) Bool)
(declare-fun _Glue13 (Addr Addr Addr Addr Heap HeapObject) Bool)
(declare-fun _Glue26 (Heap Addr HeapObject) Bool)
(declare-fun _Glue18 (Heap Addr Addr HeapObject) Bool)
(declare-fun _Glue15 (Heap Addr Addr HeapObject) Bool)
(declare-fun _Glue8_exp_exp (Addr Int Addr Heap Addr HeapObject) Bool)
(declare-fun Inv_Heap (Addr HeapObject) Bool)
(declare-fun _Glue19 (Heap Addr HeapObject) Bool)
(declare-fun _Glue31 (Addr Heap Addr HeapObject) Bool)
(declare-fun _Glue30 (Heap Addr HeapObject) Bool)
(declare-fun _Glue3 (Addr Addr Heap HeapObject) Bool)
(declare-fun _Glue21_exp (Heap Addr HeapObject) Bool)
(declare-fun _Glue24 (Addr Addr Heap HeapObject) Bool)
(declare-fun _Glue10_exp_exp (Heap Addr Addr Int Addr Addr HeapObject) Bool)
(declare-fun _Glue16 (Addr Addr Heap Addr HeapObject) Bool)
(declare-fun _Glue5_exp_exp (Addr Addr Addr Int Addr Heap HeapObject) Bool)
(assert (forall ((var0 Int) (var1 TSLL) (var2 Addr) (var3 Heap) (var4 HeapObject) (var5 Addr)) (not (and (and (Inv_Heap var5 var4) (inv_main_20 var3 var5)) (and (and (and (and (and (and (and (and (= defObj var4) (= (read var3 var5) var4)) (= nullAddr var2)) (= (getTSLL var4) var1)) (= (|TSLL::colour| var1) var0)) (not (= var5 var2))) (not (= var2 var5))) (not (= 0 var0))) (valid var3 var5))))))
(assert (forall ((var0 Int) (var1 TSLL) (var2 Addr) (var3 HeapObject) (var4 Addr) (var5 Heap)) (not (and (inv_main_20 var5 var4) (and (and (and (and (and (and (and (and (= defObj var3) (= (read var5 var4) var3)) (= nullAddr var2)) (= (getTSLL var3) var1)) (= (|TSLL::colour| var1) var0)) (not (= var4 var2))) (not (= var2 var4))) (not (= 0 var0))) (not (valid var5 var4)))))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Heap) (var3 HeapObject) (var4 Addr)) (or (not (and (and (Inv_Heap var4 var3) (inv_main_20 var2 var4)) (and (and (and (= nullAddr var1) (not (= var1 var4))) (= (read var2 var4) var3)) (valid var2 var4)))) (_Glue0 var0 var1 var2 var4 var3))))
(assert (forall ((var0 HeapObject) (var1 HeapObject) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main_20 var4 var3) (and (and (and (= nullAddr var2) (not (= var2 var3))) (= (read var4 var3) var1)) (not (valid var4 var3))))) (_Glue0 var0 var2 var4 var3 var1))))
(assert (forall ((var0 Addr) (var1 TSLL) (var2 HeapObject) (var3 HeapObject) (var4 Addr) (var5 Heap) (var6 Addr) (var7 HeapObject)) (or (not (and (_Glue0 var7 var6 var5 var4 var3) (and (and (and (and (and (= defObj var2) (= (getTSLL var3) var1)) (= (|TSLL::colour| var1) 0)) (= (|TSLL::next| var1) var0)) (not (= var0 var6))) (valid var5 var4)))) (Inv_Heap var4 var2))))
(assert (forall ((var0 TSLL) (var1 Heap) (var2 HeapObject) (var3 Addr) (var4 Heap) (var5 Addr) (var6 HeapObject) (var7 Addr)) (not (and (and (Inv_Heap var7 var6) (_Glue0 var6 var5 var4 var3 var2)) (and (and (and (and (and (and (and (= defObj var6) (= (read var1 var7) var6)) (= (getTSLL var2) var0)) (= (|TSLL::colour| var0) 0)) (= (|TSLL::next| var0) var7)) (= (write var4 var3 var6) var1)) (valid var1 var7)) (not (= var7 var5)))))))
(assert (forall ((var0 TSLL) (var1 Addr) (var2 Heap) (var3 HeapObject) (var4 Addr) (var5 Heap) (var6 Addr) (var7 HeapObject)) (not (and (_Glue0 var7 var6 var5 var4 var3) (and (and (and (and (and (and (and (= defObj var7) (= (read var2 var1) var7)) (= (getTSLL var3) var0)) (= (|TSLL::colour| var0) 0)) (= (|TSLL::next| var0) var1)) (= (write var5 var4 var7) var2)) (not (valid var2 var1))) (not (= var1 var6)))))))
(assert (forall ((var0 AllocResHeap) (var1 HeapObject) (var2 TSLL) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main1010_2 var5 var4 var3) (and (= (O_TSLL var2) var1) (= (alloc var5 var1) var0)))) (Inv_Heap (newAddr var0) var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 AllocResHeap) (var3 Addr) (var4 Heap) (var5 HeapObject) (var6 TSLL) (var7 Addr) (var8 Heap) (var9 HeapObject) (var10 Addr)) (or (not (and (and (Inv_Heap var10 var9) (inv_main1010_2 var8 var7 var10)) (and (and (and (and (= (O_TSLL var6) var5) (= (AllocResHeap var4 var3) var2)) (= (read var4 var10) var9)) (valid var4 var10)) (= (alloc var8 var5) var2)))) (_Glue5_exp_exp var10 var7 var1 var0 var3 var4 var9))))
(assert (forall ((var0 Int) (var1 Addr) (var2 HeapObject) (var3 AllocResHeap) (var4 Addr) (var5 Heap) (var6 HeapObject) (var7 TSLL) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main1010_2 var10 var9 var8) (and (and (and (and (= (O_TSLL var7) var6) (= (AllocResHeap var5 var4) var3)) (= (read var5 var8) var2)) (not (valid var5 var8))) (= (alloc var10 var6) var3)))) (_Glue5_exp_exp var8 var9 var1 var0 var4 var5 var2))))
(assert (forall ((var0 TSLL) (var1 HeapObject) (var2 TSLL) (var3 Int) (var4 HeapObject) (var5 Heap) (var6 Addr) (var7 Int) (var8 Addr) (var9 Addr) (var10 Addr)) (or (not (and (_Glue5_exp_exp var10 var9 var8 var7 var6 var5 var4) (and (and (and (and (= (TSLL var6 var3) var2) (= (O_TSLL var2) var1)) (= (getTSLL var4) var0)) (= (|TSLL::colour| var0) var3)) (valid var5 var10)))) (Inv_Heap var10 var1))))
(assert (forall ((var0 TSLL) (var1 Heap) (var2 HeapObject) (var3 TSLL) (var4 Int) (var5 HeapObject) (var6 Heap) (var7 Addr) (var8 Int) (var9 Addr) (var10 Addr) (var11 HeapObject) (var12 Addr)) (or (not (and (and (Inv_Heap var12 var11) (_Glue5_exp_exp var12 var10 var9 var8 var7 var6 var5)) (and (and (and (and (and (and (= (TSLL var7 var4) var3) (= (O_TSLL var3) var2)) (= (read var1 var12) var11)) (= (getTSLL var5) var0)) (= (|TSLL::colour| var0) var4)) (= (write var6 var12 var2) var1)) (valid var1 var12)))) (_Glue7_exp_exp var1 var10 var9 var8 var11))))
(assert (forall ((var0 TSLL) (var1 HeapObject) (var2 Heap) (var3 HeapObject) (var4 TSLL) (var5 Int) (var6 HeapObject) (var7 Heap) (var8 Addr) (var9 Int) (var10 Addr) (var11 Addr) (var12 Addr)) (or (not (and (_Glue5_exp_exp var12 var11 var10 var9 var8 var7 var6) (and (and (and (and (and (and (= (TSLL var8 var5) var4) (= (O_TSLL var4) var3)) (= (read var2 var12) var1)) (= (getTSLL var6) var0)) (= (|TSLL::colour| var0) var5)) (= (write var7 var12 var3) var2)) (not (valid var2 var12))))) (_Glue7_exp_exp var2 var11 var10 var9 var1))))
(assert (forall ((var0 TSLL) (var1 HeapObject) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap) (var6 HeapObject) (var7 Addr)) (or (not (and (and (Inv_Heap var7 var6) (_Glue7_exp_exp var5 var4 var3 var2 var1)) (and (and (and (= (getTSLL var1) var0) (= (|TSLL::next| var0) var7)) (= (read var5 var7) var6)) (valid var5 var7)))) (_Glue8_exp_exp var3 var2 var4 var5 var7 var6))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 TSLL) (var3 HeapObject) (var4 Int) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (_Glue7_exp_exp var7 var6 var5 var4 var3) (and (and (and (= (getTSLL var3) var2) (= (|TSLL::next| var2) var1)) (= (read var7 var1) var0)) (not (valid var7 var1))))) (_Glue8_exp_exp var5 var4 var6 var7 var1 var0))))
(assert (forall ((var0 TSLL) (var1 HeapObject) (var2 TSLL) (var3 Int) (var4 Addr) (var5 HeapObject) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Int) (var10 Addr)) (or (not (and (_Glue8_exp_exp var10 var9 var8 var7 var6 var5) (and (and (and (and (and (= (TSLL var4 var3) var2) (= (O_TSLL var2) var1)) (= (getTSLL var5) var0)) (= (|TSLL::colour| var0) var3)) (= nullAddr var4)) (valid var7 var6)))) (Inv_Heap var6 var1))))
(assert (forall ((var0 TSLL) (var1 Heap) (var2 HeapObject) (var3 TSLL) (var4 Int) (var5 Addr) (var6 HeapObject) (var7 Heap) (var8 Addr) (var9 Int) (var10 Addr) (var11 HeapObject) (var12 Addr)) (or (not (and (and (Inv_Heap var12 var11) (_Glue8_exp_exp var10 var9 var8 var7 var12 var6)) (and (and (and (and (and (and (and (= (TSLL var5 var4) var3) (= (O_TSLL var3) var2)) (= (read var1 var12) var11)) (= (getTSLL var6) var0)) (= (|TSLL::colour| var0) var4)) (= nullAddr var5)) (= (write var7 var12 var2) var1)) (valid var1 var12)))) (_Glue10_exp_exp var1 var5 var10 var9 var8 var12 var11))))
(assert (forall ((var0 TSLL) (var1 HeapObject) (var2 Heap) (var3 HeapObject) (var4 TSLL) (var5 Int) (var6 Addr) (var7 HeapObject) (var8 Addr) (var9 Heap) (var10 Addr) (var11 Int) (var12 Addr)) (or (not (and (_Glue8_exp_exp var12 var11 var10 var9 var8 var7) (and (and (and (and (and (and (and (= (TSLL var6 var5) var4) (= (O_TSLL var4) var3)) (= (read var2 var8) var1)) (= (getTSLL var7) var0)) (= (|TSLL::colour| var0) var5)) (= nullAddr var6)) (= (write var9 var8 var3) var2)) (not (valid var2 var8))))) (_Glue10_exp_exp var2 var6 var12 var11 var10 var8 var1))))
(assert (forall ((var0 TSLL) (var1 HeapObject) (var2 TSLL) (var3 Addr) (var4 HeapObject) (var5 Addr) (var6 Addr) (var7 Int) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (_Glue10_exp_exp var10 var9 var8 var7 var6 var5 var4) (and (and (and (and (= (TSLL var3 0) var2) (= (O_TSLL var2) var1)) (= (getTSLL var4) var0)) (= (|TSLL::next| var0) var3)) (valid var10 var5)))) (Inv_Heap var5 var1))))
(assert (forall ((var0 TSLL) (var1 AllocResHeap) (var2 Heap) (var3 HeapObject) (var4 TSLL) (var5 Addr) (var6 HeapObject) (var7 TSLL) (var8 HeapObject) (var9 Addr) (var10 Addr) (var11 Int) (var12 Addr) (var13 Addr) (var14 Heap)) (or (not (and (_Glue10_exp_exp var14 var13 var12 var11 var10 var9 var8) (and (and (and (and (and (and (and (= (O_TSLL var7) var6) (= (TSLL var5 0) var4)) (= (O_TSLL var4) var3)) (= (TSLL var12 var11) var7)) (= (alloc var2 var6) var1)) (= (getTSLL var8) var0)) (= (|TSLL::next| var0) var5)) (= (write var14 var9 var3) var2)))) (Inv_Heap (newAddr var1) var6))))
(assert (forall ((var0 TSLL) (var1 Heap) (var2 HeapObject) (var3 TSLL) (var4 Addr) (var5 HeapObject) (var6 TSLL) (var7 AllocResHeap) (var8 Addr) (var9 Heap) (var10 HeapObject) (var11 Addr) (var12 Int) (var13 Addr) (var14 Addr) (var15 Heap) (var16 HeapObject) (var17 Addr)) (or (not (and (and (Inv_Heap var17 var16) (_Glue10_exp_exp var15 var14 var13 var12 var11 var17 var10)) (and (and (and (and (and (and (and (and (and (and (= (AllocResHeap var9 var8) var7) (= (O_TSLL var6) var5)) (= (TSLL var4 0) var3)) (= (O_TSLL var3) var2)) (= (TSLL var13 var12) var6)) (= (read var9 var17) var16)) (valid var9 var17)) (= (alloc var1 var5) var7)) (= (getTSLL var10) var0)) (= (|TSLL::next| var0) var4)) (= (write var15 var17 var2) var1)))) (_Glue13 var17 var11 var14 var8 var9 var16))))
(assert (forall ((var0 TSLL) (var1 Heap) (var2 HeapObject) (var3 HeapObject) (var4 TSLL) (var5 Addr) (var6 HeapObject) (var7 TSLL) (var8 AllocResHeap) (var9 Addr) (var10 Heap) (var11 HeapObject) (var12 Addr) (var13 Addr) (var14 Int) (var15 Addr) (var16 Addr) (var17 Heap)) (or (not (and (_Glue10_exp_exp var17 var16 var15 var14 var13 var12 var11) (and (and (and (and (and (and (and (and (and (and (= (AllocResHeap var10 var9) var8) (= (O_TSLL var7) var6)) (= (TSLL var5 0) var4)) (= (O_TSLL var4) var3)) (= (TSLL var15 var14) var7)) (= (read var10 var12) var2)) (not (valid var10 var12))) (= (alloc var1 var6) var8)) (= (getTSLL var11) var0)) (= (|TSLL::next| var0) var5)) (= (write var17 var12 var3) var1)))) (_Glue13 var12 var13 var16 var9 var10 var2))))
(assert (forall ((var0 HeapObject) (var1 TSLL) (var2 Int) (var3 TSLL) (var4 HeapObject) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr)) (or (not (and (_Glue13 var9 var8 var7 var6 var5 var4) (and (and (and (and (= (getTSLL var4) var3) (= (|TSLL::colour| var3) var2)) (= (TSLL var6 var2) var1)) (= (O_TSLL var1) var0)) (valid var5 var9)))) (Inv_Heap var9 var0))))
(assert (forall ((var0 HeapObject) (var1 TSLL) (var2 Int) (var3 TSLL) (var4 Heap) (var5 HeapObject) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Addr) (var10 HeapObject) (var11 Addr)) (or (not (and (and (Inv_Heap var11 var10) (_Glue13 var11 var9 var8 var7 var6 var5)) (and (and (and (and (and (and (and (= (read var4 var11) var10) (valid var4 var11)) true) (= (getTSLL var5) var3)) (= (|TSLL::colour| var3) var2)) (= (TSLL var7 var2) var1)) (= (O_TSLL var1) var0)) (= (write var6 var11 var0) var4)))) (_Glue15 var4 var9 var8 var10))))
(assert (forall ((var0 HeapObject) (var1 TSLL) (var2 Int) (var3 TSLL) (var4 HeapObject) (var5 Heap) (var6 HeapObject) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr)) (or (not (and (_Glue13 var11 var10 var9 var8 var7 var6) (and (and (and (and (and (and (= (read var5 var11) var4) (not (valid var5 var11))) (= (getTSLL var6) var3)) (= (|TSLL::colour| var3) var2)) (= (TSLL var8 var2) var1)) (= (O_TSLL var1) var0)) (= (write var7 var11 var0) var5)))) (_Glue15 var5 var10 var9 var4))))
(assert (forall ((var0 TSLL) (var1 HeapObject) (var2 Addr) (var3 Addr) (var4 Heap) (var5 HeapObject) (var6 Addr)) (or (not (and (and (Inv_Heap var6 var5) (_Glue15 var4 var3 var2 var1)) (and (and (and (= (getTSLL var1) var0) (= (|TSLL::next| var0) var6)) (= (read var4 var6) var5)) (valid var4 var6)))) (_Glue16 var2 var3 var4 var6 var5))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 TSLL) (var3 HeapObject) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (_Glue15 var6 var5 var4 var3) (and (and (and (= (getTSLL var3) var2) (= (|TSLL::next| var2) var1)) (= (read var6 var1) var0)) (not (valid var6 var1))))) (_Glue16 var4 var5 var6 var1 var0))))
(assert (forall ((var0 HeapObject) (var1 TSLL) (var2 Int) (var3 TSLL) (var4 HeapObject) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Addr)) (or (not (and (_Glue16 var8 var7 var6 var5 var4) (and (and (and (and (= (getTSLL var4) var3) (= (|TSLL::colour| var3) var2)) (= (TSLL var8 var2) var1)) (= (O_TSLL var1) var0)) (valid var6 var5)))) (Inv_Heap var5 var0))))
(assert (forall ((var0 HeapObject) (var1 TSLL) (var2 Int) (var3 TSLL) (var4 Heap) (var5 HeapObject) (var6 Heap) (var7 Addr) (var8 Addr) (var9 HeapObject) (var10 Addr)) (or (not (and (and (Inv_Heap var10 var9) (_Glue16 var8 var7 var6 var10 var5)) (and (and (and (and (and (and (and (= (read var4 var10) var9) (valid var4 var10)) true) (= (getTSLL var5) var3)) (= (|TSLL::colour| var3) var2)) (= (TSLL var8 var2) var1)) (= (O_TSLL var1) var0)) (= (write var6 var10 var0) var4)))) (_Glue18 var4 var7 var10 var9))))
(assert (forall ((var0 HeapObject) (var1 TSLL) (var2 Int) (var3 TSLL) (var4 HeapObject) (var5 Heap) (var6 HeapObject) (var7 Addr) (var8 Heap) (var9 Addr) (var10 Addr)) (or (not (and (_Glue16 var10 var9 var8 var7 var6) (and (and (and (and (and (and (= (read var5 var7) var4) (not (valid var5 var7))) (= (getTSLL var6) var3)) (= (|TSLL::colour| var3) var2)) (= (TSLL var10 var2) var1)) (= (O_TSLL var1) var0)) (= (write var8 var7 var0) var5)))) (_Glue18 var5 var9 var7 var4))))
(assert (forall ((var0 HeapObject) (var1 TSLL) (var2 Addr) (var3 TSLL) (var4 HeapObject) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (_Glue18 var7 var6 var5 var4) (and (and (and (and (= (getTSLL var4) var3) (= (|TSLL::next| var3) var2)) (= (TSLL var2 1) var1)) (= (O_TSLL var1) var0)) (valid var7 var5)))) (Inv_Heap var5 var0))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 TSLL) (var3 Addr) (var4 TSLL) (var5 HeapObject) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (_Glue18 var8 var7 var6 var5) (and (and (and (and (= (getTSLL var5) var4) (= (|TSLL::next| var4) var3)) (= (TSLL var3 1) var2)) (= (O_TSLL var2) var1)) (= (write var8 var6 var1) var0)))) (inv_main1010_2 var0 var7 var6))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (and (inv_main_17 var2 var1 var0) (= nullAddr var0))) (inv_main_20 var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 HeapObject) (var4 Addr)) (or (not (and (and (Inv_Heap var4 var3) (inv_main_20 var2 var4)) (and (and (and (= nullAddr var1) (not (= var1 var4))) (= (read var2 var4) var3)) (valid var2 var4)))) (_Glue2 var0 var2 var4 var3))))
(assert (forall ((var0 Addr) (var1 HeapObject) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main_20 var4 var3) (and (and (and (= nullAddr var2) (not (= var2 var3))) (= (read var4 var3) var1)) (not (valid var4 var3))))) (_Glue2 var0 var4 var3 var1))))
(assert (forall ((var0 HeapObject) (var1 Int) (var2 TSLL) (var3 HeapObject) (var4 Addr) (var5 Heap) (var6 Addr)) (or (not (and (_Glue2 var6 var5 var4 var3) (and (and (and (and (and (= (getTSLL var3) var2) (= (|TSLL::next| var2) var6)) (= (|TSLL::colour| var2) var1)) (not (= 0 var1))) (= defObj var0)) (valid var5 var4)))) (Inv_Heap var4 var0))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 Int) (var3 TSLL) (var4 HeapObject) (var5 Addr) (var6 Heap) (var7 Addr)) (or (not (and (_Glue2 var7 var6 var5 var4) (and (and (and (and (and (= (getTSLL var4) var3) (= (|TSLL::next| var3) var7)) (= (|TSLL::colour| var3) var2)) (not (= 0 var2))) (= defObj var1)) (= (write var6 var5 var1) var0)))) (inv_main_20 var0 var7))))
(assert (forall ((var0 Addr) (var1 TSLL) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap) (var6 HeapObject) (var7 Addr)) (or (not (and (and (Inv_Heap var7 var6) (inv_main_17 var5 var4 var7)) (and (and (and (and (and (and (and (not (= var3 var7)) (not (= 0 var2))) (= nullAddr var3)) (= (read var5 var7) var6)) (= (getTSLL var6) var1)) (= (|TSLL::colour| var1) var2)) (= (|TSLL::next| var1) var0)) (valid var5 var7)))) (inv_main_17 var5 var4 var0))))
(assert (forall ((var0 Addr) (var1 TSLL) (var2 HeapObject) (var3 Int) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main_17 var7 var6 var5) (and (and (and (and (and (and (and (not (= var4 var5)) (not (= 0 var3))) (= nullAddr var4)) (= (read var7 var5) var2)) (= (getTSLL var2) var1)) (= (|TSLL::colour| var1) var3)) (= (|TSLL::next| var1) var0)) (not (valid var7 var5))))) (inv_main_17 var7 var6 var0))))
(assert (forall ((var0 Addr) (var1 TSLL) (var2 Addr) (var3 Addr) (var4 Heap) (var5 HeapObject) (var6 Addr)) (or (not (and (and (Inv_Heap var6 var5) (inv_main1010_2 var4 var6 var3)) (and (and (and (and (and (and (not (= var2 var6)) (= nullAddr var2)) (= (read var4 var6) var5)) (= (getTSLL var5) var1)) (= (|TSLL::colour| var1) 1)) (valid var4 var6)) (= var0 var6)))) (inv_main_17 var4 var0 var6))))
(assert (forall ((var0 Addr) (var1 TSLL) (var2 HeapObject) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main1010_2 var6 var5 var4) (and (and (and (and (and (and (not (= var3 var5)) (= nullAddr var3)) (= (read var6 var5) var2)) (= (getTSLL var2) var1)) (= (|TSLL::colour| var1) 1)) (not (valid var6 var5))) (= var0 var5)))) (inv_main_17 var6 var0 var5))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 HeapObject) (var3 Addr)) (or (not (and (and (Inv_Heap var3 var2) (inv_main_20 var1 var3)) (and (and (and (= nullAddr var0) (not (= var0 var3))) (= (read var1 var3) var2)) (valid var1 var3)))) (_Glue19 var1 var3 var2))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main_20 var3 var2) (and (and (and (= nullAddr var1) (not (= var1 var2))) (= (read var3 var2) var0)) (not (valid var3 var2))))) (_Glue19 var3 var2 var0))))
(assert (forall ((var0 HeapObject) (var1 TSLL) (var2 HeapObject) (var3 Addr) (var4 Heap)) (or (not (and (_Glue19 var4 var3 var2) (and (and (and (= (getTSLL var2) var1) (= (|TSLL::colour| var1) 0)) (= defObj var0)) (valid var4 var3)))) (Inv_Heap var3 var0))))
(assert (forall ((var0 HeapObject) (var1 TSLL) (var2 Heap) (var3 HeapObject) (var4 Addr) (var5 Heap) (var6 HeapObject) (var7 Addr)) (or (not (and (and (Inv_Heap var7 var6) (_Glue19 var5 var4 var3)) (and (and (and (and (and (and (and (= (read var2 var7) var6) (valid var2 var7)) true) (= (getTSLL var3) var1)) (= (|TSLL::colour| var1) 0)) (= (|TSLL::next| var1) var7)) (= defObj var0)) (= (write var5 var4 var0) var2)))) (_Glue21_exp var2 var7 var6))))
(assert (forall ((var0 HeapObject) (var1 TSLL) (var2 HeapObject) (var3 Addr) (var4 Heap) (var5 HeapObject) (var6 Addr) (var7 Heap)) (or (not (and (_Glue19 var7 var6 var5) (and (and (and (and (and (and (= (read var4 var3) var2) (not (valid var4 var3))) (= (getTSLL var5) var1)) (= (|TSLL::colour| var1) 0)) (= (|TSLL::next| var1) var3)) (= defObj var0)) (= (write var7 var6 var0) var4)))) (_Glue21_exp var4 var3 var2))))
(assert (forall ((var0 HeapObject) (var1 HeapObject) (var2 Addr) (var3 Heap)) (or (not (and (_Glue21_exp var3 var2 var1) (and (valid var3 var2) (= defObj var0)))) (Inv_Heap var2 var0))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 Addr) (var3 TSLL) (var4 HeapObject) (var5 Addr) (var6 Heap)) (or (not (and (_Glue21_exp var6 var5 var4) (and (and (and (= (getTSLL var4) var3) (= (|TSLL::next| var3) var2)) (= (write var6 var5 var1) var0)) (= defObj var1)))) (inv_main_20 var0 var2))))
(assert (forall ((var0 AllocResHeap) (var1 HeapObject) (var2 TSLL) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main1010_2 var5 var4 var3) (and (= (O_TSLL var2) var1) (= (alloc var5 var1) var0)))) (Inv_Heap (newAddr var0) var1))))
(assert (forall ((var0 AllocResHeap) (var1 Addr) (var2 HeapObject) (var3 TSLL) (var4 Heap) (var5 Addr) (var6 Heap) (var7 HeapObject) (var8 Addr)) (or (not (and (and (Inv_Heap var8 var7) (inv_main1010_2 var6 var5 var8)) (and (and (and (and (and (= (read var4 var8) var7) (valid var4 var8)) true) (= (O_TSLL var3) var2)) (= (AllocResHeap var4 var1) var0)) (= (alloc var6 var2) var0)))) (_Glue28 var8 var5 var1 var4 var7))))
(assert (forall ((var0 AllocResHeap) (var1 Addr) (var2 HeapObject) (var3 TSLL) (var4 HeapObject) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main1010_2 var8 var7 var6) (and (and (and (and (= (read var5 var6) var4) (not (valid var5 var6))) (= (O_TSLL var3) var2)) (= (AllocResHeap var5 var1) var0)) (= (alloc var8 var2) var0)))) (_Glue28 var6 var7 var1 var5 var4))))
(assert (forall ((var0 HeapObject) (var1 TSLL) (var2 Int) (var3 TSLL) (var4 HeapObject) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr)) (or (not (and (_Glue28 var8 var7 var6 var5 var4) (and (and (and (and (= (getTSLL var4) var3) (= (|TSLL::colour| var3) var2)) (= (TSLL var6 var2) var1)) (= (O_TSLL var1) var0)) (valid var5 var8)))) (Inv_Heap var8 var0))))
(assert (forall ((var0 HeapObject) (var1 TSLL) (var2 Int) (var3 TSLL) (var4 Heap) (var5 HeapObject) (var6 Heap) (var7 Addr) (var8 Addr) (var9 HeapObject) (var10 Addr)) (or (not (and (and (Inv_Heap var10 var9) (_Glue28 var10 var8 var7 var6 var5)) (and (and (and (and (and (and (and (= (read var4 var10) var9) (valid var4 var10)) true) (= (getTSLL var5) var3)) (= (|TSLL::colour| var3) var2)) (= (TSLL var7 var2) var1)) (= (O_TSLL var1) var0)) (= (write var6 var10 var0) var4)))) (_Glue30 var4 var8 var9))))
(assert (forall ((var0 HeapObject) (var1 TSLL) (var2 Int) (var3 TSLL) (var4 HeapObject) (var5 Heap) (var6 HeapObject) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Addr)) (or (not (and (_Glue28 var10 var9 var8 var7 var6) (and (and (and (and (and (and (= (read var5 var10) var4) (not (valid var5 var10))) (= (getTSLL var6) var3)) (= (|TSLL::colour| var3) var2)) (= (TSLL var8 var2) var1)) (= (O_TSLL var1) var0)) (= (write var7 var10 var0) var5)))) (_Glue30 var5 var9 var4))))
(assert (forall ((var0 TSLL) (var1 HeapObject) (var2 Addr) (var3 Heap) (var4 HeapObject) (var5 Addr)) (or (not (and (and (Inv_Heap var5 var4) (_Glue30 var3 var2 var1)) (and (and (and (= (getTSLL var1) var0) (= (|TSLL::next| var0) var5)) (= (read var3 var5) var4)) (valid var3 var5)))) (_Glue31 var2 var3 var5 var4))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 TSLL) (var3 HeapObject) (var4 Addr) (var5 Heap)) (or (not (and (_Glue30 var5 var4 var3) (and (and (and (= (getTSLL var3) var2) (= (|TSLL::next| var2) var1)) (= (read var5 var1) var0)) (not (valid var5 var1))))) (_Glue31 var4 var5 var1 var0))))
(assert (forall ((var0 HeapObject) (var1 TSLL) (var2 Addr) (var3 Int) (var4 TSLL) (var5 HeapObject) (var6 Addr) (var7 Heap) (var8 Addr)) (or (not (and (_Glue31 var8 var7 var6 var5) (and (and (and (and (and (= (getTSLL var5) var4) (= (|TSLL::colour| var4) var3)) (= nullAddr var2)) (= (TSLL var2 var3) var1)) (= (O_TSLL var1) var0)) (valid var7 var6)))) (Inv_Heap var6 var0))))
(assert (forall ((var0 HeapObject) (var1 TSLL) (var2 Addr) (var3 Int) (var4 TSLL) (var5 Heap) (var6 HeapObject) (var7 Heap) (var8 Addr) (var9 HeapObject) (var10 Addr)) (or (not (and (and (Inv_Heap var10 var9) (_Glue31 var8 var7 var10 var6)) (and (and (and (and (and (and (and (and (= (read var5 var10) var9) (valid var5 var10)) true) (= (getTSLL var6) var4)) (= (|TSLL::colour| var4) var3)) (= nullAddr var2)) (= (TSLL var2 var3) var1)) (= (O_TSLL var1) var0)) (= (write var7 var10 var0) var5)))) (_Glue33 var5 var8 var10 var9))))
(assert (forall ((var0 HeapObject) (var1 TSLL) (var2 Addr) (var3 Int) (var4 TSLL) (var5 HeapObject) (var6 Heap) (var7 HeapObject) (var8 Addr) (var9 Heap) (var10 Addr)) (or (not (and (_Glue31 var10 var9 var8 var7) (and (and (and (and (and (and (and (= (read var6 var8) var5) (not (valid var6 var8))) (= (getTSLL var7) var4)) (= (|TSLL::colour| var4) var3)) (= nullAddr var2)) (= (TSLL var2 var3) var1)) (= (O_TSLL var1) var0)) (= (write var9 var8 var0) var6)))) (_Glue33 var6 var10 var8 var5))))
(assert (forall ((var0 HeapObject) (var1 TSLL) (var2 Addr) (var3 TSLL) (var4 HeapObject) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (_Glue33 var7 var6 var5 var4) (and (and (and (and (= (getTSLL var4) var3) (= (|TSLL::next| var3) var2)) (= (TSLL var2 1) var1)) (= (O_TSLL var1) var0)) (valid var7 var5)))) (Inv_Heap var5 var0))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 TSLL) (var3 Addr) (var4 TSLL) (var5 HeapObject) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (_Glue33 var8 var7 var6 var5) (and (and (and (and (= (getTSLL var5) var4) (= (|TSLL::next| var4) var3)) (= (TSLL var3 1) var2)) (= (O_TSLL var2) var1)) (= (write var8 var6 var1) var0)))) (inv_main1010_2 var0 var7 var6))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 HeapObject) (var4 Addr)) (or (not (and (and (Inv_Heap var4 var3) (inv_main_17 var2 var1 var4)) (and (and (and (= nullAddr var0) (not (= var0 var4))) (= (read var2 var4) var3)) (valid var2 var4)))) (_Glue3 var0 var1 var2 var3))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main_17 var4 var3 var2) (and (and (and (= nullAddr var1) (not (= var1 var2))) (= (read var4 var2) var0)) (not (valid var4 var2))))) (_Glue3 var1 var3 var4 var0))))
(assert (forall ((var0 Addr) (var1 TSLL) (var2 TSLL) (var3 HeapObject) (var4 Heap) (var5 Addr) (var6 Addr) (var7 HeapObject) (var8 Addr)) (or (not (and (and (Inv_Heap var8 var7) (_Glue3 var6 var5 var4 var3)) (and (and (and (and (and (and (and (and (= (getTSLL var3) var2) (= (|TSLL::colour| var2) 0)) (= (|TSLL::next| var2) var8)) (not (= var6 var8))) (= (read var4 var8) var7)) (= (getTSLL var7) var1)) (= (|TSLL::colour| var1) 1)) (= (|TSLL::next| var1) var0)) (valid var4 var8)))) (inv_main_17 var4 var5 var0))))
(assert (forall ((var0 Addr) (var1 TSLL) (var2 HeapObject) (var3 Addr) (var4 TSLL) (var5 HeapObject) (var6 Heap) (var7 Addr) (var8 Addr)) (or (not (and (_Glue3 var8 var7 var6 var5) (and (and (and (and (and (and (and (and (= (getTSLL var5) var4) (= (|TSLL::colour| var4) 0)) (= (|TSLL::next| var4) var3)) (not (= var8 var3))) (= (read var6 var3) var2)) (= (getTSLL var2) var1)) (= (|TSLL::colour| var1) 1)) (= (|TSLL::next| var1) var0)) (not (valid var6 var3))))) (inv_main_17 var6 var7 var0))))
(assert (forall ((var0 TSLL) (var1 Addr) (var2 Heap) (var3 HeapObject) (var4 Addr)) (not (and (and (Inv_Heap var4 var3) (inv_main_20 var2 var4)) (and (and (and (and (and (and (and (= defObj var3) (= (read var2 var4) var3)) (= nullAddr var1)) (= (getTSLL var3) var0)) (= (|TSLL::colour| var0) 0)) (not (= var4 var1))) (not (= var1 var4))) (valid var2 var4))))))
(assert (forall ((var0 TSLL) (var1 Addr) (var2 HeapObject) (var3 Addr) (var4 Heap)) (not (and (inv_main_20 var4 var3) (and (and (and (and (and (and (and (= defObj var2) (= (read var4 var3) var2)) (= nullAddr var1)) (= (getTSLL var2) var0)) (= (|TSLL::colour| var0) 0)) (not (= var3 var1))) (not (= var1 var3))) (not (valid var4 var3)))))))
(assert (forall ((var0 AllocResHeap) (var1 Heap) (var2 HeapObject) (var3 TSLL)) (or (not (and (and (= (O_TSLL var3) var2) (= (alloc var1 var2) var0)) (= emptyHeap var1))) (Inv_Heap (newAddr var0) var2))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 HeapObject) (var3 TSLL) (var4 AllocResHeap) (var5 Heap) (var6 HeapObject) (var7 Addr)) (or (not (and (Inv_Heap var7 var6) (and (and (and (and (and (and (= (read var5 var7) var6) (valid var5 var7)) (= (AllocResHeap var5 var7) var4)) (= (O_TSLL var3) var2)) (= (alloc var1 var2) var4)) (= nullAddr var0)) (= emptyHeap var1)))) (_Glue24 var7 var0 var5 var6))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 HeapObject) (var3 TSLL) (var4 AllocResHeap) (var5 HeapObject) (var6 Addr) (var7 Heap)) (or (not (and (and (and (and (and (and (= (read var7 var6) var5) (not (valid var7 var6))) (= (AllocResHeap var7 var6) var4)) (= (O_TSLL var3) var2)) (= (alloc var1 var2) var4)) (= nullAddr var0)) (= emptyHeap var1))) (_Glue24 var6 var0 var7 var5))))
(assert (forall ((var0 HeapObject) (var1 TSLL) (var2 Int) (var3 TSLL) (var4 HeapObject) (var5 Heap) (var6 Addr) (var7 Addr)) (or (not (and (_Glue24 var7 var6 var5 var4) (and (and (and (and (= (getTSLL var4) var3) (= (|TSLL::colour| var3) var2)) (= (TSLL var6 var2) var1)) (= (O_TSLL var1) var0)) (valid var5 var7)))) (Inv_Heap var7 var0))))
(assert (forall ((var0 HeapObject) (var1 TSLL) (var2 Int) (var3 TSLL) (var4 Heap) (var5 HeapObject) (var6 Heap) (var7 Addr) (var8 HeapObject) (var9 Addr)) (or (not (and (and (Inv_Heap var9 var8) (_Glue24 var9 var7 var6 var5)) (and (and (and (and (and (and (= (read var4 var9) var8) (valid var4 var9)) (= (getTSLL var5) var3)) (= (|TSLL::colour| var3) var2)) (= (TSLL var7 var2) var1)) (= (O_TSLL var1) var0)) (= (write var6 var9 var0) var4)))) (_Glue26 var4 var9 var8))))
(assert (forall ((var0 HeapObject) (var1 TSLL) (var2 Int) (var3 TSLL) (var4 HeapObject) (var5 Heap) (var6 HeapObject) (var7 Heap) (var8 Addr) (var9 Addr)) (or (not (and (_Glue24 var9 var8 var7 var6) (and (and (and (and (and (and (= (read var5 var9) var4) (not (valid var5 var9))) (= (getTSLL var6) var3)) (= (|TSLL::colour| var3) var2)) (= (TSLL var8 var2) var1)) (= (O_TSLL var1) var0)) (= (write var7 var9 var0) var5)))) (_Glue26 var5 var9 var4))))
(assert (forall ((var0 HeapObject) (var1 TSLL) (var2 Addr) (var3 TSLL) (var4 HeapObject) (var5 Addr) (var6 Heap)) (or (not (and (_Glue26 var6 var5 var4) (and (and (and (and (= (getTSLL var4) var3) (= (|TSLL::next| var3) var2)) (= (TSLL var2 1) var1)) (= (O_TSLL var1) var0)) (valid var6 var5)))) (Inv_Heap var5 var0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 HeapObject) (var3 TSLL) (var4 Addr) (var5 TSLL) (var6 HeapObject) (var7 Addr) (var8 Heap)) (or (not (and (_Glue26 var8 var7 var6) (and (and (and (and (and (= (getTSLL var6) var5) (= (|TSLL::next| var5) var4)) (= (TSLL var4 1) var3)) (= (O_TSLL var3) var2)) (= (write var8 var7 var2) var1)) (= var0 var7)))) (inv_main1010_2 var1 var7 var0))))
(check-sat)
