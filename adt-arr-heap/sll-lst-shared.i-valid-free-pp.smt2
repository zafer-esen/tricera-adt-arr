(set-logic HORN)
(set-info :source |
    Benchmark: 
    Output by Princess (http://www.philipp.ruemmer.org/princess.shtml)
|)
(declare-heap Heap Addr HeapObject
 defObj
 ((HeapObject 0) (sll 0)) (
  (
   (O_Int (getInt Int))
   (O_UInt (getUInt Int))
   (O_Addr (getAddr Addr))
   (O_AddrRange (getAddrRange AddrRange))
   (O_sll (getsll sll))
   (defObj)
  )
  (
   (sll (|sll::data| Addr) (|sll::next| Addr))
  )
))
(declare-fun inv_main_2 (Heap Addr Addr Addr) Bool)
(declare-fun _Glue7 (Heap Addr Addr Addr HeapObject) Bool)
(declare-fun _Glue8 (Addr Addr Addr Heap Addr HeapObject) Bool)
(declare-fun _Glue5 (Heap Addr Addr Addr Addr HeapObject) Bool)
(declare-fun _Glue12_exp (Addr Int Int Addr Heap HeapObject) Bool)
(declare-fun _Glue18_exp (Addr Heap Addr HeapObject) Bool)
(declare-fun inv_main2439_5 (Heap Addr Addr) Bool)
(declare-fun inv_main2431_9 (Heap Addr Addr) Bool)
(declare-fun _Glue0 (Addr Heap Addr HeapObject) Bool)
(declare-fun Inv_Heap (Addr HeapObject) Bool)
(declare-fun _Glue3 (Addr Addr Addr Addr Heap HeapObject) Bool)
(declare-fun _Glue16 (Heap Addr Addr HeapObject) Bool)
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main2431_9 var4 var3 var2) (and (and (and (= nullAddr var1) (not (= var2 var1))) (= defObj var0)) (valid var4 var3)))) (Inv_Heap var3 var0))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 sll) (var4 Heap) (var5 Addr) (var6 Heap) (var7 HeapObject) (var8 Addr)) (or (not (and (and (Inv_Heap var8 var7) (inv_main2431_9 var6 var5 var8)) (and (and (and (and (and (and (and (and (= (read var4 var8) var7) (= (getsll var7) var3)) (= (|sll::next| var3) var2)) (valid var4 var8)) true) (= nullAddr var1)) (not (= var8 var1))) (= defObj var0)) (= (write var6 var5 var0) var4)))) (inv_main2431_9 var4 var8 var2))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 sll) (var4 HeapObject) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main2431_9 var8 var7 var6) (and (and (and (and (and (and (and (= (read var5 var6) var4) (= (getsll var4) var3)) (= (|sll::next| var3) var2)) (not (valid var5 var6))) (= nullAddr var1)) (not (= var6 var1))) (= defObj var0)) (= (write var8 var7 var0) var5)))) (inv_main2431_9 var5 var6 var2))))
(assert (forall ((var0 AllocResHeap) (var1 HeapObject) (var2 sll) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main_2 var6 var5 var4 var3) (and (= (O_sll var2) var1) (= (alloc var6 var1) var0)))) (Inv_Heap (newAddr var0) var1))))
(assert (forall ((var0 AllocResHeap) (var1 HeapObject) (var2 sll) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap) (var8 HeapObject) (var9 Addr)) (or (not (and (and (Inv_Heap var9 var8) (inv_main_2 var7 var6 var5 var4)) (and (and (and (and (and (= (read var3 var9) var8) (valid var3 var9)) true) (= (O_sll var2) var1)) (= (AllocResHeap var3 var9) var0)) (= (alloc var7 var1) var0)))) (_Glue3 var4 var5 var6 var9 var3 var8))))
(assert (forall ((var0 AllocResHeap) (var1 HeapObject) (var2 sll) (var3 HeapObject) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main_2 var9 var8 var7 var6) (and (and (and (and (= (read var5 var4) var3) (not (valid var5 var4))) (= (O_sll var2) var1)) (= (AllocResHeap var5 var4) var0)) (= (alloc var9 var1) var0)))) (_Glue3 var6 var7 var8 var4 var5 var3))))
(assert (forall ((var0 HeapObject) (var1 sll) (var2 Addr) (var3 Addr) (var4 sll) (var5 HeapObject) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr)) (or (not (and (_Glue3 var10 var9 var8 var7 var6 var5) (and (and (and (and (and (= (getsll var5) var4) (= (|sll::data| var4) var3)) (= nullAddr var2)) (= (sll var3 var2) var1)) (= (O_sll var1) var0)) (valid var6 var7)))) (Inv_Heap var7 var0))))
(assert (forall ((var0 HeapObject) (var1 sll) (var2 Addr) (var3 Addr) (var4 sll) (var5 Heap) (var6 HeapObject) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Addr) (var11 HeapObject) (var12 Addr)) (or (not (and (and (Inv_Heap var12 var11) (_Glue3 var10 var12 var9 var8 var7 var6)) (and (and (and (and (and (and (and (and (= (read var5 var12) var11) (valid var5 var12)) true) (= (getsll var6) var4)) (= (|sll::data| var4) var3)) (= nullAddr var2)) (= (sll var3 var2) var1)) (= (O_sll var1) var0)) (= (write var7 var8 var0) var5)))) (_Glue5 var5 var10 var12 var9 var8 var11))))
(assert (forall ((var0 HeapObject) (var1 sll) (var2 Addr) (var3 Addr) (var4 sll) (var5 HeapObject) (var6 Heap) (var7 HeapObject) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr)) (or (not (and (_Glue3 var12 var11 var10 var9 var8 var7) (and (and (and (and (and (and (and (= (read var6 var11) var5) (not (valid var6 var11))) (= (getsll var7) var4)) (= (|sll::data| var4) var3)) (= nullAddr var2)) (= (sll var3 var2) var1)) (= (O_sll var1) var0)) (= (write var8 var9 var0) var6)))) (_Glue5 var6 var12 var11 var10 var9 var5))))
(assert (forall ((var0 HeapObject) (var1 sll) (var2 Addr) (var3 sll) (var4 HeapObject) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (_Glue5 var9 var8 var7 var6 var5 var4) (and (and (and (and (= (getsll var4) var3) (= (|sll::data| var3) var2)) (= (sll var2 var5) var1)) (= (O_sll var1) var0)) (valid var9 var7)))) (Inv_Heap var7 var0))))
(assert (forall ((var0 HeapObject) (var1 sll) (var2 Addr) (var3 sll) (var4 Heap) (var5 HeapObject) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap) (var10 HeapObject) (var11 Addr)) (or (not (and (and (Inv_Heap var11 var10) (_Glue5 var9 var8 var11 var7 var6 var5)) (and (and (and (and (and (and (and (= (read var4 var11) var10) (valid var4 var11)) true) (= (getsll var5) var3)) (= (|sll::data| var3) var2)) (= (sll var2 var6) var1)) (= (O_sll var1) var0)) (= (write var9 var11 var0) var4)))) (_Glue7 var4 var8 var11 var7 var10))))
(assert (forall ((var0 HeapObject) (var1 sll) (var2 Addr) (var3 sll) (var4 HeapObject) (var5 Heap) (var6 HeapObject) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Heap)) (or (not (and (_Glue5 var11 var10 var9 var8 var7 var6) (and (and (and (and (and (and (= (read var5 var9) var4) (not (valid var5 var9))) (= (getsll var6) var3)) (= (|sll::data| var3) var2)) (= (sll var2 var7) var1)) (= (O_sll var1) var0)) (= (write var11 var9 var0) var5)))) (_Glue7 var5 var10 var9 var8 var4))))
(assert (forall ((var0 sll) (var1 HeapObject) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 HeapObject) (var7 Addr)) (or (not (and (and (Inv_Heap var7 var6) (_Glue7 var5 var4 var3 var2 var1)) (and (and (and (= (getsll var1) var0) (= (|sll::next| var0) var7)) (= (read var5 var7) var6)) (valid var5 var7)))) (_Glue8 var2 var3 var4 var5 var7 var6))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 sll) (var3 HeapObject) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (_Glue7 var7 var6 var5 var4 var3) (and (and (and (= (getsll var3) var2) (= (|sll::next| var2) var1)) (= (read var7 var1) var0)) (not (valid var7 var1))))) (_Glue8 var4 var5 var6 var7 var1 var0))))
(assert (forall ((var0 HeapObject) (var1 sll) (var2 Addr) (var3 sll) (var4 HeapObject) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Addr)) (or (not (and (_Glue8 var9 var8 var7 var6 var5 var4) (and (and (and (and (= (getsll var4) var3) (= (|sll::next| var3) var2)) (= (sll var7 var2) var1)) (= (O_sll var1) var0)) (valid var6 var5)))) (Inv_Heap var5 var0))))
(assert (forall ((var0 HeapObject) (var1 sll) (var2 Addr) (var3 sll) (var4 Addr) (var5 sll) (var6 Heap) (var7 HeapObject) (var8 Addr) (var9 Heap) (var10 Addr) (var11 Addr) (var12 HeapObject) (var13 Addr)) (or (not (and (and (Inv_Heap var13 var12) (_Glue8 var11 var13 var10 var9 var8 var7)) (and (and (and (and (and (and (and (and (and (= (read var6 var13) var12) (= (getsll var12) var5)) (= (|sll::next| var5) var4)) (valid var6 var13)) true) (= (getsll var7) var3)) (= (|sll::next| var3) var2)) (= (sll var10 var2) var1)) (= (O_sll var1) var0)) (= (write var9 var8 var0) var6)))) (inv_main_2 var6 var11 var4 var10))))
(assert (forall ((var0 HeapObject) (var1 sll) (var2 Addr) (var3 sll) (var4 Addr) (var5 sll) (var6 HeapObject) (var7 Heap) (var8 HeapObject) (var9 Addr) (var10 Heap) (var11 Addr) (var12 Addr) (var13 Addr)) (or (not (and (_Glue8 var13 var12 var11 var10 var9 var8) (and (and (and (and (and (and (and (and (= (read var7 var12) var6) (= (getsll var6) var5)) (= (|sll::next| var5) var4)) (not (valid var7 var12))) (= (getsll var8) var3)) (= (|sll::next| var3) var2)) (= (sll var11 var2) var1)) (= (O_sll var1) var0)) (= (write var10 var9 var0) var7)))) (inv_main_2 var7 var13 var4 var11))))
(assert (forall ((var0 Addr) (var1 sll) (var2 Addr) (var3 Addr) (var4 Heap) (var5 HeapObject) (var6 Addr)) (or (not (and (and (Inv_Heap var6 var5) (inv_main2439_5 var4 var3 var6)) (and (and (and (and (and (= nullAddr var2) (= (read var4 var6) var5)) (= (getsll var5) var1)) (= (|sll::next| var1) var0)) (not (= var6 var2))) (valid var4 var6)))) (inv_main2439_5 var4 var3 var0))))
(assert (forall ((var0 Addr) (var1 sll) (var2 HeapObject) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main2439_5 var6 var5 var4) (and (and (and (and (and (= nullAddr var3) (= (read var6 var4) var2)) (= (getsll var2) var1)) (= (|sll::next| var1) var0)) (not (= var4 var3))) (not (valid var6 var4))))) (inv_main2439_5 var6 var5 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main_2 var4 var3 var2 var1) (= var0 var3))) (inv_main2439_5 var4 var0 var3))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 HeapObject) (var3 Addr)) (or (not (and (and (Inv_Heap var3 var2) (inv_main2439_5 var1 var3 var0)) (and (and (= nullAddr var0) (= (read var1 var3) var2)) (valid var1 var3)))) (_Glue0 var0 var1 var3 var2))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main2439_5 var3 var2 var1) (and (and (= nullAddr var1) (= (read var3 var2) var0)) (not (valid var3 var2))))) (_Glue0 var1 var3 var2 var0))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 sll) (var3 HeapObject) (var4 Addr) (var5 Heap) (var6 Addr)) (or (not (and (_Glue0 var6 var5 var4 var3) (and (and (and (and (= (getsll var3) var2) (= (|sll::data| var2) var1)) (not (= var4 var6))) (= defObj var0)) (valid var5 var1)))) (Inv_Heap var1 var0))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 sll) (var3 Addr) (var4 sll) (var5 Heap) (var6 Addr) (var7 HeapObject) (var8 Heap) (var9 Addr) (var10 HeapObject) (var11 Addr)) (or (not (and (and (Inv_Heap var11 var10) (_Glue0 var9 var8 var11 var7)) (and (and (and (and (and (and (and (and (and (and (not (= var11 var6)) (= (read var5 var11) var10)) (= (getsll var10) var4)) (= (|sll::next| var4) var3)) (valid var5 var11)) true) (= (getsll var7) var2)) (= (|sll::data| var2) var1)) (not (= var11 var9))) (= defObj var0)) (= (write var8 var1 var0) var5)))) (inv_main2431_9 var5 var11 var3))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 sll) (var3 Addr) (var4 sll) (var5 HeapObject) (var6 Heap) (var7 Addr) (var8 HeapObject) (var9 Addr) (var10 Heap) (var11 Addr)) (or (not (and (_Glue0 var11 var10 var9 var8) (and (and (and (and (and (and (and (and (and (not (= var9 var7)) (= (read var6 var9) var5)) (= (getsll var5) var4)) (= (|sll::next| var4) var3)) (not (valid var6 var9))) (= (getsll var8) var2)) (= (|sll::data| var2) var1)) (not (= var9 var11))) (= defObj var0)) (= (write var10 var1 var0) var6)))) (inv_main2431_9 var6 var9 var3))))
(assert (forall ((var0 AllocResHeap) (var1 Heap) (var2 HeapObject) (var3 sll)) (or (not (and (and (= (O_sll var3) var2) (= (alloc var1 var2) var0)) (= emptyHeap var1))) (Inv_Heap (newAddr var0) var2))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Heap) (var4 HeapObject) (var5 sll) (var6 AllocResHeap) (var7 Heap) (var8 HeapObject) (var9 Addr)) (or (not (and (Inv_Heap var9 var8) (and (and (and (and (and (and (= (read var7 var9) var8) (valid var7 var9)) (= (AllocResHeap var7 var9) var6)) (= (O_sll var5) var4)) (= (alloc var3 var4) var6)) (= nullAddr var2)) (= emptyHeap var3)))) (_Glue12_exp var9 var1 var0 var2 var7 var8))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Heap) (var4 HeapObject) (var5 sll) (var6 AllocResHeap) (var7 HeapObject) (var8 Addr) (var9 Heap)) (or (not (and (and (and (and (and (and (= (read var9 var8) var7) (not (valid var9 var8))) (= (AllocResHeap var9 var8) var6)) (= (O_sll var5) var4)) (= (alloc var3 var4) var6)) (= nullAddr var2)) (= emptyHeap var3))) (_Glue12_exp var8 var1 var0 var2 var9 var7))))
(assert (forall ((var0 sll) (var1 HeapObject) (var2 sll) (var3 Addr) (var4 HeapObject) (var5 Heap) (var6 Addr) (var7 Int) (var8 Int) (var9 Addr)) (or (not (and (_Glue12_exp var9 var8 var7 var6 var5 var4) (and (and (and (and (= (sll var3 var6) var2) (= (O_sll var2) var1)) (= (getsll var4) var0)) (= (|sll::data| var0) var3)) (valid var5 var9)))) (Inv_Heap var9 var1))))
(assert (forall ((var0 sll) (var1 HeapObject) (var2 sll) (var3 Addr) (var4 AllocResHeap) (var5 Heap) (var6 HeapObject) (var7 HeapObject) (var8 Heap) (var9 Addr) (var10 Int) (var11 Int) (var12 Addr)) (or (not (and (_Glue12_exp var12 var11 var10 var9 var8 var7) (and (and (and (and (and (and (= (O_Int var10) var6) (= (alloc var5 var6) var4)) (= (sll var3 var9) var2)) (= (O_sll var2) var1)) (= (getsll var7) var0)) (= (|sll::data| var0) var3)) (= (write var8 var12 var1) var5)))) (Inv_Heap (newAddr var4) var6))))
(assert (forall ((var0 sll) (var1 HeapObject) (var2 sll) (var3 Addr) (var4 Heap) (var5 HeapObject) (var6 AllocResHeap) (var7 Addr) (var8 Heap) (var9 HeapObject) (var10 HeapObject) (var11 Heap) (var12 Addr) (var13 Int) (var14 Int) (var15 Addr)) (or (not (and (_Glue12_exp var15 var14 var13 var12 var11 var10) (and (and (and (and (and (and (and (and (and (= (O_Int var14) var9) (valid var8 var7)) (= (AllocResHeap var8 var7) var6)) (= (O_Int var13) var5)) (= (alloc var4 var5) var6)) (= (sll var3 var12) var2)) (= (O_sll var2) var1)) (= (getsll var10) var0)) (= (|sll::data| var0) var3)) (= (write var11 var15 var1) var4)))) (Inv_Heap var7 var9))))
(assert (forall ((var0 sll) (var1 HeapObject) (var2 sll) (var3 Addr) (var4 Heap) (var5 HeapObject) (var6 AllocResHeap) (var7 Addr) (var8 Heap) (var9 HeapObject) (var10 Heap) (var11 HeapObject) (var12 Heap) (var13 Addr) (var14 Int) (var15 Int) (var16 HeapObject) (var17 Addr)) (or (not (and (and (Inv_Heap var17 var16) (_Glue12_exp var17 var15 var14 var13 var12 var11)) (and (and (and (and (and (and (and (and (and (and (and (= (read var10 var17) var16) (valid var10 var17)) (= (O_Int var15) var9)) (= (write var8 var7 var9) var10)) (= (AllocResHeap var8 var7) var6)) (= (O_Int var14) var5)) (= (alloc var4 var5) var6)) (= (sll var3 var13) var2)) (= (O_sll var2) var1)) (= (getsll var11) var0)) (= (|sll::data| var0) var3)) (= (write var12 var17 var1) var4)))) (_Glue16 var10 var7 var17 var16))))
(assert (forall ((var0 sll) (var1 HeapObject) (var2 sll) (var3 Addr) (var4 Heap) (var5 HeapObject) (var6 AllocResHeap) (var7 Addr) (var8 Heap) (var9 HeapObject) (var10 HeapObject) (var11 Heap) (var12 HeapObject) (var13 Heap) (var14 Addr) (var15 Int) (var16 Int) (var17 Addr)) (or (not (and (_Glue12_exp var17 var16 var15 var14 var13 var12) (and (and (and (and (and (and (and (and (and (and (and (= (read var11 var17) var10) (not (valid var11 var17))) (= (O_Int var16) var9)) (= (write var8 var7 var9) var11)) (= (AllocResHeap var8 var7) var6)) (= (O_Int var15) var5)) (= (alloc var4 var5) var6)) (= (sll var3 var14) var2)) (= (O_sll var2) var1)) (= (getsll var12) var0)) (= (|sll::data| var0) var3)) (= (write var13 var17 var1) var4)))) (_Glue16 var11 var7 var17 var10))))
(assert (forall ((var0 HeapObject) (var1 sll) (var2 Addr) (var3 sll) (var4 HeapObject) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (_Glue16 var7 var6 var5 var4) (and (and (and (and (= (getsll var4) var3) (= (|sll::next| var3) var2)) (= (sll var6 var2) var1)) (= (O_sll var1) var0)) (valid var7 var5)))) (Inv_Heap var5 var0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 HeapObject) (var3 sll) (var4 Addr) (var5 sll) (var6 HeapObject) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (_Glue16 var9 var8 var7 var6) (and (and (and (and (and (= (getsll var6) var5) (= (|sll::next| var5) var4)) (= (sll var8 var4) var3)) (= (O_sll var3) var2)) (= (write var9 var7 var2) var1)) (= var0 var7)))) (inv_main_2 var1 var7 var0 var8))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 HeapObject) (var4 Addr)) (not (and (and (Inv_Heap var4 var3) (inv_main2431_9 var2 var4 var1)) (and (and (and (and (not (= var4 var0)) (= (read var2 var4) var3)) (= defObj var3)) (= nullAddr var0)) (valid var2 var4))))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main2431_9 var4 var3 var2) (and (and (and (and (not (= var3 var1)) (= (read var4 var3) var0)) (= defObj var0)) (= nullAddr var1)) (not (valid var4 var3)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 HeapObject) (var3 Addr)) (or (not (and (and (Inv_Heap var3 var2) (inv_main2439_5 var1 var3 var0)) (and (and (= nullAddr var0) (= (read var1 var3) var2)) (valid var1 var3)))) (_Glue18_exp var0 var1 var3 var2))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main2439_5 var3 var2 var1) (and (and (= nullAddr var1) (= (read var3 var2) var0)) (not (valid var3 var2))))) (_Glue18_exp var1 var3 var2 var0))))
(assert (forall ((var0 sll) (var1 HeapObject) (var2 Addr) (var3 Heap) (var4 Addr) (var5 HeapObject) (var6 Addr)) (not (and (and (Inv_Heap var6 var5) (_Glue18_exp var4 var3 var2 var1)) (and (and (and (and (and (and (= (getsll var1) var0) (= (|sll::data| var0) var6)) (= (read var3 var6) var5)) (not (= var2 var4))) (not (= var6 var4))) (valid var3 var6)) (= defObj var5))))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 sll) (var3 HeapObject) (var4 Addr) (var5 Heap) (var6 Addr)) (not (and (_Glue18_exp var6 var5 var4 var3) (and (and (and (and (and (and (= (getsll var3) var2) (= (|sll::data| var2) var1)) (= (read var5 var1) var0)) (not (= var4 var6))) (not (= var1 var6))) (not (valid var5 var1))) (= defObj var0))))))
(check-sat)
