(set-logic HORN)
(set-info :source |
    Benchmark: 
    Output by Princess (http://www.philipp.ruemmer.org/princess.shtml)
|)
(declare-heap Heap Addr HeapObject
 defObj
 ((HeapObject 0)) (
  (
   (O_Int (getInt Int))
   (O_UInt (getUInt Int))
   (O_Addr (getAddr Addr))
   (O_AddrRange (getAddrRange AddrRange))
   (defObj)
  )
))
(declare-fun rec15_9 (Heap Addr Heap Int) Bool)
(declare-fun Inv_Heap (Addr HeapObject) Bool)
(declare-fun _Glue1_exp (Addr Int Int Int Int Heap Addr) Bool)
(declare-fun _Glue5 (Addr Heap Int Heap HeapObject) Bool)
(declare-fun _Glue4 (Addr Heap HeapObject) Bool)
(declare-fun _Glue0 (Heap Addr HeapObject) Bool)
(declare-fun rec_pre (Heap Addr) Bool)
(declare-fun inv_main23_8 (Heap Int Addr) Bool)
(assert (forall ((var0 Int) (var1 Heap) (var2 Heap) (var3 Heap) (var4 HeapObject) (var5 Addr)) (or (not (and (and (and (Inv_Heap var5 var4) (rec_pre var3 var5)) (rec15_9 var2 var5 var1 var0)) (and (= (read var3 var5) var4) (valid var3 var5)))) (_Glue5 var5 var3 var0 var2 var4))))
(assert (forall ((var0 HeapObject) (var1 Int) (var2 Heap) (var3 Heap) (var4 Addr) (var5 Heap)) (or (not (and (and (rec_pre var5 var4) (rec15_9 var3 var4 var2 var1)) (and (= (read var5 var4) var0) (not (valid var5 var4))))) (_Glue5 var4 var5 var1 var3 var0))))
(assert (forall ((var0 HeapObject) (var1 Int) (var2 Heap) (var3 HeapObject) (var4 Heap) (var5 Int) (var6 Heap) (var7 Addr)) (or (not (and (and (_Glue5 var7 var6 var5 var4 var3) (rec15_9 var4 var7 var2 var5)) (and (and (and (and (= (getInt var3) var1) (not (<= 0 (+ (- 1) (* (- 1) var1))))) (= (O_Int (+ var1 (- 1))) var0)) (= (write var6 var7 var0) var2)) (valid var6 var7)))) (Inv_Heap var7 var0))))
(assert (forall ((var0 HeapObject) (var1 Int) (var2 Heap) (var3 HeapObject) (var4 Heap) (var5 Int) (var6 Heap) (var7 Addr)) (or (not (and (and (_Glue5 var7 var6 var5 var4 var3) (rec15_9 var4 var7 var2 var5)) (and (and (and (= (getInt var3) var1) (not (<= 0 (+ (- 1) (* (- 1) var1))))) (= (O_Int (+ var1 (- 1))) var0)) (= (write var6 var7 var0) var2)))) (rec15_9 var4 var7 var6 var5))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Heap)) (or (not (inv_main23_8 var2 var1 var0)) (rec_pre var2 var0))))
(assert (forall ((var0 AllocResHeap) (var1 Heap) (var2 HeapObject) (var3 Int)) (or (not (and (and (= (O_Int var3) var2) (= (alloc var1 var2) var0)) (= emptyHeap var1))) (Inv_Heap (newAddr var0) var2))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 Int) (var3 AllocResHeap) (var4 Addr) (var5 Heap) (var6 HeapObject) (var7 Int)) (or (not (and (and (and (and (and (= (O_Int var7) var6) (valid var5 var4)) (= (AllocResHeap var5 var4) var3)) (= (O_Int var2) var1)) (= (alloc var0 var1) var3)) (= emptyHeap var0))) (Inv_Heap var4 var6))))
(assert (forall ((var0 Int) (var1 Heap) (var2 HeapObject) (var3 Int) (var4 AllocResHeap) (var5 Heap) (var6 Addr) (var7 Heap) (var8 HeapObject) (var9 Int)) (or (not (and (and (and (and (and (and (= (O_Int var9) var8) (= (write var7 var6 var8) var5)) (= (AllocResHeap var7 var6) var4)) (= (O_Int var3) var2)) (= (alloc var1 var2) var4)) (<= 0 (+ var0 (- 1)))) (= emptyHeap var1))) (inv_main23_8 var5 var0 var6))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 Addr)) (or (not (and (and (Inv_Heap var2 var1) (rec_pre var0 var2)) (and (= (read var0 var2) var1) (valid var0 var2)))) (_Glue4 var2 var0 var1))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Heap)) (or (not (and (rec_pre var2 var1) (and (= (read var2 var1) var0) (not (valid var2 var1))))) (_Glue4 var1 var2 var0))))
(assert (forall ((var0 HeapObject) (var1 Int) (var2 HeapObject) (var3 Heap) (var4 Addr)) (or (not (and (_Glue4 var4 var3 var2) (and (and (and (= (getInt var2) var1) (<= 0 (+ (- 1) (* (- 1) var1)))) (= defObj var0)) (valid var3 var4)))) (Inv_Heap var4 var0))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 Int) (var3 HeapObject) (var4 Heap) (var5 Addr)) (or (not (and (_Glue4 var5 var4 var3) (and (and (and (= (getInt var3) var2) (<= 0 (+ (- 1) (* (- 1) var2)))) (= defObj var1)) (= (write var4 var5 var1) var0)))) (rec15_9 var0 var5 var4 var2))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 HeapObject) (var4 Addr)) (not (and (and (Inv_Heap var4 var3) (rec_pre var2 var4)) (and (and (and (and (and (and (= defObj var3) (= (read var2 var4) var3)) (= nullAddr var1)) (= (getInt var3) var0)) (not (= var4 var1))) (<= 0 (+ (- 1) (* (- 1) var0)))) (valid var2 var4))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 HeapObject) (var3 Addr) (var4 Heap)) (not (and (rec_pre var4 var3) (and (and (and (and (and (and (= defObj var2) (= (read var4 var3) var2)) (= nullAddr var1)) (= (getInt var2) var0)) (not (= var3 var1))) (<= 0 (+ (- 1) (* (- 1) var0)))) (not (valid var4 var3)))))))
(assert (forall ((var0 AllocResHeap) (var1 HeapObject) (var2 Int) (var3 Int) (var4 Heap) (var5 Addr) (var6 Int) (var7 Heap)) (or (not (and (and (inv_main23_8 var7 var6 var5) (rec15_9 var4 var5 var7 var3)) (and (= (O_Int var2) var1) (= (alloc var4 var1) var0)))) (Inv_Heap (newAddr var0) var1))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 AllocResHeap) (var4 Addr) (var5 Heap) (var6 HeapObject) (var7 Int) (var8 Int) (var9 Heap) (var10 Addr) (var11 Int) (var12 Heap)) (or (not (and (and (inv_main23_8 var12 var11 var10) (rec15_9 var9 var10 var12 var8)) (and (and (= (O_Int var7) var6) (= (AllocResHeap var5 var4) var3)) (= (alloc var9 var6) var3)))) (_Glue1_exp var2 var1 var11 var0 var8 var5 var4))))
(assert (forall ((var0 HeapObject) (var1 Heap) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Addr)) (or (not (and (_Glue1_exp var6 var5 var4 var3 var2 var1 var6) (and (and (and (= (O_Int var3) var0) (= var5 (+ var4 var2))) (<= 0 (+ (+ var2 var4) (- 1)))) (valid var1 var6)))) (Inv_Heap var6 var0))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 Heap) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Addr)) (or (not (and (_Glue1_exp var7 var6 var5 var4 var3 var2 var7) (and (and (and (= (O_Int var4) var1) (= (write var2 var7 var1) var0)) (= var6 (+ var5 var3))) (<= 0 (+ (+ var3 var5) (- 1)))))) (inv_main23_8 var0 var6 var7))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 Addr)) (or (not (and (and (Inv_Heap var2 var1) (rec_pre var0 var2)) (and (= (read var0 var2) var1) (valid var0 var2)))) (_Glue0 var0 var2 var1))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Heap)) (or (not (and (rec_pre var2 var1) (and (= (read var2 var1) var0) (not (valid var2 var1))))) (_Glue0 var2 var1 var0))))
(assert (forall ((var0 HeapObject) (var1 Int) (var2 HeapObject) (var3 Addr) (var4 Heap)) (or (not (and (_Glue0 var4 var3 var2) (and (and (and (= (getInt var2) var1) (not (<= 0 (+ (- 1) (* (- 1) var1))))) (= (O_Int (+ var1 (- 1))) var0)) (valid var4 var3)))) (Inv_Heap var3 var0))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 Int) (var3 HeapObject) (var4 Addr) (var5 Heap)) (or (not (and (_Glue0 var5 var4 var3) (and (and (and (= (getInt var3) var2) (not (<= 0 (+ (- 1) (* (- 1) var2))))) (= (O_Int (+ var2 (- 1))) var1)) (= (write var5 var4 var1) var0)))) (rec_pre var0 var4))))
(check-sat)