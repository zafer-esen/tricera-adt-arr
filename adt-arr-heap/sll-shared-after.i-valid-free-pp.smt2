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
(declare-fun _Glue6 (Heap Addr Addr Addr HeapObject) Bool)
(declare-fun _Glue4 (Addr Addr Addr Heap HeapObject) Bool)
(declare-fun inv_main_12 (Heap Addr) Bool)
(declare-fun inv_main2436_5 (Heap Addr Addr Addr) Bool)
(declare-fun _Glue2 (Addr Addr Heap HeapObject) Bool)
(declare-fun Inv_Heap (Addr HeapObject) Bool)
(declare-fun _Glue8 (Addr Heap Addr Addr HeapObject) Bool)
(declare-fun inv_main2426_9 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main2409_5 (Heap Addr Addr) Bool)
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main2426_9 var5 var4 var3 var2) (and (and (and (= nullAddr var1) (not (= var2 var1))) (= defObj var0)) (valid var5 var3)))) (Inv_Heap var3 var0))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 sll) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Heap) (var8 HeapObject) (var9 Addr)) (or (not (and (and (Inv_Heap var9 var8) (inv_main2426_9 var7 var6 var5 var9)) (and (and (and (and (and (and (and (and (= (read var4 var9) var8) (= (getsll var8) var3)) (= (|sll::next| var3) var2)) (valid var4 var9)) true) (= nullAddr var1)) (not (= var9 var1))) (= defObj var0)) (= (write var7 var5 var0) var4)))) (inv_main2426_9 var4 var6 var9 var2))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 sll) (var4 HeapObject) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main2426_9 var9 var8 var7 var6) (and (and (and (and (and (and (and (= (read var5 var6) var4) (= (getsll var4) var3)) (= (|sll::next| var3) var2)) (not (valid var5 var6))) (= nullAddr var1)) (not (= var6 var1))) (= defObj var0)) (= (write var9 var7 var0) var5)))) (inv_main2426_9 var5 var8 var6 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 HeapObject) (var5 Addr)) (or (not (and (and (Inv_Heap var5 var4) (inv_main2436_5 var3 var2 var1 var5)) (and (and (and (= nullAddr var0) (not (= var5 var0))) (= (read var3 var5) var4)) (valid var3 var5)))) (_Glue8 var2 var3 var1 var5 var4))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main2436_5 var5 var4 var3 var2) (and (and (and (= nullAddr var1) (not (= var2 var1))) (= (read var5 var2) var0)) (not (valid var5 var2))))) (_Glue8 var4 var5 var3 var2 var0))))
(assert (forall ((var0 HeapObject) (var1 sll) (var2 Addr) (var3 sll) (var4 HeapObject) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Addr)) (or (not (and (_Glue8 var8 var7 var6 var5 var4) (and (and (and (and (= (getsll var4) var3) (= (|sll::next| var3) var2)) (= (sll var6 var2) var1)) (= (O_sll var1) var0)) (valid var7 var5)))) (Inv_Heap var5 var0))))
(assert (forall ((var0 HeapObject) (var1 sll) (var2 Addr) (var3 sll) (var4 Addr) (var5 sll) (var6 Heap) (var7 HeapObject) (var8 Addr) (var9 Heap) (var10 Addr) (var11 HeapObject) (var12 Addr)) (or (not (and (and (Inv_Heap var12 var11) (_Glue8 var10 var9 var8 var12 var7)) (and (and (and (and (and (and (and (and (and (= (read var6 var12) var11) (= (getsll var11) var5)) (= (|sll::next| var5) var4)) (valid var6 var12)) true) (= (getsll var7) var3)) (= (|sll::next| var3) var2)) (= (sll var8 var2) var1)) (= (O_sll var1) var0)) (= (write var9 var12 var0) var6)))) (inv_main2436_5 var6 var10 var8 var4))))
(assert (forall ((var0 HeapObject) (var1 sll) (var2 Addr) (var3 sll) (var4 Addr) (var5 sll) (var6 HeapObject) (var7 Heap) (var8 HeapObject) (var9 Addr) (var10 Addr) (var11 Heap) (var12 Addr)) (or (not (and (_Glue8 var12 var11 var10 var9 var8) (and (and (and (and (and (and (and (and (= (read var7 var9) var6) (= (getsll var6) var5)) (= (|sll::next| var5) var4)) (not (valid var7 var9))) (= (getsll var8) var3)) (= (|sll::next| var3) var2)) (= (sll var10 var2) var1)) (= (O_sll var1) var0)) (= (write var11 var9 var0) var7)))) (inv_main2436_5 var7 var12 var10 var4))))
(assert (forall ((var0 AllocResHeap) (var1 HeapObject) (var2 sll) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main2409_5 var5 var4 var3) (and (= (O_sll var2) var1) (= (alloc var5 var1) var0)))) (Inv_Heap (newAddr var0) var1))))
(assert (forall ((var0 AllocResHeap) (var1 HeapObject) (var2 sll) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Heap) (var7 HeapObject) (var8 Addr)) (or (not (and (and (Inv_Heap var8 var7) (inv_main2409_5 var6 var5 var4)) (and (and (and (and (and (= (read var3 var8) var7) (valid var3 var8)) true) (= (O_sll var2) var1)) (= (AllocResHeap var3 var8) var0)) (= (alloc var6 var1) var0)))) (_Glue4 var4 var5 var8 var3 var7))))
(assert (forall ((var0 AllocResHeap) (var1 HeapObject) (var2 sll) (var3 HeapObject) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main2409_5 var8 var7 var6) (and (and (and (and (= (read var5 var4) var3) (not (valid var5 var4))) (= (O_sll var2) var1)) (= (AllocResHeap var5 var4) var0)) (= (alloc var8 var1) var0)))) (_Glue4 var6 var7 var4 var5 var3))))
(assert (forall ((var0 HeapObject) (var1 sll) (var2 Addr) (var3 Addr) (var4 sll) (var5 HeapObject) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Addr)) (or (not (and (_Glue4 var9 var8 var7 var6 var5) (and (and (and (and (and (= (getsll var5) var4) (= (|sll::data| var4) var3)) (= nullAddr var2)) (= (sll var3 var2) var1)) (= (O_sll var1) var0)) (valid var6 var7)))) (Inv_Heap var7 var0))))
(assert (forall ((var0 HeapObject) (var1 sll) (var2 Addr) (var3 Addr) (var4 sll) (var5 Heap) (var6 HeapObject) (var7 Heap) (var8 Addr) (var9 Addr) (var10 HeapObject) (var11 Addr)) (or (not (and (and (Inv_Heap var11 var10) (_Glue4 var11 var9 var8 var7 var6)) (and (and (and (and (and (and (and (and (= (read var5 var11) var10) (valid var5 var11)) true) (= (getsll var6) var4)) (= (|sll::data| var4) var3)) (= nullAddr var2)) (= (sll var3 var2) var1)) (= (O_sll var1) var0)) (= (write var7 var8 var0) var5)))) (_Glue6 var5 var11 var9 var8 var10))))
(assert (forall ((var0 HeapObject) (var1 sll) (var2 Addr) (var3 Addr) (var4 sll) (var5 HeapObject) (var6 Heap) (var7 HeapObject) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Addr)) (or (not (and (_Glue4 var11 var10 var9 var8 var7) (and (and (and (and (and (and (and (= (read var6 var11) var5) (not (valid var6 var11))) (= (getsll var7) var4)) (= (|sll::data| var4) var3)) (= nullAddr var2)) (= (sll var3 var2) var1)) (= (O_sll var1) var0)) (= (write var8 var9 var0) var6)))) (_Glue6 var6 var11 var10 var9 var5))))
(assert (forall ((var0 HeapObject) (var1 sll) (var2 Addr) (var3 sll) (var4 HeapObject) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (_Glue6 var8 var7 var6 var5 var4) (and (and (and (and (= (getsll var4) var3) (= (|sll::data| var3) var2)) (= (sll var2 var5) var1)) (= (O_sll var1) var0)) (valid var8 var7)))) (Inv_Heap var7 var0))))
(assert (forall ((var0 HeapObject) (var1 sll) (var2 Addr) (var3 sll) (var4 Addr) (var5 sll) (var6 Heap) (var7 HeapObject) (var8 Addr) (var9 Addr) (var10 Heap) (var11 HeapObject) (var12 Addr)) (or (not (and (and (Inv_Heap var12 var11) (_Glue6 var10 var12 var9 var8 var7)) (and (and (and (and (and (and (and (and (and (= (read var6 var12) var11) (= (getsll var11) var5)) (= (|sll::next| var5) var4)) (valid var6 var12)) true) (= (getsll var7) var3)) (= (|sll::data| var3) var2)) (= (sll var2 var8) var1)) (= (O_sll var1) var0)) (= (write var10 var12 var0) var6)))) (inv_main2409_5 var6 var9 var4))))
(assert (forall ((var0 HeapObject) (var1 sll) (var2 Addr) (var3 sll) (var4 Addr) (var5 sll) (var6 HeapObject) (var7 Heap) (var8 HeapObject) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Heap)) (or (not (and (_Glue6 var12 var11 var10 var9 var8) (and (and (and (and (and (and (and (and (= (read var7 var11) var6) (= (getsll var6) var5)) (= (|sll::next| var5) var4)) (not (valid var7 var11))) (= (getsll var8) var3)) (= (|sll::data| var3) var2)) (= (sll var2 var9) var1)) (= (O_sll var1) var0)) (= (write var12 var11 var0) var7)))) (inv_main2409_5 var7 var10 var4))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 HeapObject) (var5 Addr)) (not (and (and (Inv_Heap var5 var4) (inv_main2426_9 var3 var2 var5 var1)) (and (and (and (and (not (= var5 var0)) (= (read var3 var5) var4)) (= defObj var4)) (= nullAddr var0)) (valid var3 var5))))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (not (and (inv_main2426_9 var5 var4 var3 var2) (and (and (and (and (not (= var3 var1)) (= (read var5 var3) var0)) (= defObj var0)) (= nullAddr var1)) (not (valid var5 var3)))))))
(assert (forall ((var0 AllocResHeap) (var1 HeapObject) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main2409_5 var5 var4 var3) (and (= (O_Int var2) var1) (= (alloc var5 var1) var0)))) (Inv_Heap (newAddr var0) var1))))
(assert (forall ((var0 AllocResHeap) (var1 HeapObject) (var2 Int) (var3 Addr) (var4 Heap) (var5 HeapObject) (var6 Int) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main2409_5 var9 var8 var7) (and (and (and (and (= (O_Int var6) var5) (valid var4 var3)) (= (O_Int var2) var1)) (= (AllocResHeap var4 var3) var0)) (= (alloc var9 var1) var0)))) (Inv_Heap var3 var5))))
(assert (forall ((var0 Addr) (var1 AllocResHeap) (var2 HeapObject) (var3 Int) (var4 Heap) (var5 Addr) (var6 Heap) (var7 HeapObject) (var8 Int) (var9 Addr) (var10 Addr) (var11 Heap)) (or (not (and (inv_main2409_5 var11 var10 var9) (and (and (and (and (and (= (O_Int var8) var7) (= (write var6 var5 var7) var4)) (= (O_Int var3) var2)) (= (AllocResHeap var6 var5) var1)) (= (alloc var11 var2) var1)) (= var0 var10)))) (inv_main2436_5 var4 var0 var5 var10))))
(assert (forall ((var0 AllocResHeap) (var1 Heap) (var2 HeapObject) (var3 sll)) (or (not (and (and (= (O_sll var3) var2) (= (alloc var1 var2) var0)) (= emptyHeap var1))) (Inv_Heap (newAddr var0) var2))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 HeapObject) (var3 sll) (var4 AllocResHeap) (var5 Heap) (var6 HeapObject) (var7 Addr)) (or (not (and (Inv_Heap var7 var6) (and (and (and (and (and (and (= (read var5 var7) var6) (valid var5 var7)) (= (AllocResHeap var5 var7) var4)) (= (O_sll var3) var2)) (= (alloc var1 var2) var4)) (= nullAddr var0)) (= emptyHeap var1)))) (_Glue2 var7 var0 var5 var6))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 HeapObject) (var3 sll) (var4 AllocResHeap) (var5 HeapObject) (var6 Addr) (var7 Heap)) (or (not (and (and (and (and (and (and (= (read var7 var6) var5) (not (valid var7 var6))) (= (AllocResHeap var7 var6) var4)) (= (O_sll var3) var2)) (= (alloc var1 var2) var4)) (= nullAddr var0)) (= emptyHeap var1))) (_Glue2 var6 var0 var7 var5))))
(assert (forall ((var0 HeapObject) (var1 sll) (var2 Addr) (var3 sll) (var4 HeapObject) (var5 Heap) (var6 Addr) (var7 Addr)) (or (not (and (_Glue2 var7 var6 var5 var4) (and (and (and (and (= (getsll var4) var3) (= (|sll::data| var3) var2)) (= (sll var2 var6) var1)) (= (O_sll var1) var0)) (valid var5 var7)))) (Inv_Heap var7 var0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 HeapObject) (var3 sll) (var4 Addr) (var5 sll) (var6 HeapObject) (var7 Heap) (var8 Addr) (var9 Addr)) (or (not (and (_Glue2 var9 var8 var7 var6) (and (and (and (and (and (= (getsll var6) var5) (= (|sll::data| var5) var4)) (= (sll var4 var8) var3)) (= (O_sll var3) var2)) (= (write var7 var9 var2) var1)) (= var0 var9)))) (inv_main2409_5 var1 var9 var0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 HeapObject) (var3 Addr)) (not (and (and (Inv_Heap var3 var2) (inv_main_12 var1 var3)) (and (and (and (and (not (= var3 var0)) (= (read var1 var3) var2)) (= defObj var2)) (= nullAddr var0)) (valid var1 var3))))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_12 var3 var2) (and (and (and (and (not (= var2 var1)) (= (read var3 var2) var0)) (= defObj var0)) (= nullAddr var1)) (not (valid var3 var2)))))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main2426_9 var4 var3 var2 var1) (and (and (= defObj var0) (= nullAddr var1)) (valid var4 var2)))) (Inv_Heap var2 var0))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main2426_9 var5 var4 var3 var2) (and (and (= defObj var1) (= (write var5 var3 var1) var0)) (= nullAddr var2)))) (inv_main_12 var0 var4))))
(assert (forall ((var0 Addr) (var1 sll) (var2 Addr) (var3 Addr) (var4 Heap) (var5 HeapObject) (var6 Addr)) (or (not (and (and (Inv_Heap var6 var5) (inv_main2436_5 var4 var6 var3 var2)) (and (and (and (and (and (not (= var6 var2)) (= (read var4 var6) var5)) (= (getsll var5) var1)) (= (|sll::next| var1) var0)) (= nullAddr var2)) (valid var4 var6)))) (inv_main2426_9 var4 var3 var6 var0))))
(assert (forall ((var0 Addr) (var1 sll) (var2 HeapObject) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main2436_5 var6 var5 var4 var3) (and (and (and (and (and (not (= var5 var3)) (= (read var6 var5) var2)) (= (getsll var2) var1)) (= (|sll::next| var1) var0)) (= nullAddr var3)) (not (valid var6 var5))))) (inv_main2426_9 var6 var4 var5 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (and (inv_main2436_5 var2 var1 var0 var1) (= nullAddr var1))) (inv_main_12 var2 var0))))
(check-sat)