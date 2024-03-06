(set-logic HORN)
(set-info :source |
    Benchmark: 
    Output by Princess (http://www.philipp.ruemmer.org/princess.shtml)
|)
(declare-heap Heap Addr HeapObject
 defObj
 ((HeapObject 0) (dll 0)) (
  (
   (O_Int (getInt Int))
   (O_UInt (getUInt Int))
   (O_Addr (getAddr Addr))
   (O_AddrRange (getAddrRange AddrRange))
   (O_dll (getdll dll))
   (defObj)
  )
  (
   (dll (|dll::next| Addr) (|dll::prev| Addr))
  )
))
(declare-fun inv_main2424_5 (Heap Addr Addr) Bool)
(declare-fun _Glue1 (Addr Addr Addr Heap HeapObject) Bool)
(declare-fun _Glue8 (Addr Addr Heap Addr HeapObject) Bool)
(declare-fun _Glue7 (Heap Addr Addr HeapObject) Bool)
(declare-fun inv_main2432_9 (Heap Addr Addr) Bool)
(declare-fun Inv_Heap (Addr HeapObject) Bool)
(declare-fun inv_main2406_5 (Heap Addr Addr) Bool)
(declare-fun _Glue3 (Heap Addr Addr Addr Addr HeapObject) Bool)
(declare-fun _Glue13 (Addr Addr Heap HeapObject) Bool)
(declare-fun _Glue5 (Heap Addr Addr Addr HeapObject) Bool)
(declare-fun inv_main2416_5 (Heap Addr) Bool)
(declare-fun _Glue15 (Heap Addr Addr HeapObject) Bool)
(assert (forall ((var0 AllocResHeap) (var1 Heap) (var2 HeapObject) (var3 dll)) (or (not (and (and (= (O_dll var3) var2) (= (alloc var1 var2) var0)) (= emptyHeap var1))) (Inv_Heap (newAddr var0) var2))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 HeapObject) (var3 dll) (var4 AllocResHeap) (var5 Heap) (var6 HeapObject) (var7 Addr)) (or (not (and (Inv_Heap var7 var6) (and (and (and (and (and (and (= (read var5 var7) var6) (valid var5 var7)) (= (AllocResHeap var5 var7) var4)) (= (O_dll var3) var2)) (= (alloc var1 var2) var4)) (= nullAddr var0)) (= emptyHeap var1)))) (_Glue13 var7 var0 var5 var6))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 HeapObject) (var3 dll) (var4 AllocResHeap) (var5 HeapObject) (var6 Addr) (var7 Heap)) (or (not (and (and (and (and (and (and (= (read var7 var6) var5) (not (valid var7 var6))) (= (AllocResHeap var7 var6) var4)) (= (O_dll var3) var2)) (= (alloc var1 var2) var4)) (= nullAddr var0)) (= emptyHeap var1))) (_Glue13 var6 var0 var7 var5))))
(assert (forall ((var0 HeapObject) (var1 dll) (var2 Addr) (var3 dll) (var4 HeapObject) (var5 Heap) (var6 Addr) (var7 Addr)) (or (not (and (_Glue13 var7 var6 var5 var4) (and (and (and (and (= (getdll var4) var3) (= (|dll::prev| var3) var2)) (= (dll var6 var2) var1)) (= (O_dll var1) var0)) (valid var5 var7)))) (Inv_Heap var7 var0))))
(assert (forall ((var0 HeapObject) (var1 dll) (var2 Addr) (var3 dll) (var4 Heap) (var5 HeapObject) (var6 Heap) (var7 Addr) (var8 HeapObject) (var9 Addr)) (or (not (and (and (Inv_Heap var9 var8) (_Glue13 var9 var7 var6 var5)) (and (and (and (and (and (and (= (read var4 var9) var8) (valid var4 var9)) (= (getdll var5) var3)) (= (|dll::prev| var3) var2)) (= (dll var7 var2) var1)) (= (O_dll var1) var0)) (= (write var6 var9 var0) var4)))) (_Glue15 var4 var9 var7 var8))))
(assert (forall ((var0 HeapObject) (var1 dll) (var2 Addr) (var3 dll) (var4 HeapObject) (var5 Heap) (var6 HeapObject) (var7 Heap) (var8 Addr) (var9 Addr)) (or (not (and (_Glue13 var9 var8 var7 var6) (and (and (and (and (and (and (= (read var5 var9) var4) (not (valid var5 var9))) (= (getdll var6) var3)) (= (|dll::prev| var3) var2)) (= (dll var8 var2) var1)) (= (O_dll var1) var0)) (= (write var7 var9 var0) var5)))) (_Glue15 var5 var9 var8 var4))))
(assert (forall ((var0 HeapObject) (var1 dll) (var2 Addr) (var3 dll) (var4 HeapObject) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (_Glue15 var7 var6 var5 var4) (and (and (and (and (= (getdll var4) var3) (= (|dll::next| var3) var2)) (= (dll var2 var5) var1)) (= (O_dll var1) var0)) (valid var7 var6)))) (Inv_Heap var6 var0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 HeapObject) (var3 dll) (var4 Addr) (var5 dll) (var6 HeapObject) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (_Glue15 var9 var8 var7 var6) (and (and (and (and (and (= (getdll var6) var5) (= (|dll::next| var5) var4)) (= (dll var4 var7) var3)) (= (O_dll var3) var2)) (= (write var9 var8 var2) var1)) (= var0 var8)))) (inv_main2406_5 var1 var8 var0))))
(assert (forall ((var0 dll) (var1 Addr) (var2 Addr) (var3 Heap) (var4 HeapObject) (var5 Addr)) (or (not (and (and (Inv_Heap var5 var4) (inv_main2416_5 var3 var5)) (and (and (and (and (and (not (= var2 var1)) (= (read var3 var5) var4)) (= (getdll var4) var0)) (= (|dll::next| var0) var2)) (= nullAddr var1)) (valid var3 var5)))) (inv_main2416_5 var3 var2))))
(assert (forall ((var0 dll) (var1 HeapObject) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main2416_5 var5 var4) (and (and (and (and (and (not (= var3 var2)) (= (read var5 var4) var1)) (= (getdll var1) var0)) (= (|dll::next| var0) var3)) (= nullAddr var2)) (not (valid var5 var4))))) (inv_main2416_5 var5 var3))))
(assert (forall ((var0 Addr) (var1 dll) (var2 Addr) (var3 Addr) (var4 Heap) (var5 HeapObject) (var6 Addr)) (or (not (and (and (Inv_Heap var6 var5) (inv_main2424_5 var4 var3 var6)) (and (and (and (and (and (not (= var6 var2)) (= nullAddr var2)) (= (read var4 var6) var5)) (= (getdll var5) var1)) (= (|dll::prev| var1) var0)) (valid var4 var6)))) (inv_main2424_5 var4 var3 var0))))
(assert (forall ((var0 Addr) (var1 dll) (var2 HeapObject) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main2424_5 var6 var5 var4) (and (and (and (and (and (not (= var4 var3)) (= nullAddr var3)) (= (read var6 var4) var2)) (= (getdll var2) var1)) (= (|dll::prev| var1) var0)) (not (valid var6 var4))))) (inv_main2424_5 var6 var5 var0))))
(assert (forall ((var0 Addr) (var1 dll) (var2 Addr) (var3 Heap) (var4 HeapObject) (var5 Addr)) (or (not (and (and (Inv_Heap var5 var4) (inv_main2424_5 var3 var5 var2)) (and (and (and (and (and (not (= var5 var2)) (= (read var3 var5) var4)) (= (getdll var4) var1)) (= (|dll::prev| var1) var0)) (= nullAddr var2)) (valid var3 var5)))) (inv_main2432_9 var3 var5 var0))))
(assert (forall ((var0 Addr) (var1 dll) (var2 HeapObject) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main2424_5 var5 var4 var3) (and (and (and (and (and (not (= var4 var3)) (= (read var5 var4) var2)) (= (getdll var2) var1)) (= (|dll::prev| var1) var0)) (= nullAddr var3)) (not (valid var5 var4))))) (inv_main2432_9 var5 var4 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 dll) (var3 Heap) (var4 HeapObject) (var5 Addr)) (or (not (and (and (Inv_Heap var5 var4) (inv_main2416_5 var3 var5)) (and (and (and (and (and (= (read var3 var5) var4) (= (getdll var4) var2)) (= (|dll::next| var2) var1)) (= nullAddr var1)) (valid var3 var5)) (= var0 var5)))) (inv_main2424_5 var3 var0 var5))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 dll) (var3 HeapObject) (var4 Addr) (var5 Heap)) (or (not (and (inv_main2416_5 var5 var4) (and (and (and (and (and (= (read var5 var4) var3) (= (getdll var3) var2)) (= (|dll::next| var2) var1)) (= nullAddr var1)) (not (valid var5 var4))) (= var0 var4)))) (inv_main2424_5 var5 var0 var4))))
(assert (forall ((var0 AllocResHeap) (var1 HeapObject) (var2 dll) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main2406_5 var5 var4 var3) (and (= (O_dll var2) var1) (= (alloc var5 var1) var0)))) (Inv_Heap (newAddr var0) var1))))
(assert (forall ((var0 AllocResHeap) (var1 HeapObject) (var2 dll) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Heap) (var7 HeapObject) (var8 Addr)) (or (not (and (and (Inv_Heap var8 var7) (inv_main2406_5 var6 var5 var4)) (and (and (and (and (and (= (read var3 var8) var7) (valid var3 var8)) true) (= (O_dll var2) var1)) (= (AllocResHeap var3 var8) var0)) (= (alloc var6 var1) var0)))) (_Glue1 var4 var5 var8 var3 var7))))
(assert (forall ((var0 AllocResHeap) (var1 HeapObject) (var2 dll) (var3 HeapObject) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main2406_5 var8 var7 var6) (and (and (and (and (= (read var5 var4) var3) (not (valid var5 var4))) (= (O_dll var2) var1)) (= (AllocResHeap var5 var4) var0)) (= (alloc var8 var1) var0)))) (_Glue1 var6 var7 var4 var5 var3))))
(assert (forall ((var0 HeapObject) (var1 dll) (var2 Addr) (var3 Addr) (var4 dll) (var5 HeapObject) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Addr)) (or (not (and (_Glue1 var9 var8 var7 var6 var5) (and (and (and (and (and (= (getdll var5) var4) (= (|dll::prev| var4) var3)) (= nullAddr var2)) (= (dll var2 var3) var1)) (= (O_dll var1) var0)) (valid var6 var7)))) (Inv_Heap var7 var0))))
(assert (forall ((var0 HeapObject) (var1 dll) (var2 Addr) (var3 Addr) (var4 dll) (var5 Heap) (var6 HeapObject) (var7 Heap) (var8 Addr) (var9 Addr) (var10 HeapObject) (var11 Addr)) (or (not (and (and (Inv_Heap var11 var10) (_Glue1 var9 var8 var11 var7 var6)) (and (and (and (and (and (and (and (and (= (read var5 var11) var10) (valid var5 var11)) true) (= (getdll var6) var4)) (= (|dll::prev| var4) var3)) (= nullAddr var2)) (= (dll var2 var3) var1)) (= (O_dll var1) var0)) (= (write var7 var11 var0) var5)))) (_Glue3 var5 var2 var9 var8 var11 var10))))
(assert (forall ((var0 HeapObject) (var1 dll) (var2 Addr) (var3 Addr) (var4 dll) (var5 HeapObject) (var6 Heap) (var7 HeapObject) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Addr)) (or (not (and (_Glue1 var11 var10 var9 var8 var7) (and (and (and (and (and (and (and (= (read var6 var9) var5) (not (valid var6 var9))) (= (getdll var7) var4)) (= (|dll::prev| var4) var3)) (= nullAddr var2)) (= (dll var2 var3) var1)) (= (O_dll var1) var0)) (= (write var8 var9 var0) var6)))) (_Glue3 var6 var2 var11 var10 var9 var5))))
(assert (forall ((var0 HeapObject) (var1 dll) (var2 Addr) (var3 dll) (var4 HeapObject) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (_Glue3 var9 var8 var7 var6 var5 var4) (and (and (and (and (= (getdll var4) var3) (= (|dll::next| var3) var2)) (= (dll var2 var8) var1)) (= (O_dll var1) var0)) (valid var9 var5)))) (Inv_Heap var5 var0))))
(assert (forall ((var0 HeapObject) (var1 dll) (var2 Addr) (var3 dll) (var4 Heap) (var5 HeapObject) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap) (var10 HeapObject) (var11 Addr)) (or (not (and (and (Inv_Heap var11 var10) (_Glue3 var9 var8 var11 var7 var6 var5)) (and (and (and (and (and (and (and (= (read var4 var11) var10) (valid var4 var11)) true) (= (getdll var5) var3)) (= (|dll::next| var3) var2)) (= (dll var2 var8) var1)) (= (O_dll var1) var0)) (= (write var9 var6 var0) var4)))) (_Glue5 var4 var11 var7 var6 var10))))
(assert (forall ((var0 HeapObject) (var1 dll) (var2 Addr) (var3 dll) (var4 HeapObject) (var5 Heap) (var6 HeapObject) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Heap)) (or (not (and (_Glue3 var11 var10 var9 var8 var7 var6) (and (and (and (and (and (and (= (read var5 var9) var4) (not (valid var5 var9))) (= (getdll var6) var3)) (= (|dll::next| var3) var2)) (= (dll var2 var10) var1)) (= (O_dll var1) var0)) (= (write var11 var7 var0) var5)))) (_Glue5 var5 var9 var8 var7 var4))))
(assert (forall ((var0 HeapObject) (var1 dll) (var2 Addr) (var3 dll) (var4 HeapObject) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (_Glue5 var8 var7 var6 var5 var4) (and (and (and (and (= (getdll var4) var3) (= (|dll::prev| var3) var2)) (= (dll var5 var2) var1)) (= (O_dll var1) var0)) (valid var8 var7)))) (Inv_Heap var7 var0))))
(assert (forall ((var0 HeapObject) (var1 dll) (var2 Addr) (var3 dll) (var4 Heap) (var5 HeapObject) (var6 Addr) (var7 Addr) (var8 Heap) (var9 HeapObject) (var10 Addr)) (or (not (and (and (Inv_Heap var10 var9) (_Glue5 var8 var10 var7 var6 var5)) (and (and (and (and (and (and (and (= (read var4 var10) var9) (valid var4 var10)) true) (= (getdll var5) var3)) (= (|dll::prev| var3) var2)) (= (dll var6 var2) var1)) (= (O_dll var1) var0)) (= (write var8 var10 var0) var4)))) (_Glue7 var4 var10 var7 var9))))
(assert (forall ((var0 HeapObject) (var1 dll) (var2 Addr) (var3 dll) (var4 HeapObject) (var5 Heap) (var6 HeapObject) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (_Glue5 var10 var9 var8 var7 var6) (and (and (and (and (and (and (= (read var5 var9) var4) (not (valid var5 var9))) (= (getdll var6) var3)) (= (|dll::prev| var3) var2)) (= (dll var7 var2) var1)) (= (O_dll var1) var0)) (= (write var10 var9 var0) var5)))) (_Glue7 var5 var9 var8 var4))))
(assert (forall ((var0 dll) (var1 HeapObject) (var2 Addr) (var3 Addr) (var4 Heap) (var5 HeapObject) (var6 Addr)) (or (not (and (and (Inv_Heap var6 var5) (_Glue7 var4 var3 var2 var1)) (and (and (and (= (getdll var1) var0) (= (|dll::next| var0) var6)) (= (read var4 var6) var5)) (valid var4 var6)))) (_Glue8 var2 var3 var4 var6 var5))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 dll) (var3 HeapObject) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (_Glue7 var6 var5 var4 var3) (and (and (and (= (getdll var3) var2) (= (|dll::next| var2) var1)) (= (read var6 var1) var0)) (not (valid var6 var1))))) (_Glue8 var4 var5 var6 var1 var0))))
(assert (forall ((var0 HeapObject) (var1 dll) (var2 Addr) (var3 dll) (var4 HeapObject) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Addr)) (or (not (and (_Glue8 var8 var7 var6 var5 var4) (and (and (and (and (= (getdll var4) var3) (= (|dll::next| var3) var2)) (= (dll var2 var7) var1)) (= (O_dll var1) var0)) (valid var6 var5)))) (Inv_Heap var5 var0))))
(assert (forall ((var0 HeapObject) (var1 dll) (var2 Addr) (var3 dll) (var4 Addr) (var5 dll) (var6 Heap) (var7 HeapObject) (var8 Addr) (var9 Heap) (var10 Addr) (var11 HeapObject) (var12 Addr)) (or (not (and (and (Inv_Heap var12 var11) (_Glue8 var10 var12 var9 var8 var7)) (and (and (and (and (and (and (and (and (and (= (read var6 var12) var11) (= (getdll var11) var5)) (= (|dll::next| var5) var4)) (valid var6 var12)) true) (= (getdll var7) var3)) (= (|dll::next| var3) var2)) (= (dll var2 var12) var1)) (= (O_dll var1) var0)) (= (write var9 var8 var0) var6)))) (inv_main2406_5 var6 var10 var4))))
(assert (forall ((var0 HeapObject) (var1 dll) (var2 Addr) (var3 dll) (var4 Addr) (var5 dll) (var6 HeapObject) (var7 Heap) (var8 HeapObject) (var9 Addr) (var10 Heap) (var11 Addr) (var12 Addr)) (or (not (and (_Glue8 var12 var11 var10 var9 var8) (and (and (and (and (and (and (and (and (= (read var7 var11) var6) (= (getdll var6) var5)) (= (|dll::next| var5) var4)) (not (valid var7 var11))) (= (getdll var8) var3)) (= (|dll::next| var3) var2)) (= (dll var2 var11) var1)) (= (O_dll var1) var0)) (= (write var10 var9 var0) var7)))) (inv_main2406_5 var7 var12 var4))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (inv_main2406_5 var2 var1 var0)) (inv_main2416_5 var2 var1))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main2432_9 var4 var3 var2) (and (and (and (= nullAddr var1) (not (= var2 var1))) (= defObj var0)) (valid var4 var3)))) (Inv_Heap var3 var0))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 dll) (var4 Heap) (var5 Addr) (var6 Heap) (var7 HeapObject) (var8 Addr)) (or (not (and (and (Inv_Heap var8 var7) (inv_main2432_9 var6 var5 var8)) (and (and (and (and (and (and (and (and (= (read var4 var8) var7) (= (getdll var7) var3)) (= (|dll::prev| var3) var2)) (valid var4 var8)) true) (= nullAddr var1)) (not (= var8 var1))) (= defObj var0)) (= (write var6 var5 var0) var4)))) (inv_main2432_9 var4 var8 var2))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 dll) (var4 HeapObject) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main2432_9 var8 var7 var6) (and (and (and (and (and (and (and (= (read var5 var6) var4) (= (getdll var4) var3)) (= (|dll::prev| var3) var2)) (not (valid var5 var6))) (= nullAddr var1)) (not (= var6 var1))) (= defObj var0)) (= (write var8 var7 var0) var5)))) (inv_main2432_9 var5 var6 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 HeapObject) (var4 Addr)) (not (and (and (Inv_Heap var4 var3) (inv_main2432_9 var2 var4 var1)) (and (and (and (and (not (= var4 var0)) (= (read var2 var4) var3)) (= defObj var3)) (= nullAddr var0)) (valid var2 var4))))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main2432_9 var4 var3 var2) (and (and (and (and (not (= var3 var1)) (= (read var4 var3) var0)) (= defObj var0)) (= nullAddr var1)) (not (valid var4 var3)))))))
(check-sat)
