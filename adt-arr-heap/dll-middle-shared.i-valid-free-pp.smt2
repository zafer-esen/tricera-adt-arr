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
   (dll (|dll::data1| Addr) (|dll::next| Addr) (|dll::prev| Addr) (|dll::data2| Addr))
  )
))
(declare-fun _Glue32 (Heap Addr Addr Addr HeapObject) Bool)
(declare-fun _Glue14 (Addr Addr Addr Addr Heap Addr HeapObject) Bool)
(declare-fun _Glue34 (Addr Heap Addr HeapObject) Bool)
(declare-fun _Glue33_exp (Addr Heap Addr HeapObject) Bool)
(declare-fun _Glue36_exp (Heap Addr HeapObject) Bool)
(declare-fun _Glue11 (Addr Addr Addr Addr Heap Addr HeapObject) Bool)
(declare-fun _Glue30 (Heap Addr Addr Addr HeapObject) Bool)
(declare-fun _Glue10 (Heap Addr Addr Addr Addr HeapObject) Bool)
(declare-fun inv_main2430_5 (Heap Addr Addr) Bool)
(declare-fun _Glue16 (Heap Addr Addr Addr Addr HeapObject) Bool)
(declare-fun _Glue17 (Addr Addr Addr Addr Heap Addr HeapObject) Bool)
(declare-fun _Glue2 (Heap HeapObject Addr HeapObject) Bool)
(declare-fun _Glue24_exp (Heap Addr Int Int Int Int Addr HeapObject) Bool)
(declare-fun _Glue13 (Heap Addr Addr Addr Addr HeapObject) Bool)
(declare-fun Inv_Heap (Addr HeapObject) Bool)
(declare-fun _Glue4 (Addr Addr Addr Addr Addr Heap HeapObject) Bool)
(declare-fun inv_main_5 (Heap Addr Addr Addr Addr) Bool)
(declare-fun _Glue8 (Heap Addr Addr Addr Addr Addr HeapObject) Bool)
(declare-fun inv_main2443_9 (Heap Addr Addr) Bool)
(declare-fun _Glue0 (HeapObject Addr Heap Addr HeapObject) Bool)
(declare-fun _Glue6 (Heap Addr Addr Addr Addr Addr Addr HeapObject) Bool)
(declare-fun _Glue22_exp (Addr Int Int Int Int Addr Heap HeapObject) Bool)
(assert (forall ((var0 Addr) (var1 Heap) (var2 HeapObject) (var3 Addr)) (or (not (and (and (Inv_Heap var3 var2) (inv_main2430_5 var1 var3 var0)) (and (and (= nullAddr var0) (= (read var1 var3) var2)) (valid var1 var3)))) (_Glue33_exp var0 var1 var3 var2))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main2430_5 var3 var2 var1) (and (and (= nullAddr var1) (= (read var3 var2) var0)) (not (valid var3 var2))))) (_Glue33_exp var1 var3 var2 var0))))
(assert (forall ((var0 dll) (var1 HeapObject) (var2 Addr) (var3 Heap) (var4 Addr) (var5 HeapObject) (var6 Addr)) (not (and (and (Inv_Heap var6 var5) (_Glue33_exp var4 var3 var2 var1)) (and (and (and (and (and (and (= (getdll var1) var0) (= (|dll::data1| var0) var6)) (= (read var3 var6) var5)) (not (= var2 var4))) (not (= var6 var4))) (valid var3 var6)) (= defObj var5))))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 dll) (var3 HeapObject) (var4 Addr) (var5 Heap) (var6 Addr)) (not (and (_Glue33_exp var6 var5 var4 var3) (and (and (and (and (and (and (= (getdll var3) var2) (= (|dll::data1| var2) var1)) (= (read var5 var1) var0)) (not (= var4 var6))) (not (= var1 var6))) (not (valid var5 var1))) (= defObj var0))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 HeapObject) (var3 Addr)) (or (not (and (and (Inv_Heap var3 var2) (inv_main2430_5 var1 var3 var0)) (and (and (= nullAddr var0) (= (read var1 var3) var2)) (valid var1 var3)))) (_Glue34 var0 var1 var3 var2))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main2430_5 var3 var2 var1) (and (and (= nullAddr var1) (= (read var3 var2) var0)) (not (valid var3 var2))))) (_Glue34 var1 var3 var2 var0))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 dll) (var3 HeapObject) (var4 Addr) (var5 Heap) (var6 Addr)) (or (not (and (_Glue34 var6 var5 var4 var3) (and (and (and (and (= (getdll var3) var2) (= (|dll::data1| var2) var1)) (not (= var4 var6))) (= defObj var0)) (valid var5 var1)))) (Inv_Heap var1 var0))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 dll) (var3 Addr) (var4 Heap) (var5 HeapObject) (var6 Heap) (var7 Addr) (var8 HeapObject) (var9 Addr)) (or (not (and (and (Inv_Heap var9 var8) (_Glue34 var7 var6 var9 var5)) (and (and (and (and (and (and (and (and (= (read var4 var9) var8) (not (= var9 var3))) (valid var4 var9)) true) (= (getdll var5) var2)) (= (|dll::data1| var2) var1)) (= defObj var0)) (= (write var6 var1 var0) var4)) (not (= var9 var7))))) (_Glue36_exp var4 var9 var8))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 dll) (var3 Addr) (var4 HeapObject) (var5 Heap) (var6 HeapObject) (var7 Addr) (var8 Heap) (var9 Addr)) (or (not (and (_Glue34 var9 var8 var7 var6) (and (and (and (and (and (and (and (= (read var5 var7) var4) (not (= var7 var3))) (not (valid var5 var7))) (= (getdll var6) var2)) (= (|dll::data1| var2) var1)) (= defObj var0)) (= (write var8 var1 var0) var5)) (not (= var7 var9))))) (_Glue36_exp var5 var7 var4))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 dll) (var3 Addr) (var4 HeapObject) (var5 Addr) (var6 Heap)) (or (not (and (_Glue36_exp var6 var5 var4) (and (and (and (and (not (= var5 var3)) (= (getdll var4) var2)) (= (|dll::data2| var2) var1)) (valid var6 var1)) (= defObj var0)))) (Inv_Heap var1 var0))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 dll) (var3 Addr) (var4 Addr) (var5 dll) (var6 Heap) (var7 Addr) (var8 HeapObject) (var9 Heap) (var10 HeapObject) (var11 Addr)) (or (not (and (and (Inv_Heap var11 var10) (_Glue36_exp var9 var11 var8)) (and (and (and (and (and (and (and (and (and (and (not (= var11 var7)) (= (read var6 var11) var10)) (= (getdll var10) var5)) (= (|dll::next| var5) var4)) (valid var6 var11)) true) (not (= var11 var3))) (= (getdll var8) var2)) (= (|dll::data2| var2) var1)) (= (write var9 var1 var0) var6)) (= defObj var0)))) (inv_main2443_9 var6 var11 var4))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 dll) (var3 Addr) (var4 Addr) (var5 dll) (var6 HeapObject) (var7 Heap) (var8 Addr) (var9 HeapObject) (var10 Addr) (var11 Heap)) (or (not (and (_Glue36_exp var11 var10 var9) (and (and (and (and (and (and (and (and (and (not (= var10 var8)) (= (read var7 var10) var6)) (= (getdll var6) var5)) (= (|dll::next| var5) var4)) (not (valid var7 var10))) (not (= var10 var3))) (= (getdll var9) var2)) (= (|dll::data2| var2) var1)) (= (write var11 var1 var0) var7)) (= defObj var0)))) (inv_main2443_9 var7 var10 var4))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main2443_9 var4 var3 var2) (and (and (and (= nullAddr var1) (not (= var2 var1))) (= defObj var0)) (valid var4 var3)))) (Inv_Heap var3 var0))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 dll) (var4 Heap) (var5 Addr) (var6 Heap) (var7 HeapObject) (var8 Addr)) (or (not (and (and (Inv_Heap var8 var7) (inv_main2443_9 var6 var5 var8)) (and (and (and (and (and (and (and (and (= (read var4 var8) var7) (= (getdll var7) var3)) (= (|dll::next| var3) var2)) (valid var4 var8)) true) (= nullAddr var1)) (not (= var8 var1))) (= defObj var0)) (= (write var6 var5 var0) var4)))) (inv_main2443_9 var4 var8 var2))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 dll) (var4 HeapObject) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main2443_9 var8 var7 var6) (and (and (and (and (and (and (and (= (read var5 var6) var4) (= (getdll var4) var3)) (= (|dll::next| var3) var2)) (not (valid var5 var6))) (= nullAddr var1)) (not (= var6 var1))) (= defObj var0)) (= (write var8 var7 var0) var5)))) (inv_main2443_9 var5 var6 var2))))
(assert (forall ((var0 AllocResHeap) (var1 HeapObject) (var2 dll) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main_5 var7 var6 var5 var4 var3) (and (= (O_dll var2) var1) (= (alloc var7 var1) var0)))) (Inv_Heap (newAddr var0) var1))))
(assert (forall ((var0 AllocResHeap) (var1 HeapObject) (var2 dll) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap) (var9 HeapObject) (var10 Addr)) (or (not (and (and (Inv_Heap var10 var9) (inv_main_5 var8 var7 var6 var5 var4)) (and (and (and (and (and (= (read var3 var10) var9) (valid var3 var10)) true) (= (O_dll var2) var1)) (= (AllocResHeap var3 var10) var0)) (= (alloc var8 var1) var0)))) (_Glue4 var6 var5 var4 var7 var10 var3 var9))))
(assert (forall ((var0 AllocResHeap) (var1 HeapObject) (var2 dll) (var3 HeapObject) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main_5 var10 var9 var8 var7 var6) (and (and (and (and (= (read var5 var4) var3) (not (valid var5 var4))) (= (O_dll var2) var1)) (= (AllocResHeap var5 var4) var0)) (= (alloc var10 var1) var0)))) (_Glue4 var8 var7 var6 var9 var4 var5 var3))))
(assert (forall ((var0 HeapObject) (var1 dll) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 dll) (var7 HeapObject) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr)) (or (not (and (_Glue4 var13 var12 var11 var10 var9 var8 var7) (and (and (and (and (and (and (and (= (getdll var7) var6) (= (|dll::data1| var6) var5)) (= (|dll::prev| var6) var4)) (= (|dll::data2| var6) var3)) (= nullAddr var2)) (= (dll var5 var2 var4 var3) var1)) (= (O_dll var1) var0)) (valid var8 var9)))) (Inv_Heap var9 var0))))
(assert (forall ((var0 HeapObject) (var1 dll) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 dll) (var7 Heap) (var8 HeapObject) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 HeapObject) (var15 Addr)) (or (not (and (and (Inv_Heap var15 var14) (_Glue4 var13 var12 var11 var10 var15 var9 var8)) (and (and (and (and (and (and (and (and (and (and (= (read var7 var15) var14) (valid var7 var15)) true) (= (getdll var8) var6)) (= (|dll::data1| var6) var5)) (= (|dll::prev| var6) var4)) (= (|dll::data2| var6) var3)) (= nullAddr var2)) (= (dll var5 var2 var4 var3) var1)) (= (O_dll var1) var0)) (= (write var9 var15 var0) var7)))) (_Glue6 var7 var2 var13 var12 var11 var10 var15 var14))))
(assert (forall ((var0 HeapObject) (var1 dll) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 dll) (var7 HeapObject) (var8 Heap) (var9 HeapObject) (var10 Heap) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr)) (or (not (and (_Glue4 var15 var14 var13 var12 var11 var10 var9) (and (and (and (and (and (and (and (and (and (= (read var8 var11) var7) (not (valid var8 var11))) (= (getdll var9) var6)) (= (|dll::data1| var6) var5)) (= (|dll::prev| var6) var4)) (= (|dll::data2| var6) var3)) (= nullAddr var2)) (= (dll var5 var2 var4 var3) var1)) (= (O_dll var1) var0)) (= (write var10 var11 var0) var8)))) (_Glue6 var8 var2 var15 var14 var13 var12 var11 var7))))
(assert (forall ((var0 HeapObject) (var1 dll) (var2 Addr) (var3 Addr) (var4 Addr) (var5 dll) (var6 HeapObject) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Heap)) (or (not (and (_Glue6 var13 var12 var11 var10 var9 var8 var7 var6) (and (and (and (and (and (and (= (getdll var6) var5) (= (|dll::data1| var5) var4)) (= (|dll::next| var5) var3)) (= (|dll::data2| var5) var2)) (= (dll var4 var3 var12 var2) var1)) (= (O_dll var1) var0)) (valid var13 var7)))) (Inv_Heap var7 var0))))
(assert (forall ((var0 HeapObject) (var1 dll) (var2 Addr) (var3 Addr) (var4 Addr) (var5 dll) (var6 Heap) (var7 HeapObject) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Heap) (var14 HeapObject) (var15 Addr)) (or (not (and (and (Inv_Heap var15 var14) (_Glue6 var13 var12 var15 var11 var10 var9 var8 var7)) (and (and (and (and (and (and (and (and (and (= (read var6 var15) var14) (valid var6 var15)) true) (= (getdll var7) var5)) (= (|dll::data1| var5) var4)) (= (|dll::next| var5) var3)) (= (|dll::data2| var5) var2)) (= (dll var4 var3 var12 var2) var1)) (= (O_dll var1) var0)) (= (write var13 var8 var0) var6)))) (_Glue8 var6 var15 var11 var10 var9 var8 var14))))
(assert (forall ((var0 HeapObject) (var1 dll) (var2 Addr) (var3 Addr) (var4 Addr) (var5 dll) (var6 HeapObject) (var7 Heap) (var8 HeapObject) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Heap)) (or (not (and (_Glue6 var15 var14 var13 var12 var11 var10 var9 var8) (and (and (and (and (and (and (and (and (= (read var7 var13) var6) (not (valid var7 var13))) (= (getdll var8) var5)) (= (|dll::data1| var5) var4)) (= (|dll::next| var5) var3)) (= (|dll::data2| var5) var2)) (= (dll var4 var3 var14 var2) var1)) (= (O_dll var1) var0)) (= (write var15 var9 var0) var7)))) (_Glue8 var7 var13 var12 var11 var10 var9 var6))))
(assert (forall ((var0 HeapObject) (var1 dll) (var2 Addr) (var3 Addr) (var4 Addr) (var5 dll) (var6 HeapObject) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Heap)) (or (not (and (_Glue8 var12 var11 var10 var9 var8 var7 var6) (and (and (and (and (and (and (= (getdll var6) var5) (= (|dll::data1| var5) var4)) (= (|dll::prev| var5) var3)) (= (|dll::data2| var5) var2)) (= (dll var4 var7 var3 var2) var1)) (= (O_dll var1) var0)) (valid var12 var11)))) (Inv_Heap var11 var0))))
(assert (forall ((var0 HeapObject) (var1 dll) (var2 Addr) (var3 Addr) (var4 Addr) (var5 dll) (var6 Heap) (var7 HeapObject) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Heap) (var13 HeapObject) (var14 Addr)) (or (not (and (and (Inv_Heap var14 var13) (_Glue8 var12 var14 var11 var10 var9 var8 var7)) (and (and (and (and (and (and (and (and (and (= (read var6 var14) var13) (valid var6 var14)) true) (= (getdll var7) var5)) (= (|dll::data1| var5) var4)) (= (|dll::prev| var5) var3)) (= (|dll::data2| var5) var2)) (= (dll var4 var8 var3 var2) var1)) (= (O_dll var1) var0)) (= (write var12 var14 var0) var6)))) (_Glue10 var6 var14 var11 var10 var9 var13))))
(assert (forall ((var0 HeapObject) (var1 dll) (var2 Addr) (var3 Addr) (var4 Addr) (var5 dll) (var6 HeapObject) (var7 Heap) (var8 HeapObject) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Heap)) (or (not (and (_Glue8 var14 var13 var12 var11 var10 var9 var8) (and (and (and (and (and (and (and (and (= (read var7 var13) var6) (not (valid var7 var13))) (= (getdll var8) var5)) (= (|dll::data1| var5) var4)) (= (|dll::prev| var5) var3)) (= (|dll::data2| var5) var2)) (= (dll var4 var9 var3 var2) var1)) (= (O_dll var1) var0)) (= (write var14 var13 var0) var7)))) (_Glue10 var7 var13 var12 var11 var10 var6))))
(assert (forall ((var0 dll) (var1 HeapObject) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 HeapObject) (var8 Addr)) (or (not (and (and (Inv_Heap var8 var7) (_Glue10 var6 var5 var4 var3 var2 var1)) (and (and (and (= (getdll var1) var0) (= (|dll::next| var0) var8)) (= (read var6 var8) var7)) (valid var6 var8)))) (_Glue11 var2 var3 var4 var5 var6 var8 var7))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 dll) (var3 HeapObject) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (_Glue10 var8 var7 var6 var5 var4 var3) (and (and (and (= (getdll var3) var2) (= (|dll::next| var2) var1)) (= (read var8 var1) var0)) (not (valid var8 var1))))) (_Glue11 var4 var5 var6 var7 var8 var1 var0))))
(assert (forall ((var0 HeapObject) (var1 dll) (var2 Addr) (var3 Addr) (var4 Addr) (var5 dll) (var6 HeapObject) (var7 Addr) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr)) (or (not (and (_Glue11 var12 var11 var10 var9 var8 var7 var6) (and (and (and (and (and (and (= (getdll var6) var5) (= (|dll::data1| var5) var4)) (= (|dll::next| var5) var3)) (= (|dll::data2| var5) var2)) (= (dll var4 var3 var9 var2) var1)) (= (O_dll var1) var0)) (valid var8 var7)))) (Inv_Heap var7 var0))))
(assert (forall ((var0 HeapObject) (var1 dll) (var2 Addr) (var3 Addr) (var4 Addr) (var5 dll) (var6 Heap) (var7 HeapObject) (var8 Addr) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Addr) (var13 HeapObject) (var14 Addr)) (or (not (and (and (Inv_Heap var14 var13) (_Glue11 var12 var11 var10 var14 var9 var8 var7)) (and (and (and (and (and (and (and (and (and (= (read var6 var14) var13) (valid var6 var14)) true) (= (getdll var7) var5)) (= (|dll::data1| var5) var4)) (= (|dll::next| var5) var3)) (= (|dll::data2| var5) var2)) (= (dll var4 var3 var14 var2) var1)) (= (O_dll var1) var0)) (= (write var9 var8 var0) var6)))) (_Glue13 var6 var12 var11 var10 var14 var13))))
(assert (forall ((var0 HeapObject) (var1 dll) (var2 Addr) (var3 Addr) (var4 Addr) (var5 dll) (var6 HeapObject) (var7 Heap) (var8 HeapObject) (var9 Addr) (var10 Heap) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr)) (or (not (and (_Glue11 var14 var13 var12 var11 var10 var9 var8) (and (and (and (and (and (and (and (and (= (read var7 var11) var6) (not (valid var7 var11))) (= (getdll var8) var5)) (= (|dll::data1| var5) var4)) (= (|dll::next| var5) var3)) (= (|dll::data2| var5) var2)) (= (dll var4 var3 var11 var2) var1)) (= (O_dll var1) var0)) (= (write var10 var9 var0) var7)))) (_Glue13 var7 var14 var13 var12 var11 var6))))
(assert (forall ((var0 dll) (var1 HeapObject) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 HeapObject) (var8 Addr)) (or (not (and (and (Inv_Heap var8 var7) (_Glue13 var6 var5 var4 var3 var2 var1)) (and (and (and (= (getdll var1) var0) (= (|dll::next| var0) var8)) (= (read var6 var8) var7)) (valid var6 var8)))) (_Glue14 var2 var3 var4 var5 var6 var8 var7))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 dll) (var3 HeapObject) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (_Glue13 var8 var7 var6 var5 var4 var3) (and (and (and (= (getdll var3) var2) (= (|dll::next| var2) var1)) (= (read var8 var1) var0)) (not (valid var8 var1))))) (_Glue14 var4 var5 var6 var7 var8 var1 var0))))
(assert (forall ((var0 HeapObject) (var1 dll) (var2 Addr) (var3 Addr) (var4 Addr) (var5 dll) (var6 HeapObject) (var7 Addr) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr)) (or (not (and (_Glue14 var12 var11 var10 var9 var8 var7 var6) (and (and (and (and (and (and (= (getdll var6) var5) (= (|dll::next| var5) var4)) (= (|dll::prev| var5) var3)) (= (|dll::data2| var5) var2)) (= (dll var11 var4 var3 var2) var1)) (= (O_dll var1) var0)) (valid var8 var7)))) (Inv_Heap var7 var0))))
(assert (forall ((var0 HeapObject) (var1 dll) (var2 Addr) (var3 Addr) (var4 Addr) (var5 dll) (var6 Heap) (var7 HeapObject) (var8 Addr) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Addr) (var13 HeapObject) (var14 Addr)) (or (not (and (and (Inv_Heap var14 var13) (_Glue14 var14 var12 var11 var10 var9 var8 var7)) (and (and (and (and (and (and (and (and (and (= (read var6 var14) var13) (valid var6 var14)) true) (= (getdll var7) var5)) (= (|dll::next| var5) var4)) (= (|dll::prev| var5) var3)) (= (|dll::data2| var5) var2)) (= (dll var12 var4 var3 var2) var1)) (= (O_dll var1) var0)) (= (write var9 var8 var0) var6)))) (_Glue16 var6 var14 var12 var11 var10 var13))))
(assert (forall ((var0 HeapObject) (var1 dll) (var2 Addr) (var3 Addr) (var4 Addr) (var5 dll) (var6 HeapObject) (var7 Heap) (var8 HeapObject) (var9 Addr) (var10 Heap) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr)) (or (not (and (_Glue14 var14 var13 var12 var11 var10 var9 var8) (and (and (and (and (and (and (and (and (= (read var7 var14) var6) (not (valid var7 var14))) (= (getdll var8) var5)) (= (|dll::next| var5) var4)) (= (|dll::prev| var5) var3)) (= (|dll::data2| var5) var2)) (= (dll var13 var4 var3 var2) var1)) (= (O_dll var1) var0)) (= (write var10 var9 var0) var7)))) (_Glue16 var7 var14 var13 var12 var11 var6))))
(assert (forall ((var0 dll) (var1 HeapObject) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 HeapObject) (var8 Addr)) (or (not (and (and (Inv_Heap var8 var7) (_Glue16 var6 var5 var4 var3 var2 var1)) (and (and (and (= (getdll var1) var0) (= (|dll::next| var0) var8)) (= (read var6 var8) var7)) (valid var6 var8)))) (_Glue17 var2 var3 var4 var5 var6 var8 var7))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 dll) (var3 HeapObject) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (_Glue16 var8 var7 var6 var5 var4 var3) (and (and (and (= (getdll var3) var2) (= (|dll::next| var2) var1)) (= (read var8 var1) var0)) (not (valid var8 var1))))) (_Glue17 var4 var5 var6 var7 var8 var1 var0))))
(assert (forall ((var0 HeapObject) (var1 dll) (var2 Addr) (var3 Addr) (var4 Addr) (var5 dll) (var6 HeapObject) (var7 Addr) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr)) (or (not (and (_Glue17 var12 var11 var10 var9 var8 var7 var6) (and (and (and (and (and (and (= (getdll var6) var5) (= (|dll::data1| var5) var4)) (= (|dll::next| var5) var3)) (= (|dll::prev| var5) var2)) (= (dll var4 var3 var2 var11) var1)) (= (O_dll var1) var0)) (valid var8 var7)))) (Inv_Heap var7 var0))))
(assert (forall ((var0 HeapObject) (var1 dll) (var2 Addr) (var3 Addr) (var4 Addr) (var5 dll) (var6 Addr) (var7 dll) (var8 Heap) (var9 HeapObject) (var10 Addr) (var11 Heap) (var12 Addr) (var13 Addr) (var14 Addr) (var15 HeapObject) (var16 Addr)) (or (not (and (and (Inv_Heap var16 var15) (_Glue17 var14 var13 var12 var16 var11 var10 var9)) (and (and (and (and (and (and (and (and (and (and (and (= (read var8 var16) var15) (= (getdll var15) var7)) (= (|dll::next| var7) var6)) (valid var8 var16)) true) (= (getdll var9) var5)) (= (|dll::data1| var5) var4)) (= (|dll::next| var5) var3)) (= (|dll::prev| var5) var2)) (= (dll var4 var3 var2 var13) var1)) (= (O_dll var1) var0)) (= (write var11 var10 var0) var8)))) (inv_main_5 var8 var14 var6 var12 var13))))
(assert (forall ((var0 HeapObject) (var1 dll) (var2 Addr) (var3 Addr) (var4 Addr) (var5 dll) (var6 Addr) (var7 dll) (var8 HeapObject) (var9 Heap) (var10 HeapObject) (var11 Addr) (var12 Heap) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr)) (or (not (and (_Glue17 var16 var15 var14 var13 var12 var11 var10) (and (and (and (and (and (and (and (and (and (and (= (read var9 var13) var8) (= (getdll var8) var7)) (= (|dll::next| var7) var6)) (not (valid var9 var13))) (= (getdll var10) var5)) (= (|dll::data1| var5) var4)) (= (|dll::next| var5) var3)) (= (|dll::prev| var5) var2)) (= (dll var4 var3 var2 var15) var1)) (= (O_dll var1) var0)) (= (write var12 var11 var0) var9)))) (inv_main_5 var9 var16 var6 var14 var15))))
(assert (forall ((var0 AllocResHeap) (var1 Heap) (var2 HeapObject) (var3 dll)) (or (not (and (and (= (O_dll var3) var2) (= (alloc var1 var2) var0)) (= emptyHeap var1))) (Inv_Heap (newAddr var0) var2))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Int) (var4 Addr) (var5 Heap) (var6 HeapObject) (var7 dll) (var8 AllocResHeap) (var9 Heap) (var10 HeapObject) (var11 Addr)) (or (not (and (Inv_Heap var11 var10) (and (and (and (and (and (and (= (read var9 var11) var10) (valid var9 var11)) (= (AllocResHeap var9 var11) var8)) (= (O_dll var7) var6)) (= (alloc var5 var6) var8)) (= nullAddr var4)) (= emptyHeap var5)))) (_Glue22_exp var11 var3 var2 var1 var0 var4 var9 var10))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Int) (var4 Addr) (var5 Heap) (var6 HeapObject) (var7 dll) (var8 AllocResHeap) (var9 HeapObject) (var10 Addr) (var11 Heap)) (or (not (and (and (and (and (and (and (= (read var11 var10) var9) (not (valid var11 var10))) (= (AllocResHeap var11 var10) var8)) (= (O_dll var7) var6)) (= (alloc var5 var6) var8)) (= nullAddr var4)) (= emptyHeap var5))) (_Glue22_exp var10 var3 var2 var1 var0 var4 var11 var9))))
(assert (forall ((var0 dll) (var1 HeapObject) (var2 dll) (var3 Addr) (var4 Addr) (var5 Addr) (var6 HeapObject) (var7 Heap) (var8 Addr) (var9 Int) (var10 Int) (var11 Int) (var12 Int) (var13 Addr)) (or (not (and (_Glue22_exp var13 var12 var11 var10 var9 var8 var7 var6) (and (and (and (and (and (and (= (dll var5 var8 var4 var3) var2) (= (O_dll var2) var1)) (= (getdll var6) var0)) (= (|dll::data1| var0) var5)) (= (|dll::prev| var0) var4)) (= (|dll::data2| var0) var3)) (valid var7 var13)))) (Inv_Heap var13 var1))))
(assert (forall ((var0 dll) (var1 HeapObject) (var2 dll) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 HeapObject) (var8 Heap) (var9 Addr) (var10 Int) (var11 Int) (var12 Int) (var13 Int) (var14 HeapObject) (var15 Addr)) (or (not (and (and (Inv_Heap var15 var14) (_Glue22_exp var15 var13 var12 var11 var10 var9 var8 var7)) (and (and (and (and (and (and (and (and (= (read var6 var15) var14) (valid var6 var15)) (= (dll var5 var9 var4 var3) var2)) (= (O_dll var2) var1)) (= (getdll var7) var0)) (= (|dll::data1| var0) var5)) (= (|dll::prev| var0) var4)) (= (|dll::data2| var0) var3)) (= (write var8 var15 var1) var6)))) (_Glue24_exp var6 var15 var13 var12 var11 var10 var9 var14))))
(assert (forall ((var0 dll) (var1 HeapObject) (var2 dll) (var3 Addr) (var4 Addr) (var5 Addr) (var6 HeapObject) (var7 Heap) (var8 HeapObject) (var9 Heap) (var10 Addr) (var11 Int) (var12 Int) (var13 Int) (var14 Int) (var15 Addr)) (or (not (and (_Glue22_exp var15 var14 var13 var12 var11 var10 var9 var8) (and (and (and (and (and (and (and (and (= (read var7 var15) var6) (not (valid var7 var15))) (= (dll var5 var10 var4 var3) var2)) (= (O_dll var2) var1)) (= (getdll var8) var0)) (= (|dll::data1| var0) var5)) (= (|dll::prev| var0) var4)) (= (|dll::data2| var0) var3)) (= (write var9 var15 var1) var7)))) (_Glue24_exp var7 var15 var14 var13 var12 var11 var10 var6))))
(assert (forall ((var0 dll) (var1 HeapObject) (var2 dll) (var3 Addr) (var4 Addr) (var5 Addr) (var6 HeapObject) (var7 Addr) (var8 Int) (var9 Int) (var10 Int) (var11 Int) (var12 Addr) (var13 Heap)) (or (not (and (_Glue24_exp var13 var12 var11 var10 var9 var8 var7 var6) (and (and (and (and (and (and (= (dll var5 var4 var7 var3) var2) (= (O_dll var2) var1)) (= (getdll var6) var0)) (= (|dll::data1| var0) var5)) (= (|dll::next| var0) var4)) (= (|dll::data2| var0) var3)) (valid var13 var12)))) (Inv_Heap var12 var1))))
(assert (forall ((var0 dll) (var1 HeapObject) (var2 dll) (var3 Addr) (var4 Addr) (var5 Addr) (var6 AllocResHeap) (var7 Heap) (var8 HeapObject) (var9 HeapObject) (var10 Addr) (var11 Int) (var12 Int) (var13 Int) (var14 Int) (var15 Addr) (var16 Heap)) (or (not (and (_Glue24_exp var16 var15 var14 var13 var12 var11 var10 var9) (and (and (and (and (and (and (and (and (= (O_Int var12) var8) (= (alloc var7 var8) var6)) (= (dll var5 var4 var10 var3) var2)) (= (O_dll var2) var1)) (= (getdll var9) var0)) (= (|dll::data1| var0) var5)) (= (|dll::next| var0) var4)) (= (|dll::data2| var0) var3)) (= (write var16 var15 var1) var7)))) (Inv_Heap (newAddr var6) var8))))
(assert (forall ((var0 dll) (var1 HeapObject) (var2 dll) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 HeapObject) (var8 AllocResHeap) (var9 Addr) (var10 Heap) (var11 HeapObject) (var12 HeapObject) (var13 Addr) (var14 Int) (var15 Int) (var16 Int) (var17 Int) (var18 Addr) (var19 Heap)) (or (not (and (_Glue24_exp var19 var18 var17 var16 var15 var14 var13 var12) (and (and (and (and (and (and (and (and (and (and (and (= (O_Int var17) var11) (valid var10 var9)) (= (AllocResHeap var10 var9) var8)) (= (O_Int var15) var7)) (= (alloc var6 var7) var8)) (= (dll var5 var4 var13 var3) var2)) (= (O_dll var2) var1)) (= (getdll var12) var0)) (= (|dll::data1| var0) var5)) (= (|dll::next| var0) var4)) (= (|dll::data2| var0) var3)) (= (write var19 var18 var1) var6)))) (Inv_Heap var9 var11))))
(assert (forall ((var0 dll) (var1 HeapObject) (var2 dll) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 HeapObject) (var8 AllocResHeap) (var9 Addr) (var10 Heap) (var11 HeapObject) (var12 AllocResHeap) (var13 Heap) (var14 HeapObject) (var15 HeapObject) (var16 Addr) (var17 Int) (var18 Int) (var19 Int) (var20 Int) (var21 Addr) (var22 Heap)) (or (not (and (_Glue24_exp var22 var21 var20 var19 var18 var17 var16 var15) (and (and (and (and (and (and (and (and (and (and (and (and (and (= (O_Int var17) var14) (= (alloc var13 var14) var12)) (= (O_Int var20) var11)) (= (write var10 var9 var11) var13)) (= (AllocResHeap var10 var9) var8)) (= (O_Int var18) var7)) (= (alloc var6 var7) var8)) (= (dll var5 var4 var16 var3) var2)) (= (O_dll var2) var1)) (= (getdll var15) var0)) (= (|dll::data1| var0) var5)) (= (|dll::next| var0) var4)) (= (|dll::data2| var0) var3)) (= (write var22 var21 var1) var6)))) (Inv_Heap (newAddr var12) var14))))
(assert (forall ((var0 dll) (var1 HeapObject) (var2 dll) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 HeapObject) (var8 AllocResHeap) (var9 Addr) (var10 Heap) (var11 HeapObject) (var12 Heap) (var13 HeapObject) (var14 AllocResHeap) (var15 Addr) (var16 Heap) (var17 HeapObject) (var18 HeapObject) (var19 Addr) (var20 Int) (var21 Int) (var22 Int) (var23 Int) (var24 Addr) (var25 Heap)) (or (not (and (_Glue24_exp var25 var24 var23 var22 var21 var20 var19 var18) (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (= (O_Int var22) var17) (valid var16 var15)) (= (AllocResHeap var16 var15) var14)) (= (O_Int var20) var13)) (= (alloc var12 var13) var14)) (= (O_Int var23) var11)) (= (write var10 var9 var11) var12)) (= (AllocResHeap var10 var9) var8)) (= (O_Int var21) var7)) (= (alloc var6 var7) var8)) (= (dll var5 var4 var19 var3) var2)) (= (O_dll var2) var1)) (= (getdll var18) var0)) (= (|dll::data1| var0) var5)) (= (|dll::next| var0) var4)) (= (|dll::data2| var0) var3)) (= (write var25 var24 var1) var6)))) (Inv_Heap var15 var17))))
(assert (forall ((var0 dll) (var1 HeapObject) (var2 dll) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 HeapObject) (var8 AllocResHeap) (var9 Addr) (var10 Heap) (var11 HeapObject) (var12 Heap) (var13 HeapObject) (var14 AllocResHeap) (var15 Addr) (var16 Heap) (var17 HeapObject) (var18 Heap) (var19 HeapObject) (var20 Addr) (var21 Int) (var22 Int) (var23 Int) (var24 Int) (var25 Heap) (var26 HeapObject) (var27 Addr)) (or (not (and (and (Inv_Heap var27 var26) (_Glue24_exp var25 var27 var24 var23 var22 var21 var20 var19)) (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (= (read var18 var27) var26) (valid var18 var27)) (= (O_Int var23) var17)) (= (write var16 var15 var17) var18)) (= (AllocResHeap var16 var15) var14)) (= (O_Int var21) var13)) (= (alloc var12 var13) var14)) (= (O_Int var24) var11)) (= (write var10 var9 var11) var12)) (= (AllocResHeap var10 var9) var8)) (= (O_Int var22) var7)) (= (alloc var6 var7) var8)) (= (dll var5 var4 var20 var3) var2)) (= (O_dll var2) var1)) (= (getdll var19) var0)) (= (|dll::data1| var0) var5)) (= (|dll::next| var0) var4)) (= (|dll::data2| var0) var3)) (= (write var25 var27 var1) var6)))) (_Glue30 var18 var15 var9 var27 var26))))
(assert (forall ((var0 dll) (var1 HeapObject) (var2 dll) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 HeapObject) (var8 AllocResHeap) (var9 Addr) (var10 Heap) (var11 HeapObject) (var12 Heap) (var13 HeapObject) (var14 AllocResHeap) (var15 Addr) (var16 Heap) (var17 HeapObject) (var18 HeapObject) (var19 Heap) (var20 HeapObject) (var21 Addr) (var22 Int) (var23 Int) (var24 Int) (var25 Int) (var26 Addr) (var27 Heap)) (or (not (and (_Glue24_exp var27 var26 var25 var24 var23 var22 var21 var20) (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (= (read var19 var26) var18) (not (valid var19 var26))) (= (O_Int var24) var17)) (= (write var16 var15 var17) var19)) (= (AllocResHeap var16 var15) var14)) (= (O_Int var22) var13)) (= (alloc var12 var13) var14)) (= (O_Int var25) var11)) (= (write var10 var9 var11) var12)) (= (AllocResHeap var10 var9) var8)) (= (O_Int var23) var7)) (= (alloc var6 var7) var8)) (= (dll var5 var4 var21 var3) var2)) (= (O_dll var2) var1)) (= (getdll var20) var0)) (= (|dll::data1| var0) var5)) (= (|dll::next| var0) var4)) (= (|dll::data2| var0) var3)) (= (write var27 var26 var1) var6)))) (_Glue30 var19 var15 var9 var26 var18))))
(assert (forall ((var0 HeapObject) (var1 dll) (var2 Addr) (var3 Addr) (var4 Addr) (var5 dll) (var6 HeapObject) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (_Glue30 var10 var9 var8 var7 var6) (and (and (and (and (and (and (= (getdll var6) var5) (= (|dll::next| var5) var4)) (= (|dll::prev| var5) var3)) (= (|dll::data2| var5) var2)) (= (dll var8 var4 var3 var2) var1)) (= (O_dll var1) var0)) (valid var10 var7)))) (Inv_Heap var7 var0))))
(assert (forall ((var0 HeapObject) (var1 dll) (var2 Addr) (var3 Addr) (var4 Addr) (var5 dll) (var6 Heap) (var7 HeapObject) (var8 Addr) (var9 Addr) (var10 Heap) (var11 HeapObject) (var12 Addr)) (or (not (and (and (Inv_Heap var12 var11) (_Glue30 var10 var9 var8 var12 var7)) (and (and (and (and (and (and (and (and (= (read var6 var12) var11) (valid var6 var12)) (= (getdll var7) var5)) (= (|dll::next| var5) var4)) (= (|dll::prev| var5) var3)) (= (|dll::data2| var5) var2)) (= (dll var8 var4 var3 var2) var1)) (= (O_dll var1) var0)) (= (write var10 var12 var0) var6)))) (_Glue32 var6 var9 var8 var12 var11))))
(assert (forall ((var0 HeapObject) (var1 dll) (var2 Addr) (var3 Addr) (var4 Addr) (var5 dll) (var6 HeapObject) (var7 Heap) (var8 HeapObject) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Heap)) (or (not (and (_Glue30 var12 var11 var10 var9 var8) (and (and (and (and (and (and (and (and (= (read var7 var9) var6) (not (valid var7 var9))) (= (getdll var8) var5)) (= (|dll::next| var5) var4)) (= (|dll::prev| var5) var3)) (= (|dll::data2| var5) var2)) (= (dll var10 var4 var3 var2) var1)) (= (O_dll var1) var0)) (= (write var12 var9 var0) var7)))) (_Glue32 var7 var11 var10 var9 var6))))
(assert (forall ((var0 HeapObject) (var1 dll) (var2 Addr) (var3 Addr) (var4 Addr) (var5 dll) (var6 HeapObject) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (_Glue32 var10 var9 var8 var7 var6) (and (and (and (and (and (and (= (getdll var6) var5) (= (|dll::data1| var5) var4)) (= (|dll::next| var5) var3)) (= (|dll::prev| var5) var2)) (= (dll var4 var3 var2 var9) var1)) (= (O_dll var1) var0)) (valid var10 var7)))) (Inv_Heap var7 var0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 HeapObject) (var3 dll) (var4 Addr) (var5 Addr) (var6 Addr) (var7 dll) (var8 HeapObject) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Heap)) (or (not (and (_Glue32 var12 var11 var10 var9 var8) (and (and (and (and (and (and (and (= (getdll var8) var7) (= (|dll::data1| var7) var6)) (= (|dll::next| var7) var5)) (= (|dll::prev| var7) var4)) (= (dll var6 var5 var4 var11) var3)) (= (O_dll var3) var2)) (= (write var12 var9 var2) var1)) (= var0 var9)))) (inv_main_5 var1 var0 var9 var10 var11))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main_5 var5 var4 var3 var2 var1) (= var0 var4))) (inv_main2430_5 var5 var0 var4))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 HeapObject) (var4 Addr)) (not (and (and (Inv_Heap var4 var3) (inv_main2443_9 var2 var4 var1)) (and (and (and (and (not (= var4 var0)) (= (read var2 var4) var3)) (= defObj var3)) (= nullAddr var0)) (valid var2 var4))))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main2443_9 var4 var3 var2) (and (and (and (and (not (= var3 var1)) (= (read var4 var3) var0)) (= defObj var0)) (= nullAddr var1)) (not (valid var4 var3)))))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Heap) (var3 HeapObject) (var4 Addr)) (or (not (and (and (Inv_Heap var4 var3) (inv_main2430_5 var2 var4 var1)) (and (and (= nullAddr var1) (= (read var2 var4) var3)) (valid var2 var4)))) (_Glue0 var0 var1 var2 var4 var3))))
(assert (forall ((var0 HeapObject) (var1 HeapObject) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main2430_5 var4 var3 var2) (and (and (= nullAddr var2) (= (read var4 var3) var1)) (not (valid var4 var3))))) (_Glue0 var0 var2 var4 var3 var1))))
(assert (forall ((var0 Addr) (var1 dll) (var2 HeapObject) (var3 HeapObject) (var4 Addr) (var5 Heap) (var6 Addr) (var7 HeapObject)) (or (not (and (_Glue0 var7 var6 var5 var4 var3) (and (and (and (and (= defObj var2) (= (getdll var3) var1)) (= (|dll::data1| var1) var0)) (not (= var4 var6))) (valid var5 var0)))) (Inv_Heap var0 var2))))
(assert (forall ((var0 Addr) (var1 dll) (var2 HeapObject) (var3 Heap) (var4 HeapObject) (var5 Heap) (var6 Addr) (var7 HeapObject) (var8 HeapObject) (var9 Addr)) (or (not (and (and (Inv_Heap var9 var8) (_Glue0 var7 var6 var5 var9 var4)) (and (and (and (and (and (and (and (= (read var3 var9) var8) (valid var3 var9)) true) (= defObj var2)) (= (getdll var4) var1)) (= (|dll::data1| var1) var0)) (= (write var5 var0 var2) var3)) (not (= var9 var6))))) (_Glue2 var3 var7 var6 var8))))
(assert (forall ((var0 Addr) (var1 dll) (var2 HeapObject) (var3 HeapObject) (var4 Heap) (var5 HeapObject) (var6 Addr) (var7 Heap) (var8 Addr) (var9 HeapObject)) (or (not (and (_Glue0 var9 var8 var7 var6 var5) (and (and (and (and (and (and (= (read var4 var6) var3) (not (valid var4 var6))) (= defObj var2)) (= (getdll var5) var1)) (= (|dll::data1| var1) var0)) (= (write var7 var0 var2) var4)) (not (= var6 var8))))) (_Glue2 var4 var9 var8 var3))))
(assert (forall ((var0 dll) (var1 HeapObject) (var2 Addr) (var3 Heap) (var4 HeapObject) (var5 Addr)) (not (and (and (Inv_Heap var5 var4) (_Glue2 var3 var4 var2 var1)) (and (and (and (and (and (= defObj var4) (= (getdll var1) var0)) (= (|dll::data2| var0) var5)) (not (= var5 var2))) (= (read var3 var5) var4)) (valid var3 var5))))))
(assert (forall ((var0 Addr) (var1 dll) (var2 HeapObject) (var3 Addr) (var4 HeapObject) (var5 Heap)) (not (and (_Glue2 var5 var4 var3 var2) (and (and (and (and (and (= defObj var4) (= (getdll var2) var1)) (= (|dll::data2| var1) var0)) (not (= var0 var3))) (= (read var5 var0) var4)) (not (valid var5 var0)))))))
(assert (forall ((var0 Addr) (var1 dll) (var2 Addr) (var3 Addr) (var4 Heap) (var5 HeapObject) (var6 Addr)) (or (not (and (and (Inv_Heap var6 var5) (inv_main2430_5 var4 var3 var6)) (and (and (and (and (and (not (= var6 var2)) (= nullAddr var2)) (= (read var4 var6) var5)) (= (getdll var5) var1)) (= (|dll::next| var1) var0)) (valid var4 var6)))) (inv_main2430_5 var4 var3 var0))))
(assert (forall ((var0 Addr) (var1 dll) (var2 HeapObject) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main2430_5 var6 var5 var4) (and (and (and (and (and (not (= var4 var3)) (= nullAddr var3)) (= (read var6 var4) var2)) (= (getdll var2) var1)) (= (|dll::next| var1) var0)) (not (valid var6 var4))))) (inv_main2430_5 var6 var5 var0))))
(check-sat)
