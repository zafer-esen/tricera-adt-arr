(set-logic HORN)
(set-info :source |
    Benchmark: 
    Output by Princess (http://www.philipp.ruemmer.org/princess.shtml)
|)
(declare-heap Heap Addr HeapObject
 defObj
 ((HeapObject 0) (node 0)) (
  (
   (O_Int (getInt Int))
   (O_UInt (getUInt Int))
   (O_Addr (getAddr Addr))
   (O_AddrRange (getAddrRange AddrRange))
   (O_node (getnode node))
   (defObj)
  )
  (
   (node (|node::left| Addr) (|node::right| Addr) (|node::parent| Addr) (|node::value| Int))
  )
))
(declare-fun _Glue4 (Addr Addr Heap Addr HeapObject) Bool)
(declare-fun _Glue25 (Heap Int Addr HeapObject) Bool)
(declare-fun _Glue6 (Heap Addr Addr Addr HeapObject) Bool)
(declare-fun _Glue9 (Heap Addr Addr HeapObject) Bool)
(declare-fun _Glue23 (Heap Addr Int Addr HeapObject) Bool)
(declare-fun _Glue21 (Heap Addr Int Addr HeapObject) Bool)
(declare-fun _Glue13 (Addr Addr Heap Addr HeapObject) Bool)
(declare-fun _Glue27 (Int Addr Heap HeapObject) Bool)
(declare-fun _Glue12 (Heap Addr Addr HeapObject) Bool)
(declare-fun _Glue10 (Addr Addr Heap Addr HeapObject) Bool)
(declare-fun Inv_Heap_exp_exp (Addr Addr Addr Addr Int) Bool)
(declare-fun _Glue7 (Addr Addr Addr Heap Addr HeapObject) Bool)
(declare-fun inv_main_10 (Heap Addr Addr) Bool)
(declare-fun inv_main586_5 (Heap Addr) Bool)
(declare-fun _Glue29 (Heap Addr Int Addr HeapObject) Bool)
(declare-fun inv_main579_34 () Bool)
(declare-fun inv_main_25 (Heap Addr) Bool)
(declare-fun _Glue31 (Heap Int Addr HeapObject) Bool)
(declare-fun _Glue19 (Addr Int Addr Heap HeapObject) Bool)
(declare-fun _Glue17 (Addr Heap HeapObject) Bool)
(declare-fun _Glue32 (Addr Heap HeapObject) Bool)
(declare-fun _Glue1 (Addr Addr Addr Heap HeapObject) Bool)
(declare-fun _Glue28 (Addr Int Addr Heap) Bool)
(declare-fun _Glue16 (Addr Heap HeapObject) Bool)
(declare-fun _Glue3 (Heap Addr Addr HeapObject) Bool)
(declare-fun _Glue15 (Addr Heap HeapObject) Bool)
(assert (forall ((var0 Addr) (var1 HeapObject) (var2 node) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr)) (or (not (and (and (Inv_Heap_exp_exp var8 var7 var6 var5 var4) (inv_main_25 var3 var8)) (and (and (and (and (and (= (O_node var2) var1) (= (node var7 var6 var5 var4) var2)) (= nullAddr var0)) (not (= var8 var0))) (= (read var3 var8) var1)) (valid var3 var8)))) (_Glue17 var0 var3 var1))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main_25 var3 var2) (and (and (and (= nullAddr var1) (not (= var2 var1))) (= (read var3 var2) var0)) (not (valid var3 var2))))) (_Glue17 var1 var3 var0))))
(assert (forall ((var0 node) (var1 HeapObject) (var2 node) (var3 HeapObject) (var4 Heap) (var5 Addr) (var6 Int) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr)) (not (and (and (Inv_Heap_exp_exp var10 var9 var8 var7 var6) (_Glue17 var5 var4 var3)) (and (and (and (and (and (and (and (= (O_node var2) var1) (= (node var9 var8 var7 var6) var2)) (= (getnode var3) var0)) (= (|node::left| var0) var10)) (not (= var10 var5))) (= (read var4 var10) var1)) (not (= var6 42))) (valid var4 var10))))))
(assert (forall ((var0 Int) (var1 node) (var2 HeapObject) (var3 Addr) (var4 node) (var5 HeapObject) (var6 Heap) (var7 Addr)) (not (and (_Glue17 var7 var6 var5) (and (and (and (and (and (and (and (= (getnode var5) var4) (= (|node::left| var4) var3)) (not (= var3 var7))) (= (read var6 var3) var2)) (= (getnode var2) var1)) (= (|node::value| var1) var0)) (not (= var0 42))) (not (valid var6 var3)))))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr)) (or (not (and (and (Inv_Heap_exp_exp var6 var5 var4 var3 0) (inv_main_25 var2 var6)) (and (and (and (and (and (= (O_node var1) var0) (= (node var5 var4 var3 0) var1)) (not (= var6 var5))) (= nullAddr var5)) (= (read var2 var6) var0)) (valid var2 var6)))) inv_main579_34)))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main_25 var4 var3) (and (and (and (and (and (and (not (= var3 var2)) (= (|node::value| var1) 0)) (= nullAddr var2)) (= (read var4 var3) var0)) (= (getnode var0) var1)) (= (|node::left| var1) var2)) (not (valid var4 var3))))) inv_main579_34)))
(assert (forall ((var0 Addr) (var1 HeapObject) (var2 node) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr)) (or (not (and (and (Inv_Heap_exp_exp var8 var7 var6 var5 var4) (inv_main_25 var3 var8)) (and (and (and (and (and (= (O_node var2) var1) (= (node var7 var6 var5 var4) var2)) (= nullAddr var0)) (not (= var8 var0))) (= (read var3 var8) var1)) (valid var3 var8)))) (_Glue15 var0 var3 var1))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main_25 var3 var2) (and (and (and (= nullAddr var1) (not (= var2 var1))) (= (read var3 var2) var0)) (not (valid var3 var2))))) (_Glue15 var1 var3 var0))))
(assert (forall ((var0 node) (var1 HeapObject) (var2 node) (var3 HeapObject) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr)) (or (not (and (and (Inv_Heap_exp_exp var9 var8 var7 var6 42) (_Glue15 var5 var4 var3)) (and (and (and (and (and (and (and (= (O_node var2) var1) (= (node var8 var7 var6 42) var2)) (= (getnode var3) var0)) (= (|node::value| var0) 0)) (= (|node::left| var0) var9)) (not (= var9 var5))) (= (read var4 var9) var1)) (valid var4 var9)))) inv_main579_34)))
(assert (forall ((var0 node) (var1 HeapObject) (var2 Addr) (var3 node) (var4 HeapObject) (var5 Heap) (var6 Addr)) (or (not (and (_Glue15 var6 var5 var4) (and (and (and (and (and (and (and (= (getnode var4) var3) (= (|node::value| var3) 0)) (= (|node::left| var3) var2)) (not (= var2 var6))) (= (read var5 var2) var1)) (= (getnode var1) var0)) (= (|node::value| var0) 42)) (not (valid var5 var2))))) inv_main579_34)))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (and (inv_main_10 var2 var1 var0) (and (and (not (= var1 var0)) (not (= var1 var0))) (= nullAddr var0)))) (inv_main_25 var2 var1))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Heap) (var3 Int) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr)) (or (not (and (and (Inv_Heap_exp_exp var7 var6 var5 var4 var3) (inv_main586_5 var2 var7)) (and (and (and (= (O_node var1) var0) (= (node var6 var5 var4 var3) var1)) (= (read var2 var7) var0)) (valid var2 var7)))) (_Glue32 var7 var2 var0))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Heap)) (or (not (and (inv_main586_5 var2 var1) (and (= (read var2 var1) var0) (not (valid var2 var1))))) (_Glue32 var1 var2 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 node) (var5 HeapObject) (var6 Heap) (var7 Addr)) (or (not (and (_Glue32 var7 var6 var5) (and (and (and (and (and (and (= (getnode var5) var4) (= (|node::left| var4) var3)) (= (|node::right| var4) var2)) (= (|node::value| var4) var1)) (= nullAddr var0)) (not (= var7 var0))) (valid var6 var7)))) (Inv_Heap_exp_exp var7 var3 var2 var0 var1))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 HeapObject) (var3 node) (var4 Addr) (var5 Int) (var6 Addr) (var7 Addr) (var8 node) (var9 HeapObject) (var10 Heap) (var11 Addr)) (or (not (and (_Glue32 var11 var10 var9) (and (and (and (and (and (and (and (and (and (= (getnode var9) var8) (= (|node::left| var8) var7)) (= (|node::right| var8) var6)) (= (|node::value| var8) var5)) (= nullAddr var4)) (not (= var11 var4))) (= (node var7 var6 var4 var5) var3)) (= (O_node var3) var2)) (= (write var10 var11 var2) var1)) (= var0 var11)))) (inv_main_10 var1 var0 var11))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Heap) (var3 Int) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr)) (or (not (and (and (Inv_Heap_exp_exp var7 var6 var5 var4 var3) (inv_main_25 var2 var7)) (and (and (and (and (and (and (= (O_node var1) var0) (= (node var6 var5 var4 var3) var1)) (not (= var7 var6))) (not (= var3 0))) (= nullAddr var6)) (= (read var2 var7) var0)) (valid var2 var7)))) (inv_main_25 var2 var4))))
(assert (forall ((var0 Addr) (var1 node) (var2 HeapObject) (var3 Int) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main_25 var6 var5) (and (and (and (and (and (and (and (and (not (= var5 var4)) (not (= var3 0))) (= nullAddr var4)) (= (read var6 var5) var2)) (= (getnode var2) var1)) (= (|node::left| var1) var4)) (= (|node::value| var1) var3)) (= (|node::parent| var1) var0)) (not (valid var6 var5))))) (inv_main_25 var6 var0))))
(assert (forall ((var0 AllocResHeap) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 HeapObject) (var6 node) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main_10 var9 var8 var7) (and (and (= (O_node var6) var5) (= (node var4 var3 var2 var1) var6)) (= (alloc var9 var5) var0)))) (Inv_Heap_exp_exp (newAddr var0) var4 var3 var2 var1))))
(assert (forall ((var0 AllocResHeap) (var1 Addr) (var2 Heap) (var3 HeapObject) (var4 node) (var5 HeapObject) (var6 node) (var7 Addr) (var8 Heap) (var9 Int) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr)) (or (not (and (and (Inv_Heap_exp_exp var13 var12 var11 var10 var9) (inv_main_10 var8 var7 var13)) (and (and (and (and (and (and (= (O_node var6) var5) (= (O_node var4) var3)) (= (AllocResHeap var2 var1) var0)) (= (node var12 var11 var10 var9) var6)) (= (read var2 var13) var5)) (valid var2 var13)) (= (alloc var8 var3) var0)))) (_Glue1 var13 var7 var1 var2 var5))))
(assert (forall ((var0 AllocResHeap) (var1 Addr) (var2 HeapObject) (var3 node) (var4 HeapObject) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main_10 var8 var7 var6) (and (and (and (and (= (read var5 var6) var4) (not (valid var5 var6))) (= (O_node var3) var2)) (= (AllocResHeap var5 var1) var0)) (= (alloc var8 var2) var0)))) (_Glue1 var6 var7 var1 var5 var4))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 node) (var4 HeapObject) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr)) (or (not (and (_Glue1 var8 var7 var6 var5 var4) (and (and (and (and (= (getnode var4) var3) (= (|node::right| var3) var2)) (= (|node::parent| var3) var1)) (= (|node::value| var3) var0)) (valid var5 var8)))) (Inv_Heap_exp_exp var8 var6 var2 var1 var0))))
(assert (forall ((var0 node) (var1 Heap) (var2 HeapObject) (var3 node) (var4 Int) (var5 Addr) (var6 Addr) (var7 HeapObject) (var8 node) (var9 HeapObject) (var10 Heap) (var11 Addr) (var12 Addr) (var13 Int) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr)) (or (not (and (and (Inv_Heap_exp_exp var17 var16 var15 var14 var13) (_Glue1 var17 var12 var11 var10 var9)) (and (and (and (and (and (and (and (and (and (and (= (O_node var8) var7) (= (node var11 var6 var5 var4) var3)) (= (O_node var3) var2)) (= (node var16 var15 var14 var13) var8)) (= (read var1 var17) var7)) (valid var1 var17)) (= (getnode var9) var0)) (= (|node::right| var0) var6)) (= (|node::parent| var0) var5)) (= (|node::value| var0) var4)) (= (write var10 var17 var2) var1)))) (_Glue3 var1 var17 var12 var7))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Int) (var3 Addr) (var4 Addr) (var5 node) (var6 HeapObject) (var7 Heap) (var8 HeapObject) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Addr)) (or (not (and (_Glue1 var12 var11 var10 var9 var8) (and (and (and (and (and (and (and (and (= (read var7 var12) var6) (not (valid var7 var12))) (= (getnode var8) var5)) (= (|node::right| var5) var4)) (= (|node::parent| var5) var3)) (= (|node::value| var5) var2)) (= (node var10 var4 var3 var2) var1)) (= (O_node var1) var0)) (= (write var9 var12 var0) var7)))) (_Glue3 var7 var12 var11 var6))))
(assert (forall ((var0 node) (var1 HeapObject) (var2 node) (var3 HeapObject) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Int) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr)) (or (not (and (and (Inv_Heap_exp_exp var11 var10 var9 var8 var7) (_Glue3 var6 var5 var4 var3)) (and (and (and (and (and (= (O_node var2) var1) (= (node var10 var9 var8 var7) var2)) (= (getnode var3) var0)) (= (|node::left| var0) var11)) (= (read var6 var11) var1)) (valid var6 var11)))) (_Glue4 var4 var5 var6 var11 var1))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 node) (var3 HeapObject) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (_Glue3 var6 var5 var4 var3) (and (and (and (= (getnode var3) var2) (= (|node::left| var2) var1)) (= (read var6 var1) var0)) (not (valid var6 var1))))) (_Glue4 var4 var5 var6 var1 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 node) (var5 HeapObject) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Addr)) (or (not (and (_Glue4 var9 var8 var7 var6 var5) (and (and (and (and (and (and (= (getnode var5) var4) (= (|node::right| var4) var3)) (= (|node::parent| var4) var2)) (= (|node::value| var4) var1)) (= nullAddr var0)) (not (= var8 var0))) (valid var7 var6)))) (Inv_Heap_exp_exp var6 var0 var3 var2 var1))))
(assert (forall ((var0 node) (var1 Heap) (var2 HeapObject) (var3 node) (var4 Int) (var5 Addr) (var6 Addr) (var7 Addr) (var8 HeapObject) (var9 node) (var10 HeapObject) (var11 Addr) (var12 Heap) (var13 Addr) (var14 Int) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr)) (or (not (and (and (Inv_Heap_exp_exp var18 var17 var16 var15 var14) (_Glue4 var13 var18 var12 var11 var10)) (and (and (and (and (and (and (and (and (and (and (and (and (and (= (O_node var9) var8) (= (node var7 var6 var5 var4) var3)) (= (O_node var3) var2)) (= (node var17 var16 var15 var14) var9)) (not (= var18 var7))) (= (read var1 var18) var8)) (valid var1 var18)) (= (getnode var10) var0)) (= (|node::right| var0) var6)) (= (|node::parent| var0) var5)) (= (|node::value| var0) var4)) (= nullAddr var7)) (not (= var18 var7))) (= (write var12 var11 var2) var1)))) (_Glue6 var1 var7 var13 var18 var8))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Int) (var3 Addr) (var4 Addr) (var5 node) (var6 HeapObject) (var7 Heap) (var8 Addr) (var9 HeapObject) (var10 Addr) (var11 Heap) (var12 Addr) (var13 Addr)) (or (not (and (_Glue4 var13 var12 var11 var10 var9) (and (and (and (and (and (and (and (and (and (and (and (not (= var12 var8)) (= (read var7 var12) var6)) (not (valid var7 var12))) (= (getnode var9) var5)) (= (|node::right| var5) var4)) (= (|node::parent| var5) var3)) (= (|node::value| var5) var2)) (= nullAddr var8)) (not (= var12 var8))) (= (node var8 var4 var3 var2) var1)) (= (O_node var1) var0)) (= (write var11 var10 var0) var7)))) (_Glue6 var7 var8 var13 var12 var6))))
(assert (forall ((var0 node) (var1 HeapObject) (var2 node) (var3 HeapObject) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Int) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr)) (or (not (and (and (Inv_Heap_exp_exp var12 var11 var10 var9 var8) (_Glue6 var7 var6 var5 var4 var3)) (and (and (and (and (and (and (= (O_node var2) var1) (= (node var11 var10 var9 var8) var2)) (not (= var4 var6))) (= (getnode var3) var0)) (= (|node::left| var0) var12)) (= (read var7 var12) var1)) (valid var7 var12)))) (_Glue7 var4 var5 var6 var7 var12 var1))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 node) (var3 HeapObject) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (_Glue6 var7 var6 var5 var4 var3) (and (and (and (and (not (= var4 var6)) (= (getnode var3) var2)) (= (|node::left| var2) var1)) (= (read var7 var1) var0)) (not (valid var7 var1))))) (_Glue7 var4 var5 var6 var7 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 node) (var4 HeapObject) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Addr)) (or (not (and (_Glue7 var9 var8 var7 var6 var5 var4) (and (and (and (and (and (not (= var9 var7)) (= (getnode var4) var3)) (= (|node::left| var3) var2)) (= (|node::parent| var3) var1)) (= (|node::value| var3) var0)) (valid var6 var5)))) (Inv_Heap_exp_exp var5 var2 var7 var1 var0))))
(assert (forall ((var0 node) (var1 Heap) (var2 Addr) (var3 HeapObject) (var4 node) (var5 Int) (var6 Addr) (var7 Addr) (var8 HeapObject) (var9 node) (var10 HeapObject) (var11 Addr) (var12 Heap) (var13 Addr) (var14 Addr) (var15 Int) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Addr)) (or (not (and (and (Inv_Heap_exp_exp var19 var18 var17 var16 var15) (_Glue7 var19 var14 var13 var12 var11 var10)) (and (and (and (and (and (and (and (and (and (and (and (and (= (O_node var9) var8) (= (node var7 var13 var6 var5) var4)) (= (O_node var4) var3)) (= (node var18 var17 var16 var15) var9)) (not (= var19 var2))) (= (read var1 var19) var8)) (valid var1 var19)) (not (= var19 var13))) (= (getnode var10) var0)) (= (|node::left| var0) var7)) (= (|node::parent| var0) var6)) (= (|node::value| var0) var5)) (= (write var12 var11 var3) var1)))) (_Glue9 var1 var19 var14 var8))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Int) (var3 Addr) (var4 Addr) (var5 node) (var6 HeapObject) (var7 Heap) (var8 Addr) (var9 HeapObject) (var10 Addr) (var11 Heap) (var12 Addr) (var13 Addr) (var14 Addr)) (or (not (and (_Glue7 var14 var13 var12 var11 var10 var9) (and (and (and (and (and (and (and (and (and (and (not (= var14 var8)) (= (read var7 var14) var6)) (not (valid var7 var14))) (not (= var14 var12))) (= (getnode var9) var5)) (= (|node::left| var5) var4)) (= (|node::parent| var5) var3)) (= (|node::value| var5) var2)) (= (node var4 var12 var3 var2) var1)) (= (O_node var1) var0)) (= (write var11 var10 var0) var7)))) (_Glue9 var7 var14 var13 var6))))
(assert (forall ((var0 node) (var1 Addr) (var2 HeapObject) (var3 node) (var4 HeapObject) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Int) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr)) (or (not (and (and (Inv_Heap_exp_exp var12 var11 var10 var9 var8) (_Glue9 var7 var6 var5 var4)) (and (and (and (and (and (and (= (O_node var3) var2) (= (node var11 var10 var9 var8) var3)) (not (= var6 var1))) (= (getnode var4) var0)) (= (|node::left| var0) var12)) (= (read var7 var12) var2)) (valid var7 var12)))) (_Glue10 var5 var6 var7 var12 var2))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 node) (var3 Addr) (var4 HeapObject) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (_Glue9 var7 var6 var5 var4) (and (and (and (and (not (= var6 var3)) (= (getnode var4) var2)) (= (|node::left| var2) var1)) (= (read var7 var1) var0)) (not (valid var7 var1))))) (_Glue10 var5 var6 var7 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 node) (var5 Addr) (var6 HeapObject) (var7 Addr) (var8 Heap) (var9 Addr) (var10 Addr)) (or (not (and (_Glue10 var10 var9 var8 var7 var6) (and (and (and (and (and (and (not (= var9 var5)) (= (getnode var6) var4)) (= (|node::left| var4) var3)) (= (|node::right| var4) var2)) (= (|node::parent| var4) var1)) (valid var8 var7)) (= var0 42)))) (Inv_Heap_exp_exp var7 var3 var2 var1 var0))))
(assert (forall ((var0 node) (var1 Addr) (var2 Heap) (var3 Addr) (var4 HeapObject) (var5 node) (var6 Addr) (var7 Addr) (var8 Addr) (var9 HeapObject) (var10 node) (var11 HeapObject) (var12 Addr) (var13 Heap) (var14 Addr) (var15 Int) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Addr)) (or (not (and (and (Inv_Heap_exp_exp var19 var18 var17 var16 var15) (_Glue10 var14 var19 var13 var12 var11)) (and (and (and (and (and (and (and (and (and (and (and (and (= (O_node var10) var9) (= (node var8 var7 var6 42) var5)) (= (O_node var5) var4)) (= (node var18 var17 var16 var15) var10)) (not (= var19 var3))) (= (read var2 var19) var9)) (valid var2 var19)) (not (= var19 var1))) (= (getnode var11) var0)) (= (|node::left| var0) var8)) (= (|node::right| var0) var7)) (= (|node::parent| var0) var6)) (= (write var13 var12 var4) var2)))) (_Glue12 var2 var14 var19 var9))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Addr) (var4 Addr) (var5 node) (var6 Addr) (var7 HeapObject) (var8 Heap) (var9 Addr) (var10 HeapObject) (var11 Addr) (var12 Heap) (var13 Addr) (var14 Addr)) (or (not (and (_Glue10 var14 var13 var12 var11 var10) (and (and (and (and (and (and (and (and (and (and (not (= var13 var9)) (= (read var8 var13) var7)) (not (valid var8 var13))) (not (= var13 var6))) (= (getnode var10) var5)) (= (|node::left| var5) var4)) (= (|node::right| var5) var3)) (= (|node::parent| var5) var2)) (= (node var4 var3 var2 42) var1)) (= (O_node var1) var0)) (= (write var12 var11 var0) var8)))) (_Glue12 var8 var14 var13 var7))))
(assert (forall ((var0 node) (var1 Addr) (var2 HeapObject) (var3 node) (var4 HeapObject) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Int) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr)) (or (not (and (and (Inv_Heap_exp_exp var12 var11 var10 var9 var8) (_Glue12 var7 var6 var5 var4)) (and (and (and (and (and (and (= (O_node var3) var2) (= (node var11 var10 var9 var8) var3)) (not (= var5 var1))) (= (getnode var4) var0)) (= (|node::left| var0) var12)) (= (read var7 var12) var2)) (valid var7 var12)))) (_Glue13 var5 var6 var7 var12 var2))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 node) (var3 Addr) (var4 HeapObject) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (_Glue12 var7 var6 var5 var4) (and (and (and (and (not (= var5 var3)) (= (getnode var4) var2)) (= (|node::left| var2) var1)) (= (read var7 var1) var0)) (not (valid var7 var1))))) (_Glue13 var5 var6 var7 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 node) (var4 Addr) (var5 HeapObject) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Addr)) (or (not (and (_Glue13 var9 var8 var7 var6 var5) (and (and (and (and (and (not (= var9 var4)) (= (getnode var5) var3)) (= (|node::left| var3) var2)) (= (|node::right| var3) var1)) (= (|node::value| var3) var0)) (valid var7 var6)))) (Inv_Heap_exp_exp var6 var2 var1 var9 var0))))
(assert (forall ((var0 node) (var1 Addr) (var2 Heap) (var3 Addr) (var4 HeapObject) (var5 node) (var6 Int) (var7 Addr) (var8 Addr) (var9 HeapObject) (var10 node) (var11 HeapObject) (var12 Addr) (var13 Heap) (var14 Addr) (var15 Int) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Addr)) (or (not (and (and (Inv_Heap_exp_exp var19 var18 var17 var16 var15) (_Glue13 var19 var14 var13 var12 var11)) (and (and (and (and (and (and (and (and (and (and (and (and (= (O_node var10) var9) (= (node var8 var7 var19 var6) var5)) (= (O_node var5) var4)) (= (node var18 var17 var16 var15) var10)) (not (= var19 var3))) (= (read var2 var19) var9)) (valid var2 var19)) (not (= var19 var1))) (= (getnode var11) var0)) (= (|node::left| var0) var8)) (= (|node::right| var0) var7)) (= (|node::value| var0) var6)) (= (write var13 var12 var4) var2)))) (inv_main_10 var2 var14 var17))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Int) (var3 Addr) (var4 Addr) (var5 node) (var6 Addr) (var7 Addr) (var8 node) (var9 HeapObject) (var10 Heap) (var11 Addr) (var12 HeapObject) (var13 Addr) (var14 Heap) (var15 Addr) (var16 Addr)) (or (not (and (_Glue13 var16 var15 var14 var13 var12) (and (and (and (and (and (and (and (and (and (and (and (and (not (= var16 var11)) (= (read var10 var16) var9)) (= (getnode var9) var8)) (= (|node::right| var8) var7)) (not (valid var10 var16))) (not (= var16 var6))) (= (getnode var12) var5)) (= (|node::left| var5) var4)) (= (|node::right| var5) var3)) (= (|node::value| var5) var2)) (= (node var4 var3 var16 var2) var1)) (= (O_node var1) var0)) (= (write var14 var13 var0) var10)))) (inv_main_10 var10 var15 var7))))
(assert (forall ((var0 Heap) (var1 Addr)) (or (not (and (= nullAddr var1) (= emptyHeap var0))) (inv_main586_5 var0 var1))))
(assert (not inv_main579_34))
(assert (forall ((var0 Addr) (var1 HeapObject) (var2 node) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr)) (or (not (and (and (Inv_Heap_exp_exp var8 var7 var6 var5 var4) (inv_main_25 var3 var8)) (and (and (and (and (and (= (O_node var2) var1) (= (node var7 var6 var5 var4) var2)) (= nullAddr var0)) (not (= var8 var0))) (= (read var3 var8) var1)) (valid var3 var8)))) (_Glue16 var0 var3 var1))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main_25 var3 var2) (and (and (and (= nullAddr var1) (not (= var2 var1))) (= (read var3 var2) var0)) (not (valid var3 var2))))) (_Glue16 var1 var3 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 node) (var3 HeapObject) (var4 node) (var5 HeapObject) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr)) (or (not (and (and (Inv_Heap_exp_exp var11 var10 var9 var8 42) (_Glue16 var7 var6 var5)) (and (and (and (and (and (and (and (and (and (= (O_node var4) var3) (= (node var10 var9 var8 42) var4)) (= (getnode var5) var2)) (= (|node::parent| var2) var1)) (= (|node::value| var2) var0)) (not (= var0 0))) (= (|node::left| var2) var11)) (not (= var11 var7))) (= (read var6 var11) var3)) (valid var6 var11)))) (inv_main_25 var6 var1))))
(assert (forall ((var0 node) (var1 HeapObject) (var2 Addr) (var3 Int) (var4 Addr) (var5 node) (var6 HeapObject) (var7 Heap) (var8 Addr)) (or (not (and (_Glue16 var8 var7 var6) (and (and (and (and (and (and (and (and (and (= (getnode var6) var5) (= (|node::parent| var5) var4)) (= (|node::value| var5) var3)) (not (= var3 0))) (= (|node::left| var5) var2)) (not (= var2 var8))) (= (read var7 var2) var1)) (= (getnode var1) var0)) (= (|node::value| var0) 42)) (not (valid var7 var2))))) (inv_main_25 var7 var4))))
(assert (forall ((var0 AllocResHeap) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 HeapObject) (var6 node) (var7 Addr) (var8 Heap)) (or (not (and (inv_main586_5 var8 var7) (and (and (= (O_node var6) var5) (= (node var4 var3 var2 var1) var6)) (= (alloc var8 var5) var0)))) (Inv_Heap_exp_exp (newAddr var0) var4 var3 var2 var1))))
(assert (forall ((var0 Int) (var1 AllocResHeap) (var2 Heap) (var3 HeapObject) (var4 node) (var5 HeapObject) (var6 node) (var7 Addr) (var8 Heap) (var9 Addr) (var10 Heap) (var11 Int) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr)) (or (not (and (and (and (Inv_Heap_exp_exp var15 var14 var13 var12 var11) (inv_main586_5 var10 var9)) (inv_main586_5 var8 var7)) (and (and (and (and (and (and (= (O_node var6) var5) (= (O_node var4) var3)) (= (AllocResHeap var2 var15) var1)) (= (node var14 var13 var12 var11) var6)) (= (read var2 var15) var5)) (valid var2 var15)) (= (alloc var10 var3) var1)))) (_Glue27 var0 var15 var2 var5))))
(assert (forall ((var0 Int) (var1 AllocResHeap) (var2 HeapObject) (var3 node) (var4 HeapObject) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Heap) (var9 Addr) (var10 Heap)) (or (not (and (and (inv_main586_5 var10 var9) (inv_main586_5 var8 var7)) (and (and (and (and (and (= (read var6 var5) var4) (not (valid var6 var5))) (= (O_node var3) var2)) (= (AllocResHeap var6 var5) var1)) (= (alloc var10 var2) var1)) true))) (_Glue27 var0 var5 var6 var4))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 node) (var4 Addr) (var5 Heap) (var6 HeapObject) (var7 Heap) (var8 Addr) (var9 Int)) (or (not (and (and (_Glue27 var9 var8 var7 var6) (inv_main586_5 var5 var4)) (and (and (and (and (and (and (= (getnode var6) var3) (= (|node::right| var3) var2)) (= (|node::parent| var3) var1)) (= (|node::value| var3) var0)) (= nullAddr var4)) (not (= var8 var4))) (valid var7 var8)))) (Inv_Heap_exp_exp var8 var4 var2 var1 var0))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 node) (var3 Int) (var4 Addr) (var5 Addr) (var6 node) (var7 Addr) (var8 Heap) (var9 HeapObject) (var10 Heap) (var11 Addr) (var12 Int)) (or (not (and (and (_Glue27 var12 var11 var10 var9) (inv_main586_5 var8 var7)) (and (and (and (and (and (and (and (and (= (getnode var9) var6) (= (|node::right| var6) var5)) (= (|node::parent| var6) var4)) (= (|node::value| var6) var3)) (= nullAddr var7)) (not (= var11 var7))) (= (node var7 var5 var4 var3) var2)) (= (O_node var2) var1)) (= (write var10 var11 var1) var0)))) (_Glue28 var11 var12 var7 var0))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Heap) (var3 Addr) (var4 Int) (var5 Int) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr)) (or (not (and (and (Inv_Heap_exp_exp var9 var8 var7 var6 var5) (_Glue28 var9 var4 var3 var2)) (and (and (and (= (O_node var1) var0) (= (node var8 var7 var6 var5) var1)) (= (read var2 var9) var0)) (valid var2 var9)))) (_Glue29 var2 var3 var4 var9 var0))))
(assert (forall ((var0 HeapObject) (var1 Heap) (var2 Addr) (var3 Int) (var4 Addr)) (or (not (and (_Glue28 var4 var3 var2 var1) (and (= (read var1 var4) var0) (not (valid var1 var4))))) (_Glue29 var1 var2 var3 var4 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 node) (var4 HeapObject) (var5 Addr) (var6 Int) (var7 Addr) (var8 Heap)) (or (not (and (_Glue29 var8 var7 var6 var5 var4) (and (and (and (and (= (getnode var4) var3) (= (|node::left| var3) var2)) (= (|node::parent| var3) var1)) (= (|node::value| var3) var0)) (valid var8 var5)))) (Inv_Heap_exp_exp var5 var2 var7 var1 var0))))
(assert (forall ((var0 node) (var1 Heap) (var2 HeapObject) (var3 node) (var4 Int) (var5 Addr) (var6 Addr) (var7 HeapObject) (var8 node) (var9 HeapObject) (var10 Int) (var11 Addr) (var12 Heap) (var13 Int) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr)) (or (not (and (and (Inv_Heap_exp_exp var17 var16 var15 var14 var13) (_Glue29 var12 var11 var10 var17 var9)) (and (and (and (and (and (and (and (and (and (and (= (O_node var8) var7) (= (node var6 var11 var5 var4) var3)) (= (O_node var3) var2)) (= (node var16 var15 var14 var13) var8)) (= (read var1 var17) var7)) (valid var1 var17)) (= (getnode var9) var0)) (= (|node::left| var0) var6)) (= (|node::parent| var0) var5)) (= (|node::value| var0) var4)) (= (write var12 var17 var2) var1)))) (_Glue31 var1 var10 var17 var7))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Int) (var3 Addr) (var4 Addr) (var5 node) (var6 HeapObject) (var7 Heap) (var8 HeapObject) (var9 Addr) (var10 Int) (var11 Addr) (var12 Heap)) (or (not (and (_Glue29 var12 var11 var10 var9 var8) (and (and (and (and (and (and (and (and (= (read var7 var9) var6) (not (valid var7 var9))) (= (getnode var8) var5)) (= (|node::left| var5) var4)) (= (|node::parent| var5) var3)) (= (|node::value| var5) var2)) (= (node var4 var11 var3 var2) var1)) (= (O_node var1) var0)) (= (write var12 var9 var0) var7)))) (_Glue31 var7 var10 var9 var6))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 node) (var4 HeapObject) (var5 Addr) (var6 Int) (var7 Heap)) (or (not (and (_Glue31 var7 var6 var5 var4) (and (and (and (and (= (getnode var4) var3) (= (|node::left| var3) var2)) (= (|node::right| var3) var1)) (= (|node::parent| var3) var0)) (valid var7 var5)))) (Inv_Heap_exp_exp var5 var2 var1 var0 var6))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 node) (var3 Addr) (var4 Addr) (var5 Addr) (var6 node) (var7 HeapObject) (var8 Addr) (var9 Int) (var10 Heap)) (or (not (and (_Glue31 var10 var9 var8 var7) (and (and (and (and (and (and (= (getnode var7) var6) (= (|node::left| var6) var5)) (= (|node::right| var6) var4)) (= (|node::parent| var6) var3)) (= (node var5 var4 var3 var9) var2)) (= (O_node var2) var1)) (= (write var10 var8 var1) var0)))) (inv_main586_5 var0 var8))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (and (inv_main586_5 var2 var1) (and (= nullAddr var1) (= var0 var1)))) (inv_main_10 var2 var1 var0))))
(assert (forall ((var0 AllocResHeap) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 HeapObject) (var6 node) (var7 Addr) (var8 Heap)) (or (not (and (inv_main586_5 var8 var7) (and (and (= (O_node var6) var5) (= (node var4 var3 var2 var1) var6)) (= (alloc var8 var5) var0)))) (Inv_Heap_exp_exp (newAddr var0) var4 var3 var2 var1))))
(assert (forall ((var0 Int) (var1 AllocResHeap) (var2 Heap) (var3 HeapObject) (var4 node) (var5 HeapObject) (var6 node) (var7 Addr) (var8 Heap) (var9 Int) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr)) (or (not (and (and (Inv_Heap_exp_exp var13 var12 var11 var10 var9) (inv_main586_5 var8 var7)) (and (and (and (and (and (and (= (O_node var6) var5) (= (O_node var4) var3)) (= (AllocResHeap var2 var13) var1)) (= (node var12 var11 var10 var9) var6)) (= (read var2 var13) var5)) (valid var2 var13)) (= (alloc var8 var3) var1)))) (_Glue19 var7 var0 var13 var2 var5))))
(assert (forall ((var0 Int) (var1 AllocResHeap) (var2 HeapObject) (var3 node) (var4 HeapObject) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Heap)) (or (not (and (inv_main586_5 var8 var7) (and (and (and (and (= (read var6 var5) var4) (not (valid var6 var5))) (= (O_node var3) var2)) (= (AllocResHeap var6 var5) var1)) (= (alloc var8 var2) var1)))) (_Glue19 var7 var0 var5 var6 var4))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 node) (var5 HeapObject) (var6 Heap) (var7 Addr) (var8 Int) (var9 Addr)) (or (not (and (_Glue19 var9 var8 var7 var6 var5) (and (and (and (and (and (and (and (= (getnode var5) var4) (= (|node::right| var4) var3)) (= (|node::parent| var4) var2)) (= (|node::value| var4) var1)) (= nullAddr var0)) (not (= var9 var0))) (not (= var7 var0))) (valid var6 var7)))) (Inv_Heap_exp_exp var7 var0 var3 var2 var1))))
(assert (forall ((var0 node) (var1 Heap) (var2 HeapObject) (var3 node) (var4 Int) (var5 Addr) (var6 Addr) (var7 Addr) (var8 HeapObject) (var9 node) (var10 HeapObject) (var11 Heap) (var12 Int) (var13 Addr) (var14 Int) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr)) (or (not (and (and (Inv_Heap_exp_exp var18 var17 var16 var15 var14) (_Glue19 var13 var12 var18 var11 var10)) (and (and (and (and (and (and (and (and (and (and (and (and (and (= (O_node var9) var8) (= (node var7 var6 var5 var4) var3)) (= (O_node var3) var2)) (= (node var17 var16 var15 var14) var9)) (= (read var1 var18) var8)) (valid var1 var18)) (= (getnode var10) var0)) (= (|node::right| var0) var6)) (= (|node::parent| var0) var5)) (= (|node::value| var0) var4)) (= nullAddr var7)) (not (= var13 var7))) (not (= var18 var7))) (= (write var11 var18 var2) var1)))) (_Glue21 var1 var13 var12 var18 var8))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Int) (var4 Addr) (var5 Addr) (var6 node) (var7 HeapObject) (var8 Heap) (var9 HeapObject) (var10 Heap) (var11 Addr) (var12 Int) (var13 Addr)) (or (not (and (_Glue19 var13 var12 var11 var10 var9) (and (and (and (and (and (and (and (and (and (and (and (= (read var8 var11) var7) (not (valid var8 var11))) (= (getnode var9) var6)) (= (|node::right| var6) var5)) (= (|node::parent| var6) var4)) (= (|node::value| var6) var3)) (= nullAddr var2)) (not (= var13 var2))) (not (= var11 var2))) (= (node var2 var5 var4 var3) var1)) (= (O_node var1) var0)) (= (write var10 var11 var0) var8)))) (_Glue21 var8 var13 var12 var11 var7))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 node) (var4 HeapObject) (var5 Addr) (var6 Int) (var7 Addr) (var8 Heap)) (or (not (and (_Glue21 var8 var7 var6 var5 var4) (and (and (and (and (= (getnode var4) var3) (= (|node::left| var3) var2)) (= (|node::parent| var3) var1)) (= (|node::value| var3) var0)) (valid var8 var5)))) (Inv_Heap_exp_exp var5 var2 var7 var1 var0))))
(assert (forall ((var0 node) (var1 Heap) (var2 HeapObject) (var3 node) (var4 Int) (var5 Addr) (var6 Addr) (var7 HeapObject) (var8 node) (var9 HeapObject) (var10 Addr) (var11 Int) (var12 Heap) (var13 Int) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr)) (or (not (and (and (Inv_Heap_exp_exp var17 var16 var15 var14 var13) (_Glue21 var12 var17 var11 var10 var9)) (and (and (and (and (and (and (and (and (and (and (= (O_node var8) var7) (= (node var6 var17 var5 var4) var3)) (= (O_node var3) var2)) (= (node var16 var15 var14 var13) var8)) (= (read var1 var17) var7)) (valid var1 var17)) (= (getnode var9) var0)) (= (|node::left| var0) var6)) (= (|node::parent| var0) var5)) (= (|node::value| var0) var4)) (= (write var12 var10 var2) var1)))) (_Glue23 var1 var17 var11 var10 var7))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Int) (var3 Addr) (var4 Addr) (var5 node) (var6 HeapObject) (var7 Heap) (var8 HeapObject) (var9 Addr) (var10 Int) (var11 Addr) (var12 Heap)) (or (not (and (_Glue21 var12 var11 var10 var9 var8) (and (and (and (and (and (and (and (and (= (read var7 var11) var6) (not (valid var7 var11))) (= (getnode var8) var5)) (= (|node::left| var5) var4)) (= (|node::parent| var5) var3)) (= (|node::value| var5) var2)) (= (node var4 var11 var3 var2) var1)) (= (O_node var1) var0)) (= (write var12 var9 var0) var7)))) (_Glue23 var7 var11 var10 var9 var6))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 node) (var4 HeapObject) (var5 Addr) (var6 Int) (var7 Addr) (var8 Heap)) (or (not (and (_Glue23 var8 var7 var6 var5 var4) (and (and (and (and (= (getnode var4) var3) (= (|node::left| var3) var2)) (= (|node::right| var3) var1)) (= (|node::value| var3) var0)) (valid var8 var7)))) (Inv_Heap_exp_exp var7 var2 var1 var5 var0))))
(assert (forall ((var0 node) (var1 Heap) (var2 HeapObject) (var3 node) (var4 Int) (var5 Addr) (var6 Addr) (var7 HeapObject) (var8 node) (var9 HeapObject) (var10 Int) (var11 Addr) (var12 Heap) (var13 Int) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr)) (or (not (and (and (Inv_Heap_exp_exp var17 var16 var15 var14 var13) (_Glue23 var12 var11 var10 var17 var9)) (and (and (and (and (and (and (and (and (and (and (= (O_node var8) var7) (= (node var6 var5 var17 var4) var3)) (= (O_node var3) var2)) (= (node var16 var15 var14 var13) var8)) (= (read var1 var17) var7)) (valid var1 var17)) (= (getnode var9) var0)) (= (|node::left| var0) var6)) (= (|node::right| var0) var5)) (= (|node::value| var0) var4)) (= (write var12 var11 var2) var1)))) (_Glue25 var1 var10 var17 var7))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Int) (var3 Addr) (var4 Addr) (var5 node) (var6 HeapObject) (var7 Heap) (var8 HeapObject) (var9 Addr) (var10 Int) (var11 Addr) (var12 Heap)) (or (not (and (_Glue23 var12 var11 var10 var9 var8) (and (and (and (and (and (and (and (and (= (read var7 var9) var6) (not (valid var7 var9))) (= (getnode var8) var5)) (= (|node::left| var5) var4)) (= (|node::right| var5) var3)) (= (|node::value| var5) var2)) (= (node var4 var3 var9 var2) var1)) (= (O_node var1) var0)) (= (write var12 var11 var0) var7)))) (_Glue25 var7 var10 var9 var6))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 node) (var4 HeapObject) (var5 Addr) (var6 Int) (var7 Heap)) (or (not (and (_Glue25 var7 var6 var5 var4) (and (and (and (and (= (getnode var4) var3) (= (|node::left| var3) var2)) (= (|node::right| var3) var1)) (= (|node::parent| var3) var0)) (valid var7 var5)))) (Inv_Heap_exp_exp var5 var2 var1 var0 var6))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 node) (var3 Addr) (var4 Addr) (var5 Addr) (var6 node) (var7 HeapObject) (var8 Addr) (var9 Int) (var10 Heap)) (or (not (and (_Glue25 var10 var9 var8 var7) (and (and (and (and (and (and (= (getnode var7) var6) (= (|node::left| var6) var5)) (= (|node::right| var6) var4)) (= (|node::parent| var6) var3)) (= (node var5 var4 var3 var9) var2)) (= (O_node var2) var1)) (= (write var10 var8 var1) var0)))) (inv_main586_5 var0 var8))))
(check-sat)
