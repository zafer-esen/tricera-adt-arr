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
   (node (|node::expected_list| Int) (|node::value| Int) (|node::next| Addr))
  )
))
(declare-fun _Glue5 (Heap Addr HeapObject) Bool)
(declare-fun inv_main_19 (Heap Addr) Bool)
(declare-fun _Glue1 (Addr Int Addr Heap HeapObject) Bool)
(declare-fun inv_main581_5 (Heap Addr) Bool)
(declare-fun Inv_Heap_exp_exp (Addr Int Int Addr) Bool)
(declare-fun _Glue6 (Heap Addr Addr HeapObject) Bool)
(declare-fun _Glue8 (Addr Int Addr Heap HeapObject) Bool)
(declare-fun inv_main_14 (Heap Addr Addr) Bool)
(declare-fun _Glue10 (Heap Int Addr HeapObject) Bool)
(declare-fun _Glue3 (Heap Int Addr HeapObject) Bool)
(declare-fun inv_main595_5 (Heap Addr Addr) Bool)
(declare-fun _Glue12 (Heap Addr HeapObject) Bool)
(declare-fun _Glue13 (Heap Addr Addr HeapObject) Bool)
(assert (forall ((var0 Addr) (var1 HeapObject) (var2 node) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Int) (var7 Int) (var8 Addr)) (or (not (and (and (Inv_Heap_exp_exp var8 var7 var6 var5) (inv_main_14 var4 var8 var3)) (and (and (and (and (and (and (= (O_node var2) var1) (= (node var7 var6 var5) var2)) (= (read var4 var8) var1)) (= nullAddr var0)) (not (= var8 var0))) (not (= var7 (- 1)))) (valid var4 var8)))) (inv_main_14 var4 var5 var3))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 node) (var4 HeapObject) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main_14 var7 var6 var5) (and (and (and (and (and (and (and (= (read var7 var6) var4) (= (getnode var4) var3)) (= (|node::next| var3) var2)) (= nullAddr var1)) (= (|node::expected_list| var3) var0)) (not (= var6 var1))) (not (= var0 (- 1)))) (not (valid var7 var6))))) (inv_main_14 var7 var2 var5))))
(assert (forall ((var0 Addr) (var1 HeapObject) (var2 node) (var3 Heap) (var4 Addr) (var5 Int) (var6 Int) (var7 Addr)) (or (not (and (and (Inv_Heap_exp_exp var7 var6 var5 var4) (inv_main_19 var3 var7)) (and (and (and (and (and (and (= (O_node var2) var1) (= (node var6 var5 var4) var2)) (= (read var3 var7) var1)) (= nullAddr var0)) (not (= var7 var0))) (not (= var6 1))) (valid var3 var7)))) (inv_main_19 var3 var4))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 node) (var4 HeapObject) (var5 Addr) (var6 Heap)) (or (not (and (inv_main_19 var6 var5) (and (and (and (and (and (and (and (= (read var6 var5) var4) (= (getnode var4) var3)) (= (|node::next| var3) var2)) (= nullAddr var1)) (= (|node::expected_list| var3) var0)) (not (= var5 var1))) (not (= var0 1))) (not (valid var6 var5))))) (inv_main_19 var6 var2))))
(assert (forall ((var0 Addr) (var1 HeapObject) (var2 node) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Int) (var7 Int) (var8 Addr)) (not (and (and (Inv_Heap_exp_exp var8 var7 var6 var5) (inv_main_14 var4 var8 var3)) (and (and (and (and (and (and (= (O_node var2) var1) (= (node var7 var6 var5) var2)) (not (= var8 var0))) (not (= var7 (- 1)))) (= nullAddr var0)) (= (read var4 var8) var1)) (valid var4 var8))))))
(assert (forall ((var0 node) (var1 HeapObject) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap)) (not (and (inv_main_14 var6 var5 var4) (and (and (and (and (and (and (not (= var5 var3)) (not (= var2 (- 1)))) (= nullAddr var3)) (= (read var6 var5) var1)) (= (getnode var1) var0)) (= (|node::expected_list| var0) var2)) (not (valid var6 var5)))))))
(assert (forall ((var0 Addr) (var1 HeapObject) (var2 node) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Int) (var7 Int) (var8 Addr)) (or (not (and (and (Inv_Heap_exp_exp var8 var7 var6 var5) (inv_main595_5 var4 var3 var8)) (and (and (and (and (and (= (O_node var2) var1) (= (node var7 var6 var5) var2)) (= nullAddr var0)) (not (= var8 var0))) (= (read var4 var8) var1)) (valid var4 var8)))) (_Glue6 var4 var3 var8 var1))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main595_5 var4 var3 var2) (and (and (and (= nullAddr var1) (not (= var2 var1))) (= (read var4 var2) var0)) (not (valid var4 var2))))) (_Glue6 var4 var3 var2 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 node) (var3 HeapObject) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (_Glue6 var6 var5 var4 var3) (and (and (and (and (= (getnode var3) var2) (= (|node::value| var2) var1)) (<= 0 var1)) (= (|node::expected_list| var2) var0)) (valid var6 var4)))) (Inv_Heap_exp_exp var4 var0 var1 var5))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 node) (var3 Int) (var4 Int) (var5 Addr) (var6 node) (var7 HeapObject) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (_Glue6 var10 var9 var8 var7) (and (and (and (and (and (and (and (= (getnode var7) var6) (= (|node::next| var6) var5)) (= (|node::value| var6) var4)) (<= 0 var4)) (= (|node::expected_list| var6) var3)) (= (node var3 var4 var9) var2)) (= (O_node var2) var1)) (= (write var10 var8 var1) var0)))) (inv_main595_5 var0 var9 var5))))
(assert (forall ((var0 Addr) (var1 HeapObject) (var2 node) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Int) (var7 Addr)) (or (not (and (and (Inv_Heap_exp_exp var7 (- 1) var6 var5) (inv_main_14 var4 var7 var3)) (and (and (and (and (and (= (O_node var2) var1) (= (node (- 1) var6 var5) var2)) (= nullAddr var0)) (= (read var4 var7) var1)) (not (= var7 var0))) (valid var4 var7)))) (inv_main_14 var4 var5 var3))))
(assert (forall ((var0 Addr) (var1 node) (var2 HeapObject) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main_14 var6 var5 var4) (and (and (and (and (and (and (= nullAddr var3) (= (read var6 var5) var2)) (= (getnode var2) var1)) (= (|node::expected_list| var1) (- 1))) (= (|node::next| var1) var0)) (not (= var5 var3))) (not (valid var6 var5))))) (inv_main_14 var6 var0 var4))))
(assert (forall ((var0 AllocResHeap) (var1 Addr) (var2 Int) (var3 Int) (var4 HeapObject) (var5 node) (var6 Addr) (var7 Heap)) (or (not (and (inv_main581_5 var7 var6) (and (and (= (O_node var5) var4) (= (node var3 var2 var1) var5)) (= (alloc var7 var4) var0)))) (Inv_Heap_exp_exp (newAddr var0) var3 var2 var1))))
(assert (forall ((var0 Int) (var1 AllocResHeap) (var2 Heap) (var3 HeapObject) (var4 node) (var5 HeapObject) (var6 node) (var7 Addr) (var8 Heap) (var9 Addr) (var10 Int) (var11 Int) (var12 Addr)) (or (not (and (and (Inv_Heap_exp_exp var12 var11 var10 var9) (inv_main581_5 var8 var7)) (and (and (and (and (and (and (and (= (O_node var6) var5) (= (O_node var4) var3)) (= (AllocResHeap var2 var12) var1)) (= (node var11 var10 var9) var6)) (= (read var2 var12) var5)) (valid var2 var12)) (<= 0 (+ (- 1) (* (- 1) var0)))) (= (alloc var8 var3) var1)))) (_Glue8 var7 var0 var12 var2 var5))))
(assert (forall ((var0 Int) (var1 AllocResHeap) (var2 HeapObject) (var3 node) (var4 HeapObject) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Heap)) (or (not (and (inv_main581_5 var8 var7) (and (and (and (and (and (= (read var6 var5) var4) (not (valid var6 var5))) (= (O_node var3) var2)) (= (AllocResHeap var6 var5) var1)) (<= 0 (+ (- 1) (* (- 1) var0)))) (= (alloc var8 var2) var1)))) (_Glue8 var7 var0 var5 var6 var4))))
(assert (forall ((var0 Int) (var1 Int) (var2 node) (var3 HeapObject) (var4 Heap) (var5 Addr) (var6 Int) (var7 Addr)) (or (not (and (_Glue8 var7 var6 var5 var4 var3) (and (and (and (= (getnode var3) var2) (= (|node::expected_list| var2) var1)) (= (|node::value| var2) var0)) (valid var4 var5)))) (Inv_Heap_exp_exp var5 var1 var0 var7))))
(assert (forall ((var0 node) (var1 Heap) (var2 HeapObject) (var3 node) (var4 Int) (var5 Int) (var6 HeapObject) (var7 node) (var8 HeapObject) (var9 Heap) (var10 Int) (var11 Addr) (var12 Addr) (var13 Int) (var14 Int) (var15 Addr)) (or (not (and (and (Inv_Heap_exp_exp var15 var14 var13 var12) (_Glue8 var11 var10 var15 var9 var8)) (and (and (and (and (and (and (and (and (and (= (O_node var7) var6) (= (node var5 var4 var11) var3)) (= (O_node var3) var2)) (= (node var14 var13 var12) var7)) (= (read var1 var15) var6)) (valid var1 var15)) (= (getnode var8) var0)) (= (|node::expected_list| var0) var5)) (= (|node::value| var0) var4)) (= (write var9 var15 var2) var1)))) (_Glue10 var1 var10 var15 var6))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Int) (var3 Int) (var4 node) (var5 HeapObject) (var6 Heap) (var7 HeapObject) (var8 Heap) (var9 Addr) (var10 Int) (var11 Addr)) (or (not (and (_Glue8 var11 var10 var9 var8 var7) (and (and (and (and (and (and (and (= (read var6 var9) var5) (not (valid var6 var9))) (= (getnode var7) var4)) (= (|node::expected_list| var4) var3)) (= (|node::value| var4) var2)) (= (node var3 var2 var11) var1)) (= (O_node var1) var0)) (= (write var8 var9 var0) var6)))) (_Glue10 var6 var10 var9 var5))))
(assert (forall ((var0 Addr) (var1 Int) (var2 node) (var3 HeapObject) (var4 Addr) (var5 Int) (var6 Heap)) (or (not (and (_Glue10 var6 var5 var4 var3) (and (and (and (= (getnode var3) var2) (= (|node::expected_list| var2) var1)) (= (|node::next| var2) var0)) (valid var6 var4)))) (Inv_Heap_exp_exp var4 var1 var5 var0))))
(assert (forall ((var0 node) (var1 Heap) (var2 HeapObject) (var3 node) (var4 Addr) (var5 Int) (var6 HeapObject) (var7 node) (var8 HeapObject) (var9 Int) (var10 Heap) (var11 Addr) (var12 Int) (var13 Int) (var14 Addr)) (or (not (and (and (Inv_Heap_exp_exp var14 var13 var12 var11) (_Glue10 var10 var9 var14 var8)) (and (and (and (and (and (and (and (and (and (= (O_node var7) var6) (= (node var5 var9 var4) var3)) (= (O_node var3) var2)) (= (node var13 var12 var11) var7)) (= (read var1 var14) var6)) (valid var1 var14)) (= (getnode var8) var0)) (= (|node::expected_list| var0) var5)) (= (|node::next| var0) var4)) (= (write var10 var14 var2) var1)))) (_Glue12 var1 var14 var6))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Int) (var4 node) (var5 HeapObject) (var6 Heap) (var7 HeapObject) (var8 Addr) (var9 Int) (var10 Heap)) (or (not (and (_Glue10 var10 var9 var8 var7) (and (and (and (and (and (and (and (= (read var6 var8) var5) (not (valid var6 var8))) (= (getnode var7) var4)) (= (|node::expected_list| var4) var3)) (= (|node::next| var4) var2)) (= (node var3 var9 var2) var1)) (= (O_node var1) var0)) (= (write var10 var8 var0) var6)))) (_Glue12 var6 var8 var5))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 node) (var4 HeapObject) (var5 Addr) (var6 Heap)) (or (not (and (_Glue12 var6 var5 var4) (and (and (and (and (= (getnode var4) var3) (= (|node::value| var3) var2)) (= (|node::next| var3) var1)) (valid var6 var5)) (= var0 (- 1))))) (Inv_Heap_exp_exp var5 var0 var2 var1))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 node) (var3 Addr) (var4 Int) (var5 node) (var6 HeapObject) (var7 Addr) (var8 Heap)) (or (not (and (_Glue12 var8 var7 var6) (and (and (and (and (and (= (getnode var6) var5) (= (|node::value| var5) var4)) (= (|node::next| var5) var3)) (= (node (- 1) var4 var3) var2)) (= (O_node var2) var1)) (= (write var8 var7 var1) var0)))) (inv_main581_5 var0 var7))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (and (inv_main581_5 var2 var1) (= nullAddr var0))) (inv_main595_5 var2 var0 var1))))
(assert (forall ((var0 Addr) (var1 HeapObject) (var2 node) (var3 Heap) (var4 Addr) (var5 Int) (var6 Int) (var7 Addr)) (not (and (and (Inv_Heap_exp_exp var7 var6 var5 var4) (inv_main_19 var3 var7)) (and (and (and (and (and (and (= (O_node var2) var1) (= (node var6 var5 var4) var2)) (not (= var7 var0))) (not (= var6 1))) (= nullAddr var0)) (= (read var3 var7) var1)) (valid var3 var7))))))
(assert (forall ((var0 node) (var1 HeapObject) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap)) (not (and (inv_main_19 var5 var4) (and (and (and (and (and (and (not (= var4 var3)) (not (= var2 1))) (= nullAddr var3)) (= (read var5 var4) var1)) (= (getnode var1) var0)) (= (|node::expected_list| var0) var2)) (not (valid var5 var4)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (and (inv_main_14 var2 var1 var0) (= nullAddr var1))) (inv_main_19 var2 var0))))
(assert (forall ((var0 AllocResHeap) (var1 Int) (var2 Addr) (var3 Int) (var4 Int) (var5 HeapObject) (var6 node) (var7 Addr) (var8 Heap)) (or (not (and (inv_main581_5 var8 var7) (and (and (and (= (O_node var6) var5) (= (node var4 var3 var2) var6)) (not (<= 0 (+ (- 1) (* (- 1) var1))))) (= (alloc var8 var5) var0)))) (Inv_Heap_exp_exp (newAddr var0) var4 var3 var2))))
(assert (forall ((var0 Int) (var1 AllocResHeap) (var2 Heap) (var3 HeapObject) (var4 node) (var5 HeapObject) (var6 node) (var7 Addr) (var8 Heap) (var9 Addr) (var10 Int) (var11 Int) (var12 Addr)) (or (not (and (and (Inv_Heap_exp_exp var12 var11 var10 var9) (inv_main581_5 var8 var7)) (and (and (and (and (and (and (and (= (O_node var6) var5) (= (O_node var4) var3)) (= (AllocResHeap var2 var12) var1)) (= (node var11 var10 var9) var6)) (= (read var2 var12) var5)) (valid var2 var12)) (not (<= 0 (+ (- 1) (* (- 1) var0))))) (= (alloc var8 var3) var1)))) (_Glue1 var7 var0 var12 var2 var5))))
(assert (forall ((var0 Int) (var1 AllocResHeap) (var2 HeapObject) (var3 node) (var4 HeapObject) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Heap)) (or (not (and (inv_main581_5 var8 var7) (and (and (and (and (and (= (read var6 var5) var4) (not (valid var6 var5))) (= (O_node var3) var2)) (= (AllocResHeap var6 var5) var1)) (not (<= 0 (+ (- 1) (* (- 1) var0))))) (= (alloc var8 var2) var1)))) (_Glue1 var7 var0 var5 var6 var4))))
(assert (forall ((var0 Int) (var1 Int) (var2 node) (var3 HeapObject) (var4 Heap) (var5 Addr) (var6 Int) (var7 Addr)) (or (not (and (_Glue1 var7 var6 var5 var4 var3) (and (and (and (= (getnode var3) var2) (= (|node::expected_list| var2) var1)) (= (|node::value| var2) var0)) (valid var4 var5)))) (Inv_Heap_exp_exp var5 var1 var0 var7))))
(assert (forall ((var0 node) (var1 Heap) (var2 HeapObject) (var3 node) (var4 Int) (var5 Int) (var6 HeapObject) (var7 node) (var8 HeapObject) (var9 Heap) (var10 Int) (var11 Addr) (var12 Addr) (var13 Int) (var14 Int) (var15 Addr)) (or (not (and (and (Inv_Heap_exp_exp var15 var14 var13 var12) (_Glue1 var11 var10 var15 var9 var8)) (and (and (and (and (and (and (and (and (and (= (O_node var7) var6) (= (node var5 var4 var11) var3)) (= (O_node var3) var2)) (= (node var14 var13 var12) var7)) (= (read var1 var15) var6)) (valid var1 var15)) (= (getnode var8) var0)) (= (|node::expected_list| var0) var5)) (= (|node::value| var0) var4)) (= (write var9 var15 var2) var1)))) (_Glue3 var1 var10 var15 var6))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Int) (var3 Int) (var4 node) (var5 HeapObject) (var6 Heap) (var7 HeapObject) (var8 Heap) (var9 Addr) (var10 Int) (var11 Addr)) (or (not (and (_Glue1 var11 var10 var9 var8 var7) (and (and (and (and (and (and (and (= (read var6 var9) var5) (not (valid var6 var9))) (= (getnode var7) var4)) (= (|node::expected_list| var4) var3)) (= (|node::value| var4) var2)) (= (node var3 var2 var11) var1)) (= (O_node var1) var0)) (= (write var8 var9 var0) var6)))) (_Glue3 var6 var10 var9 var5))))
(assert (forall ((var0 Addr) (var1 Int) (var2 node) (var3 HeapObject) (var4 Addr) (var5 Int) (var6 Heap)) (or (not (and (_Glue3 var6 var5 var4 var3) (and (and (and (= (getnode var3) var2) (= (|node::expected_list| var2) var1)) (= (|node::next| var2) var0)) (valid var6 var4)))) (Inv_Heap_exp_exp var4 var1 var5 var0))))
(assert (forall ((var0 node) (var1 Heap) (var2 HeapObject) (var3 node) (var4 Addr) (var5 Int) (var6 HeapObject) (var7 node) (var8 HeapObject) (var9 Int) (var10 Heap) (var11 Addr) (var12 Int) (var13 Int) (var14 Addr)) (or (not (and (and (Inv_Heap_exp_exp var14 var13 var12 var11) (_Glue3 var10 var9 var14 var8)) (and (and (and (and (and (and (and (and (and (= (O_node var7) var6) (= (node var5 var9 var4) var3)) (= (O_node var3) var2)) (= (node var13 var12 var11) var7)) (= (read var1 var14) var6)) (valid var1 var14)) (= (getnode var8) var0)) (= (|node::expected_list| var0) var5)) (= (|node::next| var0) var4)) (= (write var10 var14 var2) var1)))) (_Glue5 var1 var14 var6))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Int) (var4 node) (var5 HeapObject) (var6 Heap) (var7 HeapObject) (var8 Addr) (var9 Int) (var10 Heap)) (or (not (and (_Glue3 var10 var9 var8 var7) (and (and (and (and (and (and (and (= (read var6 var8) var5) (not (valid var6 var8))) (= (getnode var7) var4)) (= (|node::expected_list| var4) var3)) (= (|node::next| var4) var2)) (= (node var3 var9 var2) var1)) (= (O_node var1) var0)) (= (write var10 var8 var0) var6)))) (_Glue5 var6 var8 var5))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 node) (var4 HeapObject) (var5 Addr) (var6 Heap)) (or (not (and (_Glue5 var6 var5 var4) (and (and (and (and (= (getnode var4) var3) (= (|node::value| var3) var2)) (= (|node::next| var3) var1)) (valid var6 var5)) (= var0 1)))) (Inv_Heap_exp_exp var5 var0 var2 var1))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 node) (var3 Addr) (var4 Int) (var5 node) (var6 HeapObject) (var7 Addr) (var8 Heap)) (or (not (and (_Glue5 var8 var7 var6) (and (and (and (and (and (= (getnode var6) var5) (= (|node::value| var5) var4)) (= (|node::next| var5) var3)) (= (node 1 var4 var3) var2)) (= (O_node var2) var1)) (= (write var8 var7 var1) var0)))) (inv_main581_5 var0 var7))))
(assert (forall ((var0 Addr) (var1 HeapObject) (var2 node) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Int) (var7 Int) (var8 Addr)) (or (not (and (and (Inv_Heap_exp_exp var8 var7 var6 var5) (inv_main595_5 var4 var3 var8)) (and (and (and (and (and (= (O_node var2) var1) (= (node var7 var6 var5) var2)) (= nullAddr var0)) (not (= var8 var0))) (= (read var4 var8) var1)) (valid var4 var8)))) (_Glue13 var4 var3 var8 var1))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main595_5 var4 var3 var2) (and (and (and (= nullAddr var1) (not (= var2 var1))) (= (read var4 var2) var0)) (not (valid var4 var2))))) (_Glue13 var4 var3 var2 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 node) (var3 HeapObject) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (_Glue13 var6 var5 var4 var3) (and (and (and (and (= (getnode var3) var2) (= (|node::value| var2) var1)) (not (<= 0 var1))) (= (|node::expected_list| var2) var0)) (valid var6 var4)))) (Inv_Heap_exp_exp var4 var0 var1 var5))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 node) (var3 Int) (var4 Int) (var5 Addr) (var6 node) (var7 HeapObject) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (_Glue13 var10 var9 var8 var7) (and (and (and (and (and (and (and (= (getnode var7) var6) (= (|node::next| var6) var5)) (= (|node::value| var6) var4)) (not (<= 0 var4))) (= (|node::expected_list| var6) var3)) (= (node var3 var4 var9) var2)) (= (O_node var2) var1)) (= (write var10 var8 var1) var0)))) (inv_main595_5 var0 var9 var5))))
(assert (forall ((var0 Addr) (var1 HeapObject) (var2 node) (var3 Heap) (var4 Addr) (var5 Int) (var6 Addr)) (or (not (and (and (Inv_Heap_exp_exp var6 1 var5 var4) (inv_main_19 var3 var6)) (and (and (and (and (and (= (O_node var2) var1) (= (node 1 var5 var4) var2)) (= nullAddr var0)) (= (read var3 var6) var1)) (not (= var6 var0))) (valid var3 var6)))) (inv_main_19 var3 var4))))
(assert (forall ((var0 Addr) (var1 node) (var2 HeapObject) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main_19 var5 var4) (and (and (and (and (and (and (= nullAddr var3) (= (read var5 var4) var2)) (= (getnode var2) var1)) (= (|node::expected_list| var1) 1)) (= (|node::next| var1) var0)) (not (= var4 var3))) (not (valid var5 var4))))) (inv_main_19 var5 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main595_5 var3 var2 var1) (and (= nullAddr var1) (= var0 var2)))) (inv_main_14 var3 var2 var0))))
(assert (forall ((var0 Heap) (var1 Addr)) (or (not (and (= nullAddr var1) (= emptyHeap var0))) (inv_main581_5 var0 var1))))
(check-sat)
