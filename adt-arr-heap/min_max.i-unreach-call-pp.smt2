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
   (node (|node::next| Addr) (|node::val| Int))
  )
))
(declare-fun _Glue13 (Heap Addr Int Int Int Addr HeapObject) Bool)
(declare-fun _Glue3 (Heap Addr Int Int Addr HeapObject) Bool)
(declare-fun _Glue18 (Heap Addr Int Int Addr HeapObject) Bool)
(declare-fun _Glue8 (Heap Addr Int Int Addr HeapObject) Bool)
(declare-fun inv_main590_13_14 (Heap Int Int Addr) Bool)
(declare-fun _Glue1 (Addr Int Int Int Addr Heap HeapObject) Bool)
(declare-fun _Glue16 (Addr Int Int Int Addr Heap HeapObject) Bool)
(declare-fun inv_main586_5 (Heap Int Int Addr) Bool)
(declare-fun _Glue11 (Addr Int Int Int Int Addr Heap HeapObject) Bool)
(declare-fun Inv_Heap_exp_exp (Addr Addr Int) Bool)
(declare-fun inv_main574_5 (Heap Addr Int Int) Bool)
(declare-fun _Glue6 (Addr Int Int Int Addr Heap HeapObject) Bool)
(assert (forall ((var0 Addr) (var1 HeapObject) (var2 node) (var3 Int) (var4 Int) (var5 Heap) (var6 Int) (var7 Addr) (var8 Addr)) (or (not (and (and (Inv_Heap_exp_exp var8 var7 var6) (inv_main586_5 var5 var4 var3 var8)) (and (and (and (and (and (and (and (= (O_node var2) var1) (= (node var7 var6) var2)) (= (read var5 var8) var1)) (= nullAddr var0)) (<= 0 (+ (+ var6 (* (- 1) var3)) (- 1)))) (not (= var8 var0))) (<= 0 (+ (+ var4 (* (- 1) var6)) (- 1)))) (valid var5 var8)))) (inv_main590_13_14 var5 var4 var3 var8))))
(assert (forall ((var0 Addr) (var1 Int) (var2 node) (var3 HeapObject) (var4 Addr) (var5 Int) (var6 Int) (var7 Heap)) (or (not (and (inv_main586_5 var7 var6 var5 var4) (and (and (and (and (and (and (and (= (read var7 var4) var3) (= (getnode var3) var2)) (= (|node::val| var2) var1)) (= nullAddr var0)) (<= 0 (+ (+ var1 (* (- 1) var5)) (- 1)))) (not (= var4 var0))) (<= 0 (+ (+ var6 (* (- 1) var1)) (- 1)))) (not (valid var7 var4))))) (inv_main590_13_14 var7 var6 var5 var4))))
(assert (forall ((var0 AllocResHeap) (var1 Int) (var2 Addr) (var3 HeapObject) (var4 node) (var5 Int) (var6 Int) (var7 Addr) (var8 Heap)) (or (not (and (inv_main574_5 var8 var7 var6 var5) (and (and (= (O_node var4) var3) (= (node var2 var1) var4)) (= (alloc var8 var3) var0)))) (Inv_Heap_exp_exp (newAddr var0) var2 var1))))
(assert (forall ((var0 Int) (var1 AllocResHeap) (var2 Heap) (var3 HeapObject) (var4 node) (var5 HeapObject) (var6 node) (var7 Int) (var8 Int) (var9 Addr) (var10 Heap) (var11 Int) (var12 Addr) (var13 Addr)) (or (not (and (and (Inv_Heap_exp_exp var13 var12 var11) (inv_main574_5 var10 var9 var8 var7)) (and (and (and (and (and (and (= (O_node var6) var5) (= (O_node var4) var3)) (= (AllocResHeap var2 var13) var1)) (= (node var12 var11) var6)) (= (read var2 var13) var5)) (valid var2 var13)) (= (alloc var10 var3) var1)))) (_Glue1 var9 var8 var7 var0 var13 var2 var5))))
(assert (forall ((var0 Int) (var1 AllocResHeap) (var2 HeapObject) (var3 node) (var4 HeapObject) (var5 Addr) (var6 Heap) (var7 Int) (var8 Int) (var9 Addr) (var10 Heap)) (or (not (and (inv_main574_5 var10 var9 var8 var7) (and (and (and (and (= (read var6 var5) var4) (not (valid var6 var5))) (= (O_node var3) var2)) (= (AllocResHeap var6 var5) var1)) (= (alloc var10 var2) var1)))) (_Glue1 var9 var8 var7 var0 var5 var6 var4))))
(assert (forall ((var0 Addr) (var1 node) (var2 HeapObject) (var3 Heap) (var4 Addr) (var5 Int) (var6 Int) (var7 Int) (var8 Addr)) (or (not (and (_Glue1 var8 var7 var6 var5 var4 var3 var2) (and (and (= (getnode var2) var1) (= (|node::next| var1) var0)) (valid var3 var4)))) (Inv_Heap_exp_exp var4 var0 var5))))
(assert (forall ((var0 node) (var1 Heap) (var2 HeapObject) (var3 node) (var4 Addr) (var5 HeapObject) (var6 node) (var7 HeapObject) (var8 Heap) (var9 Int) (var10 Int) (var11 Int) (var12 Addr) (var13 Int) (var14 Addr) (var15 Addr)) (or (not (and (and (Inv_Heap_exp_exp var15 var14 var13) (_Glue1 var12 var11 var10 var9 var15 var8 var7)) (and (and (and (and (and (and (and (and (= (O_node var6) var5) (= (node var4 var9) var3)) (= (O_node var3) var2)) (= (node var14 var13) var6)) (= (read var1 var15) var5)) (valid var1 var15)) (= (getnode var7) var0)) (= (|node::next| var0) var4)) (= (write var8 var15 var2) var1)))) (_Glue3 var1 var12 var11 var10 var15 var5))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 node) (var4 HeapObject) (var5 Heap) (var6 HeapObject) (var7 Heap) (var8 Addr) (var9 Int) (var10 Int) (var11 Int) (var12 Addr)) (or (not (and (_Glue1 var12 var11 var10 var9 var8 var7 var6) (and (and (and (and (and (and (= (read var5 var8) var4) (not (valid var5 var8))) (= (getnode var6) var3)) (= (|node::next| var3) var2)) (= (node var2 var9) var1)) (= (O_node var1) var0)) (= (write var7 var8 var0) var5)))) (_Glue3 var5 var12 var11 var10 var8 var4))))
(assert (forall ((var0 Int) (var1 node) (var2 HeapObject) (var3 Addr) (var4 Int) (var5 Int) (var6 Addr) (var7 Heap)) (or (not (and (_Glue3 var7 var6 var5 var4 var3 var2) (and (and (= (getnode var2) var1) (= (|node::val| var1) var0)) (valid var7 var3)))) (Inv_Heap_exp_exp var3 var6 var0))))
(assert (forall ((var0 node) (var1 Heap) (var2 HeapObject) (var3 node) (var4 Int) (var5 HeapObject) (var6 node) (var7 HeapObject) (var8 Int) (var9 Int) (var10 Addr) (var11 Heap) (var12 Int) (var13 Addr) (var14 Addr)) (or (not (and (and (Inv_Heap_exp_exp var14 var13 var12) (_Glue3 var11 var10 var9 var8 var14 var7)) (and (and (and (and (and (and (and (and (and (and (= (O_node var6) var5) (= (node var10 var4) var3)) (= (O_node var3) var2)) (= (node var13 var12) var6)) (= (read var1 var14) var5)) (not (<= 0 (+ (+ var9 (* (- 1) var12)) (- 1))))) (not (<= 0 (+ (+ var12 (* (- 1) var8)) (- 1))))) (valid var1 var14)) (= (getnode var7) var0)) (= (|node::val| var0) var4)) (= (write var11 var14 var2) var1)))) (inv_main574_5 var1 var14 var9 var8))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Int) (var3 node) (var4 Int) (var5 node) (var6 HeapObject) (var7 Heap) (var8 HeapObject) (var9 Addr) (var10 Int) (var11 Int) (var12 Addr) (var13 Heap)) (or (not (and (_Glue3 var13 var12 var11 var10 var9 var8) (and (and (and (and (and (and (and (and (and (and (= (read var7 var9) var6) (= (getnode var6) var5)) (= (|node::val| var5) var4)) (not (<= 0 (+ (+ var11 (* (- 1) var4)) (- 1))))) (not (<= 0 (+ (+ var4 (* (- 1) var10)) (- 1))))) (not (valid var7 var9))) (= (getnode var8) var3)) (= (|node::val| var3) var2)) (= (node var12 var2) var1)) (= (O_node var1) var0)) (= (write var13 var9 var0) var7)))) (inv_main574_5 var7 var9 var11 var10))))
(assert (forall ((var0 Addr) (var1 HeapObject) (var2 node) (var3 Int) (var4 Int) (var5 Heap) (var6 Int) (var7 Addr) (var8 Addr)) (or (not (and (and (Inv_Heap_exp_exp var8 var7 var6) (inv_main586_5 var5 var4 var3 var8)) (and (and (and (and (and (and (and (= (O_node var2) var1) (= (node var7 var6) var2)) (= nullAddr var0)) (= (read var5 var8) var1)) (not (= var8 var0))) (not (<= 0 (+ (+ var4 (* (- 1) var6)) (- 1))))) (not (<= 0 (+ (+ var6 (* (- 1) var3)) (- 1))))) (valid var5 var8)))) (inv_main586_5 var5 var4 var3 var7))))
(assert (forall ((var0 Addr) (var1 Int) (var2 node) (var3 HeapObject) (var4 Addr) (var5 Addr) (var6 Int) (var7 Int) (var8 Heap)) (or (not (and (inv_main586_5 var8 var7 var6 var5) (and (and (and (and (and (and (and (and (= nullAddr var4) (= (read var8 var5) var3)) (= (getnode var3) var2)) (= (|node::val| var2) var1)) (= (|node::next| var2) var0)) (not (= var5 var4))) (not (<= 0 (+ (+ var7 (* (- 1) var1)) (- 1))))) (not (<= 0 (+ (+ var1 (* (- 1) var6)) (- 1))))) (not (valid var8 var5))))) (inv_main586_5 var8 var7 var6 var0))))
(assert (forall ((var0 AllocResHeap) (var1 Int) (var2 Addr) (var3 HeapObject) (var4 node) (var5 Int) (var6 Int) (var7 Addr) (var8 Heap)) (or (not (and (inv_main574_5 var8 var7 var6 var5) (and (and (= (O_node var4) var3) (= (node var2 var1) var4)) (= (alloc var8 var3) var0)))) (Inv_Heap_exp_exp (newAddr var0) var2 var1))))
(assert (forall ((var0 Int) (var1 AllocResHeap) (var2 Heap) (var3 HeapObject) (var4 node) (var5 HeapObject) (var6 node) (var7 Int) (var8 Int) (var9 Addr) (var10 Heap) (var11 Int) (var12 Addr) (var13 Addr)) (or (not (and (and (Inv_Heap_exp_exp var13 var12 var11) (inv_main574_5 var10 var9 var8 var7)) (and (and (and (and (and (and (= (O_node var6) var5) (= (O_node var4) var3)) (= (AllocResHeap var2 var13) var1)) (= (node var12 var11) var6)) (= (read var2 var13) var5)) (valid var2 var13)) (= (alloc var10 var3) var1)))) (_Glue6 var9 var8 var7 var0 var13 var2 var5))))
(assert (forall ((var0 Int) (var1 AllocResHeap) (var2 HeapObject) (var3 node) (var4 HeapObject) (var5 Addr) (var6 Heap) (var7 Int) (var8 Int) (var9 Addr) (var10 Heap)) (or (not (and (inv_main574_5 var10 var9 var8 var7) (and (and (and (and (= (read var6 var5) var4) (not (valid var6 var5))) (= (O_node var3) var2)) (= (AllocResHeap var6 var5) var1)) (= (alloc var10 var2) var1)))) (_Glue6 var9 var8 var7 var0 var5 var6 var4))))
(assert (forall ((var0 Addr) (var1 node) (var2 HeapObject) (var3 Heap) (var4 Addr) (var5 Int) (var6 Int) (var7 Int) (var8 Addr)) (or (not (and (_Glue6 var8 var7 var6 var5 var4 var3 var2) (and (and (= (getnode var2) var1) (= (|node::next| var1) var0)) (valid var3 var4)))) (Inv_Heap_exp_exp var4 var0 var5))))
(assert (forall ((var0 node) (var1 Heap) (var2 HeapObject) (var3 node) (var4 Addr) (var5 HeapObject) (var6 node) (var7 HeapObject) (var8 Heap) (var9 Int) (var10 Int) (var11 Int) (var12 Addr) (var13 Int) (var14 Addr) (var15 Addr)) (or (not (and (and (Inv_Heap_exp_exp var15 var14 var13) (_Glue6 var12 var11 var10 var9 var15 var8 var7)) (and (and (and (and (and (and (and (and (= (O_node var6) var5) (= (node var4 var9) var3)) (= (O_node var3) var2)) (= (node var14 var13) var6)) (= (read var1 var15) var5)) (valid var1 var15)) (= (getnode var7) var0)) (= (|node::next| var0) var4)) (= (write var8 var15 var2) var1)))) (_Glue8 var1 var12 var11 var10 var15 var5))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 node) (var4 HeapObject) (var5 Heap) (var6 HeapObject) (var7 Heap) (var8 Addr) (var9 Int) (var10 Int) (var11 Int) (var12 Addr)) (or (not (and (_Glue6 var12 var11 var10 var9 var8 var7 var6) (and (and (and (and (and (and (= (read var5 var8) var4) (not (valid var5 var8))) (= (getnode var6) var3)) (= (|node::next| var3) var2)) (= (node var2 var9) var1)) (= (O_node var1) var0)) (= (write var7 var8 var0) var5)))) (_Glue8 var5 var12 var11 var10 var8 var4))))
(assert (forall ((var0 Int) (var1 node) (var2 HeapObject) (var3 Addr) (var4 Int) (var5 Int) (var6 Addr) (var7 Heap)) (or (not (and (_Glue8 var7 var6 var5 var4 var3 var2) (and (and (= (getnode var2) var1) (= (|node::val| var1) var0)) (valid var7 var3)))) (Inv_Heap_exp_exp var3 var6 var0))))
(assert (forall ((var0 node) (var1 Heap) (var2 HeapObject) (var3 node) (var4 Int) (var5 HeapObject) (var6 node) (var7 HeapObject) (var8 Int) (var9 Int) (var10 Addr) (var11 Heap) (var12 Int) (var13 Addr) (var14 Addr)) (or (not (and (and (Inv_Heap_exp_exp var14 var13 var12) (_Glue8 var11 var10 var9 var8 var14 var7)) (and (and (and (and (and (and (and (and (and (and (= (O_node var6) var5) (= (node var10 var4) var3)) (= (O_node var3) var2)) (= (node var13 var12) var6)) (= (read var1 var14) var5)) (<= 0 (+ (+ var9 (* (- 1) var12)) (- 1)))) (not (<= 0 (+ (+ var12 (* (- 1) var8)) (- 1))))) (valid var1 var14)) (= (getnode var7) var0)) (= (|node::val| var0) var4)) (= (write var11 var14 var2) var1)))) (inv_main574_5 var1 var14 var12 var8))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Int) (var3 node) (var4 Int) (var5 node) (var6 HeapObject) (var7 Heap) (var8 HeapObject) (var9 Addr) (var10 Int) (var11 Int) (var12 Addr) (var13 Heap)) (or (not (and (_Glue8 var13 var12 var11 var10 var9 var8) (and (and (and (and (and (and (and (and (and (and (= (read var7 var9) var6) (= (getnode var6) var5)) (= (|node::val| var5) var4)) (<= 0 (+ (+ var11 (* (- 1) var4)) (- 1)))) (not (<= 0 (+ (+ var4 (* (- 1) var10)) (- 1))))) (not (valid var7 var9))) (= (getnode var8) var3)) (= (|node::val| var3) var2)) (= (node var12 var2) var1)) (= (O_node var1) var0)) (= (write var13 var9 var0) var7)))) (inv_main574_5 var7 var9 var4 var10))))
(assert (forall ((var0 AllocResHeap) (var1 Int) (var2 Addr) (var3 HeapObject) (var4 node) (var5 Int) (var6 Int) (var7 Addr) (var8 Heap)) (or (not (and (inv_main574_5 var8 var7 var6 var5) (and (and (= (O_node var4) var3) (= (node var2 var1) var4)) (= (alloc var8 var3) var0)))) (Inv_Heap_exp_exp (newAddr var0) var2 var1))))
(assert (forall ((var0 Int) (var1 Int) (var2 AllocResHeap) (var3 Heap) (var4 HeapObject) (var5 node) (var6 HeapObject) (var7 node) (var8 Int) (var9 Int) (var10 Addr) (var11 Heap) (var12 Int) (var13 Addr) (var14 Addr)) (or (not (and (and (Inv_Heap_exp_exp var14 var13 var12) (inv_main574_5 var11 var10 var9 var8)) (and (and (and (and (and (and (= (O_node var7) var6) (= (O_node var5) var4)) (= (AllocResHeap var3 var14) var2)) (= (node var13 var12) var7)) (= (read var3 var14) var6)) (valid var3 var14)) (= (alloc var11 var4) var2)))) (_Glue11 var10 var9 var8 var1 var0 var14 var3 var6))))
(assert (forall ((var0 Int) (var1 Int) (var2 AllocResHeap) (var3 HeapObject) (var4 node) (var5 HeapObject) (var6 Addr) (var7 Heap) (var8 Int) (var9 Int) (var10 Addr) (var11 Heap)) (or (not (and (inv_main574_5 var11 var10 var9 var8) (and (and (and (and (= (read var7 var6) var5) (not (valid var7 var6))) (= (O_node var4) var3)) (= (AllocResHeap var7 var6) var2)) (= (alloc var11 var3) var2)))) (_Glue11 var10 var9 var8 var1 var0 var6 var7 var5))))
(assert (forall ((var0 Addr) (var1 node) (var2 HeapObject) (var3 Heap) (var4 Addr) (var5 Int) (var6 Int) (var7 Int) (var8 Int) (var9 Addr)) (or (not (and (_Glue11 var9 var8 var7 var6 var5 var4 var3 var2) (and (and (= (getnode var2) var1) (= (|node::next| var1) var0)) (valid var3 var4)))) (Inv_Heap_exp_exp var4 var0 var6))))
(assert (forall ((var0 node) (var1 Heap) (var2 HeapObject) (var3 node) (var4 Addr) (var5 HeapObject) (var6 node) (var7 HeapObject) (var8 Heap) (var9 Int) (var10 Int) (var11 Int) (var12 Int) (var13 Addr) (var14 Int) (var15 Addr) (var16 Addr)) (or (not (and (and (Inv_Heap_exp_exp var16 var15 var14) (_Glue11 var13 var12 var11 var10 var9 var16 var8 var7)) (and (and (and (and (and (and (and (and (= (O_node var6) var5) (= (node var4 var10) var3)) (= (O_node var3) var2)) (= (node var15 var14) var6)) (= (read var1 var16) var5)) (valid var1 var16)) (= (getnode var7) var0)) (= (|node::next| var0) var4)) (= (write var8 var16 var2) var1)))) (_Glue13 var1 var13 var12 var11 var9 var16 var5))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 node) (var4 HeapObject) (var5 Heap) (var6 HeapObject) (var7 Heap) (var8 Addr) (var9 Int) (var10 Int) (var11 Int) (var12 Int) (var13 Addr)) (or (not (and (_Glue11 var13 var12 var11 var10 var9 var8 var7 var6) (and (and (and (and (and (and (= (read var5 var8) var4) (not (valid var5 var8))) (= (getnode var6) var3)) (= (|node::next| var3) var2)) (= (node var2 var10) var1)) (= (O_node var1) var0)) (= (write var7 var8 var0) var5)))) (_Glue13 var5 var13 var12 var11 var9 var8 var4))))
(assert (forall ((var0 Int) (var1 node) (var2 HeapObject) (var3 Addr) (var4 Int) (var5 Int) (var6 Int) (var7 Addr) (var8 Heap)) (or (not (and (_Glue13 var8 var7 var6 var5 var4 var3 var2) (and (and (= (getnode var2) var1) (= (|node::val| var1) var0)) (valid var8 var3)))) (Inv_Heap_exp_exp var3 var7 var0))))
(assert (forall ((var0 Int) (var1 node) (var2 Heap) (var3 HeapObject) (var4 node) (var5 Int) (var6 HeapObject) (var7 node) (var8 HeapObject) (var9 Int) (var10 Int) (var11 Addr) (var12 Heap) (var13 Int) (var14 Addr) (var15 Addr)) (or (not (and (and (Inv_Heap_exp_exp var15 var14 var13) (_Glue13 var12 var11 var10 var9 var13 var15 var8)) (and (and (and (and (and (and (and (and (and (and (and (= (O_node var7) var6) (= (node var11 var5) var4)) (= (O_node var4) var3)) (= (node var14 var13) var7)) (= (read var2 var15) var6)) (<= 0 (+ (+ var10 (* (- 1) var13)) (- 1)))) (<= 0 (+ (+ var13 (* (- 1) var9)) (- 1)))) (valid var2 var15)) (= (getnode var8) var1)) (= (|node::val| var1) var5)) (= (write var12 var15 var3) var2)) (= var0 var13)))) (inv_main574_5 var2 var15 var0 var13))))
(assert (forall ((var0 Int) (var1 HeapObject) (var2 node) (var3 Int) (var4 node) (var5 node) (var6 HeapObject) (var7 Heap) (var8 HeapObject) (var9 Addr) (var10 Int) (var11 Int) (var12 Int) (var13 Addr) (var14 Heap)) (or (not (and (_Glue13 var14 var13 var12 var11 var10 var9 var8) (and (and (and (and (and (and (and (and (and (and (and (= (read var7 var9) var6) (= (getnode var6) var5)) (= (|node::val| var5) var10)) (<= 0 (+ (+ var12 (* (- 1) var10)) (- 1)))) (<= 0 (+ (+ var10 (* (- 1) var11)) (- 1)))) (not (valid var7 var9))) (= (getnode var8) var4)) (= (|node::val| var4) var3)) (= (node var13 var3) var2)) (= (O_node var2) var1)) (= (write var14 var9 var1) var7)) (= var0 var10)))) (inv_main574_5 var7 var9 var0 var10))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Heap)) (or (not (inv_main574_5 var3 var2 var1 var0)) (inv_main586_5 var3 var1 var0 var2))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Int) (var3 Int) (var4 Heap) (var5 Int) (var6 Addr) (var7 Addr)) (or (not (and (and (Inv_Heap_exp_exp var7 var6 var5) (inv_main590_13_14 var4 var3 var2 var7)) (and (and (and (= (O_node var1) var0) (= (node var6 var5) var1)) (= (read var4 var7) var0)) (valid var4 var7)))) (inv_main586_5 var4 var3 var2 var6))))
(assert (forall ((var0 Addr) (var1 node) (var2 HeapObject) (var3 Addr) (var4 Int) (var5 Int) (var6 Heap)) (or (not (and (inv_main590_13_14 var6 var5 var4 var3) (and (and (and (= (read var6 var3) var2) (= (getnode var2) var1)) (= (|node::next| var1) var0)) (not (valid var6 var3))))) (inv_main586_5 var6 var5 var4 var0))))
(assert (forall ((var0 Addr) (var1 HeapObject) (var2 node) (var3 Int) (var4 Int) (var5 Heap) (var6 Int) (var7 Addr) (var8 Addr)) (or (not (and (and (Inv_Heap_exp_exp var8 var7 var6) (inv_main586_5 var5 var4 var3 var8)) (and (and (and (and (and (and (and (= (O_node var2) var1) (= (node var7 var6) var2)) (= (read var5 var8) var1)) (= nullAddr var0)) (not (<= 0 (+ (+ var6 (* (- 1) var3)) (- 1))))) (not (= var8 var0))) (<= 0 (+ (+ var4 (* (- 1) var6)) (- 1)))) (valid var5 var8)))) (inv_main586_5 var5 var4 var3 var7))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 node) (var4 HeapObject) (var5 Addr) (var6 Int) (var7 Int) (var8 Heap)) (or (not (and (inv_main586_5 var8 var7 var6 var5) (and (and (and (and (and (and (and (and (= (read var8 var5) var4) (= (getnode var4) var3)) (= (|node::val| var3) var2)) (= (|node::next| var3) var1)) (= nullAddr var0)) (not (<= 0 (+ (+ var2 (* (- 1) var6)) (- 1))))) (not (= var5 var0))) (<= 0 (+ (+ var7 (* (- 1) var2)) (- 1)))) (not (valid var8 var5))))) (inv_main586_5 var8 var7 var6 var1))))
(assert (forall ((var0 AllocResHeap) (var1 Int) (var2 Addr) (var3 HeapObject) (var4 node) (var5 Int) (var6 Int) (var7 Addr) (var8 Heap)) (or (not (and (inv_main574_5 var8 var7 var6 var5) (and (and (= (O_node var4) var3) (= (node var2 var1) var4)) (= (alloc var8 var3) var0)))) (Inv_Heap_exp_exp (newAddr var0) var2 var1))))
(assert (forall ((var0 Int) (var1 AllocResHeap) (var2 Heap) (var3 HeapObject) (var4 node) (var5 HeapObject) (var6 node) (var7 Int) (var8 Int) (var9 Addr) (var10 Heap) (var11 Int) (var12 Addr) (var13 Addr)) (or (not (and (and (Inv_Heap_exp_exp var13 var12 var11) (inv_main574_5 var10 var9 var8 var7)) (and (and (and (and (and (and (= (O_node var6) var5) (= (O_node var4) var3)) (= (AllocResHeap var2 var13) var1)) (= (node var12 var11) var6)) (= (read var2 var13) var5)) (valid var2 var13)) (= (alloc var10 var3) var1)))) (_Glue16 var9 var8 var7 var0 var13 var2 var5))))
(assert (forall ((var0 Int) (var1 AllocResHeap) (var2 HeapObject) (var3 node) (var4 HeapObject) (var5 Addr) (var6 Heap) (var7 Int) (var8 Int) (var9 Addr) (var10 Heap)) (or (not (and (inv_main574_5 var10 var9 var8 var7) (and (and (and (and (= (read var6 var5) var4) (not (valid var6 var5))) (= (O_node var3) var2)) (= (AllocResHeap var6 var5) var1)) (= (alloc var10 var2) var1)))) (_Glue16 var9 var8 var7 var0 var5 var6 var4))))
(assert (forall ((var0 Addr) (var1 node) (var2 HeapObject) (var3 Heap) (var4 Addr) (var5 Int) (var6 Int) (var7 Int) (var8 Addr)) (or (not (and (_Glue16 var8 var7 var6 var5 var4 var3 var2) (and (and (= (getnode var2) var1) (= (|node::next| var1) var0)) (valid var3 var4)))) (Inv_Heap_exp_exp var4 var0 var5))))
(assert (forall ((var0 node) (var1 Heap) (var2 HeapObject) (var3 node) (var4 Addr) (var5 HeapObject) (var6 node) (var7 HeapObject) (var8 Heap) (var9 Int) (var10 Int) (var11 Int) (var12 Addr) (var13 Int) (var14 Addr) (var15 Addr)) (or (not (and (and (Inv_Heap_exp_exp var15 var14 var13) (_Glue16 var12 var11 var10 var9 var15 var8 var7)) (and (and (and (and (and (and (and (and (= (O_node var6) var5) (= (node var4 var9) var3)) (= (O_node var3) var2)) (= (node var14 var13) var6)) (= (read var1 var15) var5)) (valid var1 var15)) (= (getnode var7) var0)) (= (|node::next| var0) var4)) (= (write var8 var15 var2) var1)))) (_Glue18 var1 var12 var11 var10 var15 var5))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 node) (var4 HeapObject) (var5 Heap) (var6 HeapObject) (var7 Heap) (var8 Addr) (var9 Int) (var10 Int) (var11 Int) (var12 Addr)) (or (not (and (_Glue16 var12 var11 var10 var9 var8 var7 var6) (and (and (and (and (and (and (= (read var5 var8) var4) (not (valid var5 var8))) (= (getnode var6) var3)) (= (|node::next| var3) var2)) (= (node var2 var9) var1)) (= (O_node var1) var0)) (= (write var7 var8 var0) var5)))) (_Glue18 var5 var12 var11 var10 var8 var4))))
(assert (forall ((var0 Int) (var1 node) (var2 HeapObject) (var3 Addr) (var4 Int) (var5 Int) (var6 Addr) (var7 Heap)) (or (not (and (_Glue18 var7 var6 var5 var4 var3 var2) (and (and (= (getnode var2) var1) (= (|node::val| var1) var0)) (valid var7 var3)))) (Inv_Heap_exp_exp var3 var6 var0))))
(assert (forall ((var0 node) (var1 Heap) (var2 HeapObject) (var3 node) (var4 Int) (var5 HeapObject) (var6 node) (var7 HeapObject) (var8 Int) (var9 Int) (var10 Addr) (var11 Heap) (var12 Int) (var13 Addr) (var14 Addr)) (or (not (and (and (Inv_Heap_exp_exp var14 var13 var12) (_Glue18 var11 var10 var9 var8 var14 var7)) (and (and (and (and (and (and (and (and (and (and (= (O_node var6) var5) (= (node var10 var4) var3)) (= (O_node var3) var2)) (= (node var13 var12) var6)) (= (read var1 var14) var5)) (not (<= 0 (+ (+ var9 (* (- 1) var12)) (- 1))))) (<= 0 (+ (+ var12 (* (- 1) var8)) (- 1)))) (valid var1 var14)) (= (getnode var7) var0)) (= (|node::val| var0) var4)) (= (write var11 var14 var2) var1)))) (inv_main574_5 var1 var14 var9 var12))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Int) (var3 node) (var4 Int) (var5 node) (var6 HeapObject) (var7 Heap) (var8 HeapObject) (var9 Addr) (var10 Int) (var11 Int) (var12 Addr) (var13 Heap)) (or (not (and (_Glue18 var13 var12 var11 var10 var9 var8) (and (and (and (and (and (and (and (and (and (and (= (read var7 var9) var6) (= (getnode var6) var5)) (= (|node::val| var5) var4)) (not (<= 0 (+ (+ var11 (* (- 1) var4)) (- 1))))) (<= 0 (+ (+ var4 (* (- 1) var10)) (- 1)))) (not (valid var7 var9))) (= (getnode var8) var3)) (= (|node::val| var3) var2)) (= (node var12 var2) var1)) (= (O_node var1) var0)) (= (write var13 var9 var0) var7)))) (inv_main574_5 var7 var9 var11 var4))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Heap)) (not (inv_main590_13_14 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Heap) (var3 Addr)) (or (not (and (and (and (= nullAddr var3) (= emptyHeap var2)) (= var1 (- 2147483647))) (= var0 2147483647))) (inv_main574_5 var2 var3 var0 var1))))
(assert (forall ((var0 Addr) (var1 HeapObject) (var2 node) (var3 Int) (var4 Int) (var5 Heap) (var6 Int) (var7 Addr) (var8 Addr)) (or (not (and (and (Inv_Heap_exp_exp var8 var7 var6) (inv_main586_5 var5 var4 var3 var8)) (and (and (and (and (and (and (and (= (O_node var2) var1) (= (node var7 var6) var2)) (= nullAddr var0)) (= (read var5 var8) var1)) (not (= var8 var0))) (not (<= 0 (+ (+ var4 (* (- 1) var6)) (- 1))))) (<= 0 (+ (+ var6 (* (- 1) var3)) (- 1)))) (valid var5 var8)))) (inv_main590_13_14 var5 var4 var3 var8))))
(assert (forall ((var0 Int) (var1 node) (var2 HeapObject) (var3 Addr) (var4 Addr) (var5 Int) (var6 Int) (var7 Heap)) (or (not (and (inv_main586_5 var7 var6 var5 var4) (and (and (and (and (and (and (and (= nullAddr var3) (= (read var7 var4) var2)) (= (getnode var2) var1)) (= (|node::val| var1) var0)) (not (= var4 var3))) (not (<= 0 (+ (+ var6 (* (- 1) var0)) (- 1))))) (<= 0 (+ (+ var0 (* (- 1) var5)) (- 1)))) (not (valid var7 var4))))) (inv_main590_13_14 var7 var6 var5 var4))))
(assert (forall ((var0 Addr) (var1 HeapObject) (var2 node) (var3 Int) (var4 Int) (var5 Heap) (var6 Int) (var7 Addr) (var8 Addr)) (not (and (and (Inv_Heap_exp_exp var8 var7 var6) (inv_main586_5 var5 var4 var3 var8)) (and (and (and (and (and (and (= (O_node var2) var1) (= (node var7 var6) var2)) (not (= var8 var0))) (<= 0 (+ (+ var4 (* (- 1) var6)) (- 1)))) (= nullAddr var0)) (= (read var5 var8) var1)) (valid var5 var8))))))
(assert (forall ((var0 node) (var1 HeapObject) (var2 Int) (var3 Addr) (var4 Addr) (var5 Int) (var6 Int) (var7 Heap)) (not (and (inv_main586_5 var7 var6 var5 var4) (and (and (and (and (and (and (not (= var4 var3)) (<= 0 (+ (+ var6 (* (- 1) var2)) (- 1)))) (= nullAddr var3)) (= (read var7 var4) var1)) (= (getnode var1) var0)) (= (|node::val| var0) var2)) (not (valid var7 var4)))))))
(check-sat)