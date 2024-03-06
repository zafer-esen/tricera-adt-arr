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
   (node (|node::next| Addr) (|node::event1| Int) (|node::event2| Int))
  )
))
(declare-fun inv_main589_13 (Heap Addr Int) Bool)
(declare-fun inv_main587_5 (Heap Addr) Bool)
(declare-fun Inv_Heap_exp_exp (Addr Addr Int Int) Bool)
(declare-fun _Glue1 (Addr Int Int Addr Heap HeapObject) Bool)
(declare-fun _Glue3 (Heap Addr Int Addr HeapObject) Bool)
(declare-fun inv_main574_5_1 (Heap Addr) Bool)
(declare-fun inv_main589_14 (Heap Addr Int) Bool)
(declare-fun _Glue5 (Heap Addr Addr HeapObject) Bool)
(assert (forall ((var0 Int) (var1 HeapObject) (var2 node) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr)) (or (not (and (and (Inv_Heap_exp_exp var6 var5 1 3) (inv_main587_5 var4 var6)) (and (and (and (and (and (and (not (= var3 var6)) (= (O_node var2) var1)) (= (node var5 1 3) var2)) (= nullAddr var3)) (= (read var4 var6) var1)) (valid var4 var6)) (= var0 1)))) (inv_main589_14 var4 var6 var0))))
(assert (forall ((var0 Int) (var1 HeapObject) (var2 node) (var3 Addr) (var4 Heap) (var5 Int) (var6 Addr) (var7 Addr)) (or (not (and (and (Inv_Heap_exp_exp var7 var6 1 var5) (inv_main587_5 var4 var7)) (and (and (and (and (and (and (and (not (= var3 var7)) (not (= var5 3))) (= (O_node var2) var1)) (= (node var6 1 var5) var2)) (= nullAddr var3)) (= (read var4 var7) var1)) (valid var4 var7)) (= var0 0)))) (inv_main589_14 var4 var7 var0))))
(assert (forall ((var0 Int) (var1 node) (var2 HeapObject) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main587_5 var5 var4) (and (and (and (and (and (and (and (not (= var3 var4)) (= nullAddr var3)) (= (read var5 var4) var2)) (= (getnode var2) var1)) (= (|node::event2| var1) 3)) (= (|node::event1| var1) 1)) (not (valid var5 var4))) (= var0 1)))) (inv_main589_14 var5 var4 var0))))
(assert (forall ((var0 Int) (var1 node) (var2 HeapObject) (var3 Int) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main587_5 var6 var5) (and (and (and (and (and (and (and (and (not (= var4 var5)) (not (= var3 3))) (= nullAddr var4)) (= (read var6 var5) var2)) (= (getnode var2) var1)) (= (|node::event2| var1) var3)) (= (|node::event1| var1) 1)) (not (valid var6 var5))) (= var0 0)))) (inv_main589_14 var6 var5 var0))))
(assert (forall ((var0 Heap) (var1 Addr)) (or (not (and (= nullAddr var1) (= emptyHeap var0))) (inv_main574_5_1 var0 var1))))
(assert (forall ((var0 Int) (var1 HeapObject) (var2 node) (var3 Heap) (var4 Addr) (var5 Addr)) (or (not (and (and (Inv_Heap_exp_exp var5 var4 0 2) (inv_main589_14 var3 var5 0)) (and (and (and (and (= (O_node var2) var1) (= (node var4 0 2) var2)) (= (read var3 var5) var1)) (valid var3 var5)) (= var0 1)))) (inv_main589_13 var3 var5 var0))))
(assert (forall ((var0 Int) (var1 HeapObject) (var2 node) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr)) (or (not (and (and (Inv_Heap_exp_exp var6 var5 0 var4) (inv_main589_14 var3 var6 0)) (and (and (and (and (and (not (= var4 2)) (= (O_node var2) var1)) (= (node var5 0 var4) var2)) (= (read var3 var6) var1)) (valid var3 var6)) (= var0 0)))) (inv_main589_13 var3 var6 var0))))
(assert (forall ((var0 Int) (var1 node) (var2 HeapObject) (var3 Addr) (var4 Heap)) (or (not (and (inv_main589_14 var4 var3 0) (and (and (and (and (and (= (read var4 var3) var2) (= (getnode var2) var1)) (= (|node::event2| var1) 2)) (= (|node::event1| var1) 0)) (not (valid var4 var3))) (= var0 1)))) (inv_main589_13 var4 var3 var0))))
(assert (forall ((var0 Int) (var1 node) (var2 HeapObject) (var3 Int) (var4 Addr) (var5 Heap)) (or (not (and (inv_main589_14 var5 var4 0) (and (and (and (and (and (and (not (= var3 2)) (= (read var5 var4) var2)) (= (getnode var2) var1)) (= (|node::event2| var1) var3)) (= (|node::event1| var1) 0)) (not (valid var5 var4))) (= var0 0)))) (inv_main589_13 var5 var4 var0))))
(assert (forall ((var0 Addr) (var1 Heap)) (or (not (inv_main574_5_1 var1 var0)) (inv_main574_5_1 var1 var0))))
(assert (forall ((var0 Addr) (var1 Heap)) (or (not (inv_main574_5_1 var1 var0)) (inv_main574_5_1 var1 var0))))
(assert (forall ((var0 Addr) (var1 Heap)) (or (not (inv_main574_5_1 var1 var0)) (inv_main574_5_1 var1 var0))))
(assert (forall ((var0 Addr) (var1 Heap)) (or (not (inv_main574_5_1 var1 var0)) (inv_main574_5_1 var1 var0))))
(assert (forall ((var0 Addr) (var1 Heap)) (or (not (inv_main574_5_1 var1 var0)) (inv_main574_5_1 var1 var0))))
(assert (forall ((var0 Addr) (var1 Heap)) (or (not (inv_main574_5_1 var1 var0)) (inv_main574_5_1 var1 var0))))
(assert (forall ((var0 Addr) (var1 Heap)) (or (not (inv_main574_5_1 var1 var0)) (inv_main574_5_1 var1 var0))))
(assert (forall ((var0 AllocResHeap) (var1 Int) (var2 Int) (var3 Addr) (var4 HeapObject) (var5 node) (var6 Int) (var7 Addr) (var8 Heap)) (or (not (and (inv_main574_5_1 var8 var7) (and (and (and (and (<= 0 (+ (* (- 1) var6) 2)) (<= 0 var6)) (= (O_node var5) var4)) (= (node var3 var2 var1) var5)) (= (alloc var8 var4) var0)))) (Inv_Heap_exp_exp (newAddr var0) var3 var2 var1))))
(assert (forall ((var0 AllocResHeap) (var1 Int) (var2 Int) (var3 Addr) (var4 HeapObject) (var5 node) (var6 Int) (var7 Addr) (var8 Heap)) (or (not (and (inv_main574_5_1 var8 var7) (and (and (and (and (<= 0 (+ (* (- 1) var6) 1)) (<= 0 var6)) (= (O_node var5) var4)) (= (node var3 var2 var1) var5)) (= (alloc var8 var4) var0)))) (Inv_Heap_exp_exp (newAddr var0) var3 var2 var1))))
(assert (forall ((var0 AllocResHeap) (var1 Int) (var2 Int) (var3 Addr) (var4 HeapObject) (var5 node) (var6 Int) (var7 Int) (var8 Addr) (var9 Heap)) (or (not (and (inv_main574_5_1 var9 var8) (and (and (and (and (and (and (<= 0 (+ (* (- 1) var7) 3)) (<= 0 (+ var7 (- 2)))) (<= 0 (+ (* (- 1) var6) 3))) (<= 0 var6)) (= (O_node var5) var4)) (= (node var3 var2 var1) var5)) (= (alloc var9 var4) var0)))) (Inv_Heap_exp_exp (newAddr var0) var3 var2 var1))))
(assert (forall ((var0 Int) (var1 AllocResHeap) (var2 Heap) (var3 HeapObject) (var4 node) (var5 HeapObject) (var6 node) (var7 Int) (var8 Addr) (var9 Heap) (var10 Int) (var11 Int) (var12 Addr) (var13 Addr)) (or (not (and (and (Inv_Heap_exp_exp var13 var12 var11 var10) (inv_main574_5_1 var9 var8)) (and (and (and (and (and (and (and (and (and (<= 0 (+ (* (- 1) var7) 2)) (<= 0 var7)) (= (O_node var6) var5)) (= (O_node var4) var3)) (= (AllocResHeap var2 var13) var1)) (= (node var12 var11 var10) var6)) (= (read var2 var13) var5)) (valid var2 var13)) (= (alloc var9 var3) var1)) (= var0 1)))) (_Glue1 var8 var0 var7 var13 var2 var5))))
(assert (forall ((var0 Int) (var1 AllocResHeap) (var2 Heap) (var3 HeapObject) (var4 node) (var5 HeapObject) (var6 node) (var7 Int) (var8 Addr) (var9 Heap) (var10 Int) (var11 Int) (var12 Addr) (var13 Addr)) (or (not (and (and (Inv_Heap_exp_exp var13 var12 var11 var10) (inv_main574_5_1 var9 var8)) (and (and (and (and (and (and (and (and (and (<= 0 (+ (* (- 1) var7) 1)) (<= 0 var7)) (= (O_node var6) var5)) (= (O_node var4) var3)) (= (AllocResHeap var2 var13) var1)) (= (node var12 var11 var10) var6)) (= (read var2 var13) var5)) (valid var2 var13)) (= (alloc var9 var3) var1)) (= var0 0)))) (_Glue1 var8 var0 var7 var13 var2 var5))))
(assert (forall ((var0 AllocResHeap) (var1 Heap) (var2 HeapObject) (var3 node) (var4 HeapObject) (var5 node) (var6 Int) (var7 Int) (var8 Addr) (var9 Heap) (var10 Int) (var11 Int) (var12 Addr) (var13 Addr)) (or (not (and (and (Inv_Heap_exp_exp var13 var12 var11 var10) (inv_main574_5_1 var9 var8)) (and (and (and (and (and (and (and (and (and (and (<= 0 (+ (* (- 1) var7) 3)) (<= 0 (+ var7 (- 2)))) (<= 0 (+ (* (- 1) var6) 3))) (<= 0 var6)) (= (O_node var5) var4)) (= (O_node var3) var2)) (= (AllocResHeap var1 var13) var0)) (= (node var12 var11 var10) var5)) (= (read var1 var13) var4)) (valid var1 var13)) (= (alloc var9 var2) var0)))) (_Glue1 var8 var7 var6 var13 var1 var4))))
(assert (forall ((var0 Int) (var1 AllocResHeap) (var2 HeapObject) (var3 node) (var4 HeapObject) (var5 Addr) (var6 Heap) (var7 Int) (var8 Addr) (var9 Heap)) (or (not (and (inv_main574_5_1 var9 var8) (and (and (and (and (and (and (and (<= 0 (+ (* (- 1) var7) 2)) (<= 0 var7)) (= (read var6 var5) var4)) (not (valid var6 var5))) (= (O_node var3) var2)) (= (AllocResHeap var6 var5) var1)) (= (alloc var9 var2) var1)) (= var0 1)))) (_Glue1 var8 var0 var7 var5 var6 var4))))
(assert (forall ((var0 Int) (var1 AllocResHeap) (var2 HeapObject) (var3 node) (var4 HeapObject) (var5 Addr) (var6 Heap) (var7 Int) (var8 Addr) (var9 Heap)) (or (not (and (inv_main574_5_1 var9 var8) (and (and (and (and (and (and (and (<= 0 (+ (* (- 1) var7) 1)) (<= 0 var7)) (= (read var6 var5) var4)) (not (valid var6 var5))) (= (O_node var3) var2)) (= (AllocResHeap var6 var5) var1)) (= (alloc var9 var2) var1)) (= var0 0)))) (_Glue1 var8 var0 var7 var5 var6 var4))))
(assert (forall ((var0 AllocResHeap) (var1 HeapObject) (var2 node) (var3 HeapObject) (var4 Addr) (var5 Heap) (var6 Int) (var7 Int) (var8 Addr) (var9 Heap)) (or (not (and (inv_main574_5_1 var9 var8) (and (and (and (and (and (and (and (and (<= 0 (+ (* (- 1) var7) 3)) (<= 0 (+ var7 (- 2)))) (<= 0 (+ (* (- 1) var6) 3))) (<= 0 var6)) (= (read var5 var4) var3)) (not (valid var5 var4))) (= (O_node var2) var1)) (= (AllocResHeap var5 var4) var0)) (= (alloc var9 var1) var0)))) (_Glue1 var8 var7 var6 var4 var5 var3))))
(assert (forall ((var0 Int) (var1 Addr) (var2 node) (var3 HeapObject) (var4 Heap) (var5 Addr) (var6 Int) (var7 Int) (var8 Addr)) (or (not (and (_Glue1 var8 var7 var6 var5 var4 var3) (and (and (and (= (getnode var3) var2) (= (|node::next| var2) var1)) (= (|node::event2| var2) var0)) (valid var4 var5)))) (Inv_Heap_exp_exp var5 var1 var7 var0))))
(assert (forall ((var0 node) (var1 Heap) (var2 HeapObject) (var3 node) (var4 Int) (var5 Addr) (var6 HeapObject) (var7 node) (var8 HeapObject) (var9 Heap) (var10 Int) (var11 Int) (var12 Addr) (var13 Int) (var14 Int) (var15 Addr) (var16 Addr)) (or (not (and (and (Inv_Heap_exp_exp var16 var15 var14 var13) (_Glue1 var12 var11 var10 var16 var9 var8)) (and (and (and (and (and (and (and (and (and (= (O_node var7) var6) (= (node var5 var11 var4) var3)) (= (O_node var3) var2)) (= (node var15 var14 var13) var7)) (= (read var1 var16) var6)) (valid var1 var16)) (= (getnode var8) var0)) (= (|node::next| var0) var5)) (= (|node::event2| var0) var4)) (= (write var9 var16 var2) var1)))) (_Glue3 var1 var12 var10 var16 var6))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Int) (var3 Addr) (var4 node) (var5 HeapObject) (var6 Heap) (var7 HeapObject) (var8 Heap) (var9 Addr) (var10 Int) (var11 Int) (var12 Addr)) (or (not (and (_Glue1 var12 var11 var10 var9 var8 var7) (and (and (and (and (and (and (and (= (read var6 var9) var5) (not (valid var6 var9))) (= (getnode var7) var4)) (= (|node::next| var4) var3)) (= (|node::event2| var4) var2)) (= (node var3 var11 var2) var1)) (= (O_node var1) var0)) (= (write var8 var9 var0) var6)))) (_Glue3 var6 var12 var10 var9 var5))))
(assert (forall ((var0 Int) (var1 Addr) (var2 node) (var3 HeapObject) (var4 Addr) (var5 Int) (var6 Addr) (var7 Heap)) (or (not (and (_Glue3 var7 var6 var5 var4 var3) (and (and (and (= (getnode var3) var2) (= (|node::next| var2) var1)) (= (|node::event1| var2) var0)) (valid var7 var4)))) (Inv_Heap_exp_exp var4 var1 var0 var5))))
(assert (forall ((var0 node) (var1 Heap) (var2 HeapObject) (var3 node) (var4 Int) (var5 Addr) (var6 HeapObject) (var7 node) (var8 HeapObject) (var9 Int) (var10 Addr) (var11 Heap) (var12 Int) (var13 Int) (var14 Addr) (var15 Addr)) (or (not (and (and (Inv_Heap_exp_exp var15 var14 var13 var12) (_Glue3 var11 var10 var9 var15 var8)) (and (and (and (and (and (and (and (and (and (= (O_node var7) var6) (= (node var5 var4 var9) var3)) (= (O_node var3) var2)) (= (node var14 var13 var12) var7)) (= (read var1 var15) var6)) (valid var1 var15)) (= (getnode var8) var0)) (= (|node::next| var0) var5)) (= (|node::event1| var0) var4)) (= (write var11 var15 var2) var1)))) (_Glue5 var1 var10 var15 var6))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Int) (var3 Addr) (var4 node) (var5 HeapObject) (var6 Heap) (var7 HeapObject) (var8 Addr) (var9 Int) (var10 Addr) (var11 Heap)) (or (not (and (_Glue3 var11 var10 var9 var8 var7) (and (and (and (and (and (and (and (= (read var6 var8) var5) (not (valid var6 var8))) (= (getnode var7) var4)) (= (|node::next| var4) var3)) (= (|node::event1| var4) var2)) (= (node var3 var2 var9) var1)) (= (O_node var1) var0)) (= (write var11 var8 var0) var6)))) (_Glue5 var6 var10 var8 var5))))
(assert (forall ((var0 Int) (var1 Int) (var2 node) (var3 HeapObject) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (_Glue5 var6 var5 var4 var3) (and (and (and (= (getnode var3) var2) (= (|node::event1| var2) var1)) (= (|node::event2| var2) var0)) (valid var6 var4)))) (Inv_Heap_exp_exp var4 var5 var1 var0))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 node) (var3 Int) (var4 Int) (var5 node) (var6 HeapObject) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (_Glue5 var9 var8 var7 var6) (and (and (and (and (and (= (getnode var6) var5) (= (|node::event1| var5) var4)) (= (|node::event2| var5) var3)) (= (node var8 var4 var3) var2)) (= (O_node var2) var1)) (= (write var9 var7 var1) var0)))) (inv_main574_5_1 var0 var7))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap)) (not (and (inv_main589_13 var2 var1 var0) (not (= var0 0))))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Int) (var3 Heap) (var4 Int) (var5 Int) (var6 Addr) (var7 Addr)) (or (not (and (and (Inv_Heap_exp_exp var7 var6 var5 var4) (inv_main589_13 var3 var7 var2)) (and (and (and (and (= (O_node var1) var0) (= (node var6 var5 var4) var1)) (= (read var3 var7) var0)) (not (= var2 0))) (valid var3 var7)))) (inv_main587_5 var3 var6))))
(assert (forall ((var0 Addr) (var1 node) (var2 HeapObject) (var3 Int) (var4 Addr) (var5 Heap)) (or (not (and (inv_main589_13 var5 var4 var3) (and (and (and (and (= (read var5 var4) var2) (= (getnode var2) var1)) (= (|node::next| var1) var0)) (not (= var3 0))) (not (valid var5 var4))))) (inv_main587_5 var5 var0))))
(assert (forall ((var0 Int) (var1 HeapObject) (var2 node) (var3 Heap) (var4 Int) (var5 Int) (var6 Addr) (var7 Addr)) (or (not (and (and (Inv_Heap_exp_exp var7 var6 var5 var4) (inv_main589_14 var3 var7 0)) (and (and (and (and (and (= (O_node var2) var1) (= (node var6 var5 var4) var2)) (not (= var5 0))) (= (read var3 var7) var1)) (valid var3 var7)) (= var0 0)))) (inv_main589_13 var3 var7 var0))))
(assert (forall ((var0 Int) (var1 node) (var2 HeapObject) (var3 Int) (var4 Addr) (var5 Heap)) (or (not (and (inv_main589_14 var5 var4 0) (and (and (and (and (and (not (= var3 0)) (= (read var5 var4) var2)) (= (getnode var2) var1)) (= (|node::event1| var1) var3)) (not (valid var5 var4))) (= var0 0)))) (inv_main589_13 var5 var4 var0))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Heap) (var3 Int) (var4 Int) (var5 Addr) (var6 Addr)) (or (not (and (and (Inv_Heap_exp_exp var6 var5 var4 var3) (inv_main589_13 var2 var6 0)) (and (and (and (= (O_node var1) var0) (= (node var5 var4 var3) var1)) (= (read var2 var6) var0)) (valid var2 var6)))) (inv_main587_5 var2 var5))))
(assert (forall ((var0 Addr) (var1 node) (var2 HeapObject) (var3 Addr) (var4 Heap)) (or (not (and (inv_main589_13 var4 var3 0) (and (and (and (= (read var4 var3) var2) (= (getnode var2) var1)) (= (|node::next| var1) var0)) (not (valid var4 var3))))) (inv_main587_5 var4 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 HeapObject) (var3 node) (var4 Heap) (var5 Int) (var6 Int) (var7 Addr) (var8 Addr)) (or (not (and (and (Inv_Heap_exp_exp var8 var7 var6 var5) (inv_main587_5 var4 var8)) (and (and (and (and (and (and (and (= (O_node var3) var2) (= (node var7 var6 var5) var3)) (not (= var8 var1))) (not (= var6 1))) (= nullAddr var1)) (= (read var4 var8) var2)) (valid var4 var8)) (= var0 0)))) (inv_main589_14 var4 var8 var0))))
(assert (forall ((var0 Int) (var1 node) (var2 HeapObject) (var3 Int) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main587_5 var6 var5) (and (and (and (and (and (and (and (not (= var5 var4)) (not (= var3 1))) (= nullAddr var4)) (= (read var6 var5) var2)) (= (getnode var2) var1)) (= (|node::event1| var1) var3)) (not (valid var6 var5))) (= var0 0)))) (inv_main589_14 var6 var5 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Heap)) (or (not (and (inv_main589_14 var3 var2 var1) (and (not (= var1 0)) (= var0 1)))) (inv_main589_13 var3 var2 var0))))
(assert (forall ((var0 Addr) (var1 Heap)) (or (not (inv_main574_5_1 var1 var0)) (inv_main587_5 var1 var0))))
(check-sat)
