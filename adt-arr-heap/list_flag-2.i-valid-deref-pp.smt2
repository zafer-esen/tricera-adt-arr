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
   (node (|node::h| Int) (|node::n| Addr))
  )
))
(declare-fun inv_main_4 (Heap Int Addr Addr) Bool)
(declare-fun _Glue7 (Addr Int Addr Heap Addr HeapObject) Bool)
(declare-fun inv_main_16 (Heap Addr) Bool)
(declare-fun inv_main554_5 (Heap Addr) Bool)
(declare-fun _Glue6 (Addr Addr Int Heap Addr HeapObject) Bool)
(declare-fun _Glue9_exp_exp (Addr Int Addr Addr Int Heap Addr HeapObject) Bool)
(declare-fun _Glue2_exp_exp (Addr Int Addr Addr Heap Addr HeapObject) Bool)
(declare-fun Inv_Heap_exp_exp (Addr Int Addr) Bool)
(declare-fun inv_main_9 (Heap Int Addr Addr Addr) Bool)
(declare-fun inv_main551_5 (Heap Addr) Bool)
(declare-fun _Glue4 (Addr Heap Addr HeapObject) Bool)
(declare-fun _Glue1 (Addr Addr Heap Addr HeapObject) Bool)
(assert (forall ((var0 Addr) (var1 HeapObject) (var2 node) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Int) (var7 Addr)) (or (not (and (and (Inv_Heap_exp_exp var7 var6 var5) (inv_main_4 var4 0 var7 var3)) (and (and (and (= (O_node var2) var1) (= (node var6 var5) var2)) (= (read var4 var7) var1)) (valid var4 var7)))) (_Glue1 var0 var3 var4 var7 var1))))
(assert (forall ((var0 Addr) (var1 HeapObject) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main_4 var4 0 var3 var2) (and (= (read var4 var3) var1) (not (valid var4 var3))))) (_Glue1 var0 var2 var4 var3 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 node) (var3 HeapObject) (var4 Addr) (var5 Heap) (var6 Addr)) (or (not (and (_Glue1 var6 var6 var5 var4 var3) (and (and (and (and (is-O_node var3) (= (getnode var3) var2)) (= (|node::n| var2) var1)) (valid var5 var4)) (= var0 3)))) (Inv_Heap_exp_exp var4 var0 var1))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 node) (var3 Addr) (var4 node) (var5 HeapObject) (var6 Addr) (var7 Heap) (var8 Addr)) (or (not (and (_Glue1 var8 var8 var7 var6 var5) (and (and (and (and (and (is-O_node var5) (= (getnode var5) var4)) (= (|node::n| var4) var3)) (= (node 3 var3) var2)) (= (O_node var2) var1)) (= (write var7 var6 var1) var0)))) (inv_main554_5 var0 var8))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Heap) (var3 Addr) (var4 Addr)) (or (not (and (and (Inv_Heap_exp_exp var4 2 var3) (inv_main554_5 var2 var4)) (and (and (and (= (O_node var1) var0) (= (node 2 var3) var1)) (= (read var2 var4) var0)) (valid var2 var4)))) (inv_main554_5 var2 var3))))
(assert (forall ((var0 Addr) (var1 node) (var2 HeapObject) (var3 Addr) (var4 Heap)) (or (not (and (inv_main554_5 var4 var3) (and (and (and (and (and (is-O_node var2) (= (read var4 var3) var2)) (= (getnode var2) var1)) (= (|node::n| var1) var0)) (= (|node::h| var1) 2)) (not (valid var4 var3))))) (inv_main554_5 var4 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 HeapObject) (var4 node) (var5 Addr) (var6 Int) (var7 Heap) (var8 Addr) (var9 Int) (var10 Addr)) (or (not (and (and (Inv_Heap_exp_exp var10 var9 var8) (inv_main_4 var7 var6 var10 var5)) (and (and (and (and (= (O_node var4) var3) (= (node var9 var8) var4)) (= nullAddr var2)) (= (read var7 var10) var3)) (valid var7 var10)))) (_Glue9_exp_exp var2 var1 var0 var5 var6 var7 var10 var3))))
(assert (forall ((var0 Addr) (var1 Int) (var2 HeapObject) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Int) (var7 Heap)) (or (not (and (inv_main_4 var7 var6 var5 var4) (and (and (= nullAddr var3) (= (read var7 var5) var2)) (not (valid var7 var5))))) (_Glue9_exp_exp var3 var1 var0 var4 var6 var7 var5 var2))))
(assert (forall ((var0 Int) (var1 Addr) (var2 node) (var3 HeapObject) (var4 Addr) (var5 Heap) (var6 Int) (var7 Addr) (var8 Addr) (var9 Int) (var10 Addr)) (or (not (and (_Glue9_exp_exp var10 var9 var8 var7 var6 var5 var4 var3) (and (and (and (and (is-O_node var3) (= (getnode var3) var2)) (= (|node::n| var2) var1)) (valid var5 var4)) (= var0 1)))) (Inv_Heap_exp_exp var4 var0 var1))))
(assert (forall ((var0 node) (var1 Addr) (var2 AllocResHeap) (var3 Heap) (var4 HeapObject) (var5 node) (var6 Addr) (var7 HeapObject) (var8 node) (var9 HeapObject) (var10 Addr) (var11 Heap) (var12 Int) (var13 Addr) (var14 Addr) (var15 Int) (var16 Addr)) (or (not (and (_Glue9_exp_exp var16 var15 var14 var13 var12 var11 var10 var9) (and (and (and (and (and (and (and (and (and (and (and (= (O_node var8) var7) (= (node 1 var6) var5)) (= (O_node var5) var4)) (= (node var15 var14) var8)) (= (alloc var3 var7) var2)) (= (newAddr var2) var1)) (is-O_node var9)) (= (getnode var9) var0)) (= (|node::n| var0) var6)) (= (write var11 var10 var4) var3)) (not (= var1 var16))) (not (= var12 0))))) (Inv_Heap_exp_exp (newAddr var2) var15 var14))))
(assert (forall ((var0 node) (var1 Addr) (var2 Heap) (var3 AllocResHeap) (var4 Heap) (var5 HeapObject) (var6 node) (var7 Addr) (var8 HeapObject) (var9 node) (var10 HeapObject) (var11 Addr) (var12 Heap) (var13 Int) (var14 Addr) (var15 Addr) (var16 Int) (var17 Addr)) (or (not (and (_Glue9_exp_exp var17 var16 var15 var14 var13 var12 var11 var10) (and (and (and (and (and (and (and (and (and (and (and (and (= (O_node var9) var8) (= (node 1 var7) var6)) (= (O_node var6) var5)) (= (node var16 var15) var9)) (= (alloc var4 var8) var3)) (= (newHeap var3) var2)) (= (newAddr var3) var1)) (not (= var1 var17))) (not (= var13 0))) (is-O_node var10)) (= (getnode var10) var0)) (= (|node::n| var0) var7)) (= (write var12 var11 var5) var4)))) (inv_main_9 var2 var13 var11 var14 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 AllocResHeap) (var3 Heap) (var4 Addr) (var5 Int) (var6 HeapObject) (var7 node)) (or (not (and (and (and (and (and (and (= (O_node var7) var6) (= (node var5 var4) var7)) (= (alloc var3 var6) var2)) (= (newAddr var2) var1)) (not (= var1 var0))) (= nullAddr var0)) (= emptyHeap var3))) (Inv_Heap_exp_exp (newAddr var2) var5 var4))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 AllocResHeap) (var6 Heap) (var7 HeapObject) (var8 node)) (or (not (and (and (and (and (and (and (and (= (O_node var8) var7) (= (alloc var6 var7) var5)) (= (newHeap var5) var4)) (= (newAddr var5) var3)) (not (= var3 var2))) (= nullAddr var2)) (= emptyHeap var6)) (= var1 var3))) (inv_main_4 var4 var0 var1 var3))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Int) (var4 Heap) (var5 Addr) (var6 Int) (var7 Addr)) (not (and (and (Inv_Heap_exp_exp var7 var6 var5) (inv_main_4 var4 var3 var7 var2)) (and (and (and (and (and (= (O_node var1) var0) (= (node var6 var5) var1)) (= (read var4 var7) var0)) (not (= 4 4))) (not (= var3 0))) (valid var4 var7))))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap)) (not (and (inv_main_4 var4 var3 var2 var1) (and (and (and (and (is-O_node var0) (= (read var4 var2) var0)) (not (= 4 4))) (not (= var3 0))) (not (valid var4 var2)))))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Heap) (var3 Addr) (var4 Addr)) (not (and (and (Inv_Heap_exp_exp var4 2 var3) (inv_main554_5 var2 var4)) (and (and (and (and (= (O_node var1) var0) (= (node 2 var3) var1)) (= (read var2 var4) var0)) (not (= 4 4))) (valid var2 var4))))))
(assert (forall ((var0 node) (var1 HeapObject) (var2 Addr) (var3 Heap)) (not (and (inv_main554_5 var3 var2) (and (and (and (and (and (= (read var3 var2) var1) (is-O_node var1)) (= (getnode var1) var0)) (= (|node::h| var0) 2)) (not (= 4 4))) (not (valid var3 var2)))))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Heap) (var3 Addr) (var4 Int) (var5 Addr)) (not (and (and (Inv_Heap_exp_exp var5 var4 var3) (inv_main551_5 var2 var5)) (and (and (and (and (= (O_node var1) var0) (= (node var4 var3) var1)) (not (= 4 4))) (= (read var2 var5) var0)) (valid var2 var5))))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Heap)) (not (and (inv_main551_5 var2 var1) (and (and (not (is-O_node var0)) (= (read var2 var1) var0)) (not (valid var2 var1)))))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Heap) (var3 Addr) (var4 Int) (var5 Addr)) (not (and (and (Inv_Heap_exp_exp var5 var4 var3) (inv_main554_5 var2 var5)) (and (and (and (and (= (O_node var1) var0) (= (node var4 var3) var1)) (not (= 4 4))) (= (read var2 var5) var0)) (valid var2 var5))))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Heap)) (not (and (inv_main554_5 var2 var1) (and (and (not (is-O_node var0)) (= (read var2 var1) var0)) (not (valid var2 var1)))))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Int) (var4 Heap) (var5 Addr) (var6 Int) (var7 Addr)) (not (and (and (Inv_Heap_exp_exp var7 var6 var5) (inv_main_4 var4 var3 var7 var2)) (and (and (and (and (= (O_node var1) var0) (= (node var6 var5) var1)) (= (read var4 var7) var0)) (not (= 4 4))) (valid var4 var7))))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap)) (not (and (inv_main_4 var4 var3 var2 var1) (and (and (and (is-O_node var0) (= (read var4 var2) var0)) (not (= 4 4))) (not (valid var4 var2)))))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap) (var6 Addr) (var7 Int) (var8 Addr)) (or (not (and (and (Inv_Heap_exp_exp var8 var7 var6) (inv_main_9 var5 var4 var8 var3 var2)) (and (and (and (= (O_node var1) var0) (= (node var7 var6) var1)) (= (read var5 var8) var0)) (valid var5 var8)))) (_Glue4 var8 var5 var2 var0))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap)) (or (not (and (inv_main_9 var5 var4 var3 var2 var1) (and (= (read var5 var3) var0) (not (valid var5 var3))))) (_Glue4 var3 var5 var1 var0))))
(assert (forall ((var0 Int) (var1 node) (var2 HeapObject) (var3 Addr) (var4 Heap) (var5 Addr)) (or (not (and (_Glue4 var5 var4 var3 var2) (and (and (and (is-O_node var2) (= (getnode var2) var1)) (= (|node::h| var1) var0)) (valid var4 var5)))) (Inv_Heap_exp_exp var5 var0 var3))))
(assert (forall ((var0 node) (var1 Heap) (var2 HeapObject) (var3 node) (var4 Int) (var5 HeapObject) (var6 node) (var7 HeapObject) (var8 Addr) (var9 Heap) (var10 Addr) (var11 Int) (var12 Addr)) (not (and (and (Inv_Heap_exp_exp var12 var11 var10) (_Glue4 var12 var9 var8 var7)) (and (and (and (and (and (and (and (and (and (and (= (O_node var6) var5) (= (node var4 var8) var3)) (= (O_node var3) var2)) (= (node var11 var10) var6)) (= (read var1 var12) var5)) (not (= 4 4))) (valid var1 var12)) (is-O_node var7)) (= (getnode var7) var0)) (= (|node::h| var0) var4)) (= (write var9 var12 var2) var1))))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Int) (var3 node) (var4 HeapObject) (var5 Heap) (var6 HeapObject) (var7 Addr) (var8 Heap) (var9 Addr)) (not (and (_Glue4 var9 var8 var7 var6) (and (and (and (and (and (and (and (and (= (read var5 var9) var4) (not (is-O_node var4))) (not (valid var5 var9))) (is-O_node var6)) (= (getnode var6) var3)) (= (|node::h| var3) var2)) (= (node var2 var7) var1)) (= (O_node var1) var0)) (= (write var8 var9 var0) var5))))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Int) (var4 Heap) (var5 Addr) (var6 Int) (var7 Addr)) (not (and (and (Inv_Heap_exp_exp var7 var6 var5) (inv_main_4 var4 var3 var7 var2)) (and (and (and (and (= (O_node var1) var0) (= (node var6 var5) var1)) (not (= 4 4))) (= (read var4 var7) var0)) (valid var4 var7))))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap)) (not (and (inv_main_4 var4 var3 var2 var1) (and (and (not (is-O_node var0)) (= (read var4 var2) var0)) (not (valid var4 var2)))))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Heap) (var3 Addr) (var4 Addr)) (or (not (and (and (Inv_Heap_exp_exp var4 1 var3) (inv_main551_5 var2 var4)) (and (and (and (= (O_node var1) var0) (= (node 1 var3) var1)) (= (read var2 var4) var0)) (valid var2 var4)))) (inv_main551_5 var2 var3))))
(assert (forall ((var0 Addr) (var1 node) (var2 HeapObject) (var3 Addr) (var4 Heap)) (or (not (and (inv_main551_5 var4 var3) (and (and (and (and (and (is-O_node var2) (= (read var4 var3) var2)) (= (getnode var2) var1)) (= (|node::n| var1) var0)) (= (|node::h| var1) 1)) (not (valid var4 var3))))) (inv_main551_5 var4 var0))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Heap) (var3 Addr) (var4 Int) (var5 Addr)) (or (not (and (and (Inv_Heap_exp_exp var5 var4 var3) (inv_main554_5 var2 var5)) (and (and (and (and (= (O_node var1) var0) (= (node var4 var3) var1)) (not (= var4 2))) (= (read var2 var5) var0)) (valid var2 var5)))) (inv_main_16 var2 var5))))
(assert (forall ((var0 node) (var1 Int) (var2 HeapObject) (var3 Addr) (var4 Heap)) (or (not (and (inv_main554_5 var4 var3) (and (and (and (and (and (is-O_node var2) (not (= var1 2))) (= (read var4 var3) var2)) (= (getnode var2) var0)) (= (|node::h| var0) var1)) (not (valid var4 var3))))) (inv_main_16 var4 var3))))
(assert (forall ((var0 Addr) (var1 HeapObject) (var2 node) (var3 Addr) (var4 Int) (var5 Heap) (var6 Addr) (var7 Int) (var8 Addr)) (or (not (and (and (Inv_Heap_exp_exp var8 var7 var6) (inv_main_4 var5 var4 var8 var3)) (and (and (and (= (O_node var2) var1) (= (node var7 var6) var2)) (= (read var5 var8) var1)) (valid var5 var8)))) (_Glue6 var0 var3 var4 var5 var8 var1))))
(assert (forall ((var0 Addr) (var1 HeapObject) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap)) (or (not (and (inv_main_4 var5 var4 var3 var2) (and (= (read var5 var3) var1) (not (valid var5 var3))))) (_Glue6 var0 var2 var4 var5 var3 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 node) (var3 HeapObject) (var4 Addr) (var5 Heap) (var6 Int) (var7 Addr)) (or (not (and (_Glue6 var7 var7 var6 var5 var4 var3) (and (and (and (and (and (is-O_node var3) (= (getnode var3) var2)) (= (|node::n| var2) var1)) (not (= var6 0))) (valid var5 var4)) (= var0 3)))) (Inv_Heap_exp_exp var4 var0 var1))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 node) (var3 Addr) (var4 node) (var5 HeapObject) (var6 Addr) (var7 Heap) (var8 Int) (var9 Addr)) (or (not (and (_Glue6 var9 var9 var8 var7 var6 var5) (and (and (and (and (and (and (is-O_node var5) (= (getnode var5) var4)) (= (|node::n| var4) var3)) (= (node 3 var3) var2)) (= (O_node var2) var1)) (= (write var7 var6 var1) var0)) (not (= var8 0))))) (inv_main551_5 var0 var9))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Int) (var6 Addr)) (not (and (and (Inv_Heap_exp_exp var6 var5 var4) (inv_main_4 var3 0 var6 var2)) (and (and (and (and (= (O_node var1) var0) (= (node var5 var4) var1)) (= (read var3 var6) var0)) (not (= 4 4))) (valid var3 var6))))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_4 var3 0 var2 var1) (and (and (and (is-O_node var0) (= (read var3 var2) var0)) (not (= 4 4))) (not (valid var3 var2)))))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Heap) (var3 Addr) (var4 Int) (var5 Addr)) (or (not (and (and (Inv_Heap_exp_exp var5 var4 var3) (inv_main551_5 var2 var5)) (and (and (and (and (= (O_node var1) var0) (= (node var4 var3) var1)) (not (= var4 1))) (= (read var2 var5) var0)) (valid var2 var5)))) (inv_main_16 var2 var5))))
(assert (forall ((var0 node) (var1 Int) (var2 HeapObject) (var3 Addr) (var4 Heap)) (or (not (and (inv_main551_5 var4 var3) (and (and (and (and (and (is-O_node var2) (not (= var1 1))) (= (read var4 var3) var2)) (= (getnode var2) var0)) (= (|node::h| var0) var1)) (not (valid var4 var3))))) (inv_main_16 var4 var3))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap) (var6 Addr) (var7 Int) (var8 Addr)) (or (not (and (and (Inv_Heap_exp_exp var8 var7 var6) (inv_main_9 var5 var4 var8 var3 var2)) (and (and (and (= (O_node var1) var0) (= (node var7 var6) var1)) (= (read var5 var8) var0)) (valid var5 var8)))) (_Glue7 var3 var4 var8 var5 var2 var0))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap)) (or (not (and (inv_main_9 var5 var4 var3 var2 var1) (and (= (read var5 var3) var0) (not (valid var5 var3))))) (_Glue7 var2 var4 var3 var5 var1 var0))))
(assert (forall ((var0 Int) (var1 node) (var2 HeapObject) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Int) (var7 Addr)) (or (not (and (_Glue7 var7 var6 var5 var4 var3 var2) (and (and (and (is-O_node var2) (= (getnode var2) var1)) (= (|node::h| var1) var0)) (valid var4 var5)))) (Inv_Heap_exp_exp var5 var0 var3))))
(assert (forall ((var0 node) (var1 Heap) (var2 HeapObject) (var3 node) (var4 Int) (var5 HeapObject) (var6 node) (var7 HeapObject) (var8 Addr) (var9 Heap) (var10 Int) (var11 Addr) (var12 Addr) (var13 Int) (var14 Addr)) (or (not (and (and (Inv_Heap_exp_exp var14 var13 var12) (_Glue7 var11 var10 var14 var9 var8 var7)) (and (and (and (and (and (and (and (and (and (= (O_node var6) var5) (= (node var4 var8) var3)) (= (O_node var3) var2)) (= (node var13 var12) var6)) (= (read var1 var14) var5)) (valid var1 var14)) (is-O_node var7)) (= (getnode var7) var0)) (= (|node::h| var0) var4)) (= (write var9 var14 var2) var1)))) (inv_main_4 var1 var10 var12 var11))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Int) (var3 node) (var4 Addr) (var5 node) (var6 HeapObject) (var7 Heap) (var8 HeapObject) (var9 Addr) (var10 Heap) (var11 Addr) (var12 Int) (var13 Addr)) (or (not (and (_Glue7 var13 var12 var11 var10 var9 var8) (and (and (and (and (and (and (and (and (and (and (= (read var7 var11) var6) (is-O_node var6)) (= (getnode var6) var5)) (= (|node::n| var5) var4)) (not (valid var7 var11))) (is-O_node var8)) (= (getnode var8) var3)) (= (|node::h| var3) var2)) (= (node var2 var9) var1)) (= (O_node var1) var0)) (= (write var10 var11 var0) var7)))) (inv_main_4 var7 var12 var4 var13))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Int) (var6 Addr)) (not (and (and (Inv_Heap_exp_exp var6 var5 var4) (inv_main_4 var3 0 var6 var2)) (and (and (and (and (= (O_node var1) var0) (= (node var5 var4) var1)) (not (= 4 4))) (= (read var3 var6) var0)) (valid var3 var6))))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_4 var3 0 var2 var1) (and (and (not (is-O_node var0)) (= (read var3 var2) var0)) (not (valid var3 var2)))))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Int) (var4 Heap) (var5 Addr) (var6 Int) (var7 Addr)) (not (and (and (Inv_Heap_exp_exp var7 var6 var5) (inv_main_4 var4 var3 var7 var2)) (and (and (and (and (and (= (O_node var1) var0) (= (node var6 var5) var1)) (not (= 4 4))) (= (read var4 var7) var0)) (not (= var3 0))) (valid var4 var7))))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap)) (not (and (inv_main_4 var4 var3 var2 var1) (and (and (and (not (is-O_node var0)) (= (read var4 var2) var0)) (not (= var3 0))) (not (valid var4 var2)))))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap) (var6 Addr) (var7 Int) (var8 Addr)) (not (and (and (Inv_Heap_exp_exp var8 var7 var6) (inv_main_9 var5 var4 var8 var3 var2)) (and (and (and (and (= (O_node var1) var0) (= (node var7 var6) var1)) (= (read var5 var8) var0)) (not (= 4 4))) (valid var5 var8))))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap)) (not (and (inv_main_9 var5 var4 var3 var2 var1) (and (and (and (is-O_node var0) (= (read var5 var3) var0)) (not (= 4 4))) (not (valid var5 var3)))))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Heap) (var3 Addr) (var4 Addr)) (not (and (and (Inv_Heap_exp_exp var4 1 var3) (inv_main551_5 var2 var4)) (and (and (and (and (= (O_node var1) var0) (= (node 1 var3) var1)) (= (read var2 var4) var0)) (not (= 4 4))) (valid var2 var4))))))
(assert (forall ((var0 node) (var1 HeapObject) (var2 Addr) (var3 Heap)) (not (and (inv_main551_5 var3 var2) (and (and (and (and (and (= (read var3 var2) var1) (is-O_node var1)) (= (getnode var1) var0)) (= (|node::h| var0) 1)) (not (= 4 4))) (not (valid var3 var2)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 HeapObject) (var4 node) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Int) (var9 Addr)) (or (not (and (and (Inv_Heap_exp_exp var9 var8 var7) (inv_main_4 var6 0 var9 var5)) (and (and (and (and (= (O_node var4) var3) (= (node var8 var7) var4)) (= nullAddr var2)) (= (read var6 var9) var3)) (valid var6 var9)))) (_Glue2_exp_exp var2 var1 var0 var5 var6 var9 var3))))
(assert (forall ((var0 Addr) (var1 Int) (var2 HeapObject) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main_4 var6 0 var5 var4) (and (and (= nullAddr var3) (= (read var6 var5) var2)) (not (valid var6 var5))))) (_Glue2_exp_exp var3 var1 var0 var4 var6 var5 var2))))
(assert (forall ((var0 Int) (var1 Addr) (var2 node) (var3 HeapObject) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Int) (var9 Addr)) (or (not (and (_Glue2_exp_exp var9 var8 var7 var6 var5 var4 var3) (and (and (and (and (is-O_node var3) (= (getnode var3) var2)) (= (|node::n| var2) var1)) (valid var5 var4)) (= var0 2)))) (Inv_Heap_exp_exp var4 var0 var1))))
(assert (forall ((var0 node) (var1 Addr) (var2 AllocResHeap) (var3 Heap) (var4 HeapObject) (var5 node) (var6 Addr) (var7 HeapObject) (var8 node) (var9 HeapObject) (var10 Addr) (var11 Heap) (var12 Addr) (var13 Addr) (var14 Int) (var15 Addr)) (or (not (and (_Glue2_exp_exp var15 var14 var13 var12 var11 var10 var9) (and (and (and (and (and (and (and (and (and (and (= (O_node var8) var7) (= (node 2 var6) var5)) (= (O_node var5) var4)) (= (node var14 var13) var8)) (= (alloc var3 var7) var2)) (= (newAddr var2) var1)) (is-O_node var9)) (= (getnode var9) var0)) (= (|node::n| var0) var6)) (= (write var11 var10 var4) var3)) (not (= var1 var15))))) (Inv_Heap_exp_exp (newAddr var2) var14 var13))))
(assert (forall ((var0 Int) (var1 node) (var2 Addr) (var3 Heap) (var4 AllocResHeap) (var5 Heap) (var6 HeapObject) (var7 node) (var8 Addr) (var9 HeapObject) (var10 node) (var11 HeapObject) (var12 Addr) (var13 Heap) (var14 Addr) (var15 Addr) (var16 Int) (var17 Addr)) (or (not (and (_Glue2_exp_exp var17 var16 var15 var14 var13 var12 var11) (and (and (and (and (and (and (and (and (and (and (and (and (= (O_node var10) var9) (= (node 2 var8) var7)) (= (O_node var7) var6)) (= (node var16 var15) var10)) (= (alloc var5 var9) var4)) (= (newHeap var4) var3)) (= (newAddr var4) var2)) (not (= var2 var17))) (is-O_node var11)) (= (getnode var11) var1)) (= (|node::n| var1) var8)) (= (write var13 var12 var6) var5)) (= var0 0)))) (inv_main_9 var3 var0 var12 var14 var2))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Heap) (var3 Addr) (var4 Int) (var5 Addr)) (not (and (and (Inv_Heap_exp_exp var5 var4 var3) (inv_main_16 var2 var5)) (and (and (and (and (= (O_node var1) var0) (= (node var4 var3) var1)) (not (= 4 4))) (= (read var2 var5) var0)) (valid var2 var5))))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Heap)) (not (and (inv_main_16 var2 var1) (and (and (not (is-O_node var0)) (= (read var2 var1) var0)) (not (valid var2 var1)))))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap) (var6 Addr) (var7 Int) (var8 Addr)) (not (and (and (Inv_Heap_exp_exp var8 var7 var6) (inv_main_9 var5 var4 var8 var3 var2)) (and (and (and (and (= (O_node var1) var0) (= (node var7 var6) var1)) (not (= 4 4))) (= (read var5 var8) var0)) (valid var5 var8))))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap)) (not (and (inv_main_9 var5 var4 var3 var2 var1) (and (and (not (is-O_node var0)) (= (read var5 var3) var0)) (not (valid var5 var3)))))))
(check-sat)
