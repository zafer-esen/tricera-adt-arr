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
(declare-fun _Glue0 (Addr Heap Addr Addr HeapObject) Bool)
(declare-fun _Glue9_exp_exp (Addr Int Addr Addr Heap Addr HeapObject) Bool)
(declare-fun inv_main_38 (Heap Addr) Bool)
(declare-fun inv_main_9 (Heap Int Addr Addr Addr) Bool)
(declare-fun _Glue13 (Int Addr Heap Addr Addr HeapObject) Bool)
(declare-fun Inv_Heap_exp_exp (Addr Int Addr) Bool)
(declare-fun inv_main_32 (Heap Addr Addr) Bool)
(declare-fun _Glue11 (Heap Addr Addr HeapObject) Bool)
(declare-fun _Glue4 (Addr Heap Addr Addr HeapObject) Bool)
(declare-fun inv_main540_3 (Heap Int Addr Addr) Bool)
(declare-fun _Glue2 (Heap Addr Addr HeapObject) Bool)
(declare-fun _Glue6_exp_exp (Addr Int Addr Addr Int Heap Addr HeapObject) Bool)
(declare-fun _Glue1 (Addr Int Addr Heap Addr HeapObject) Bool)
(declare-fun inv_main_21 (Heap Int Addr Addr Addr) Bool)
(assert (forall ((var0 Addr) (var1 HeapObject) (var2 node) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr)) (or (not (and (and (Inv_Heap_exp_exp var6 1 var5) (inv_main_32 var4 var3 var6)) (and (and (and (and (and (= (O_node var2) var1) (= (node 1 var5) var2)) (= (read var4 var6) var1)) (= nullAddr var0)) (not (= var5 var0))) (valid var4 var6)))) (inv_main_32 var4 var3 var5))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 node) (var3 HeapObject) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main_32 var6 var5 var4) (and (and (and (and (and (and (and (is-O_node var3) (= (read var6 var4) var3)) (= (getnode var3) var2)) (= (|node::n| var2) var1)) (= nullAddr var0)) (= (|node::h| var2) 1)) (not (= var1 var0))) (not (valid var6 var4))))) (inv_main_32 var6 var5 var1))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap) (var6 Addr) (var7 Int) (var8 Addr)) (not (and (and (Inv_Heap_exp_exp var8 var7 var6) (inv_main_9 var5 var4 var3 var2 var8)) (and (and (and (and (= (O_node var1) var0) (= (node var7 var6) var1)) (not (= 4 4))) (= (read var5 var8) var0)) (valid var5 var8))))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap)) (not (and (inv_main_9 var5 var4 var3 var2 var1) (and (and (not (is-O_node var0)) (= (read var5 var1) var0)) (not (valid var5 var1)))))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Heap) (var3 Addr) (var4 Int) (var5 Addr)) (not (and (and (Inv_Heap_exp_exp var5 var4 var3) (inv_main_38 var2 var5)) (and (and (and (and (= (O_node var1) var0) (= (node var4 var3) var1)) (not (= 4 4))) (= (read var2 var5) var0)) (valid var2 var5))))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Heap)) (not (and (inv_main_38 var2 var1) (and (and (not (is-O_node var0)) (= (read var2 var1) var0)) (not (valid var2 var1)))))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Int) (var4 Heap) (var5 Addr) (var6 Int) (var7 Addr)) (or (not (and (and (Inv_Heap_exp_exp var7 var6 var5) (inv_main540_3 var4 var3 var2 var7)) (and (and (and (= (O_node var1) var0) (= (node var6 var5) var1)) (= (read var4 var7) var0)) (valid var4 var7)))) (_Glue11 var4 var2 var7 var0))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap)) (or (not (and (inv_main540_3 var4 var3 var2 var1) (and (= (read var4 var1) var0) (not (valid var4 var1))))) (_Glue11 var4 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 node) (var3 HeapObject) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (_Glue11 var6 var5 var4 var3) (and (and (and (and (is-O_node var3) (= (getnode var3) var2)) (= (|node::n| var2) var1)) (valid var6 var4)) (= var0 3)))) (Inv_Heap_exp_exp var4 var0 var1))))
(assert (forall ((var0 node) (var1 Heap) (var2 HeapObject) (var3 node) (var4 Addr) (var5 HeapObject) (var6 node) (var7 HeapObject) (var8 Addr) (var9 Heap) (var10 Addr) (var11 Int) (var12 Addr)) (not (and (and (Inv_Heap_exp_exp var12 var11 var10) (_Glue11 var9 var12 var8 var7)) (and (and (and (and (and (and (and (and (and (and (= (O_node var6) var5) (= (node 3 var4) var3)) (= (O_node var3) var2)) (= (node var11 var10) var6)) (= (read var1 var12) var5)) (not (= 4 4))) (valid var1 var12)) (is-O_node var7)) (= (getnode var7) var0)) (= (|node::n| var0) var4)) (= (write var9 var8 var2) var1))))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 node) (var4 HeapObject) (var5 Heap) (var6 HeapObject) (var7 Addr) (var8 Addr) (var9 Heap)) (not (and (_Glue11 var9 var8 var7 var6) (and (and (and (and (and (and (and (and (= (read var5 var8) var4) (not (is-O_node var4))) (not (valid var5 var8))) (is-O_node var6)) (= (getnode var6) var3)) (= (|node::n| var3) var2)) (= (node 3 var2) var1)) (= (O_node var1) var0)) (= (write var9 var7 var0) var5))))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Int) (var4 Heap) (var5 Addr) (var6 Int) (var7 Addr)) (not (and (and (Inv_Heap_exp_exp var7 var6 var5) (inv_main540_3 var4 var3 var2 var7)) (and (and (and (and (= (O_node var1) var0) (= (node var6 var5) var1)) (not (= 4 4))) (= (read var4 var7) var0)) (valid var4 var7))))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap)) (not (and (inv_main540_3 var4 var3 var2 var1) (and (and (not (is-O_node var0)) (= (read var4 var1) var0)) (not (valid var4 var1)))))))
(assert (forall ((var0 Addr) (var1 HeapObject) (var2 node) (var3 Addr) (var4 Int) (var5 Heap) (var6 Addr) (var7 Int) (var8 Addr)) (or (not (and (and (Inv_Heap_exp_exp var8 var7 var6) (inv_main540_3 var5 var4 var3 var8)) (and (and (and (and (= (O_node var2) var1) (= (node var7 var6) var2)) (= nullAddr var0)) (= (read var5 var8) var1)) (valid var5 var8)))) (_Glue4 var0 var5 var3 var8 var1))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap)) (or (not (and (inv_main540_3 var5 var4 var3 var2) (and (and (= nullAddr var1) (= (read var5 var2) var0)) (not (valid var5 var2))))) (_Glue4 var1 var5 var3 var2 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 node) (var3 HeapObject) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Addr)) (or (not (and (_Glue4 var7 var6 var5 var4 var3) (and (and (and (and (is-O_node var3) (= (getnode var3) var2)) (= (|node::n| var2) var1)) (valid var6 var4)) (= var0 3)))) (Inv_Heap_exp_exp var4 var0 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 node) (var3 Heap) (var4 HeapObject) (var5 node) (var6 Addr) (var7 HeapObject) (var8 node) (var9 HeapObject) (var10 Addr) (var11 Heap) (var12 Addr) (var13 Addr) (var14 Int) (var15 Addr)) (or (not (and (and (Inv_Heap_exp_exp var15 var14 var13) (_Glue4 var12 var11 var15 var10 var9)) (and (and (and (and (and (and (and (and (and (and (and (and (= (O_node var8) var7) (= (node 3 var6) var5)) (= (O_node var5) var4)) (= (node var14 var13) var8)) (= (read var3 var15) var7)) (not (= var14 3))) (valid var3 var15)) (is-O_node var9)) (= (getnode var9) var2)) (= (|node::n| var2) var6)) (= (write var11 var10 var4) var3)) (= var1 var12)) (= var0 1)))) (inv_main_21 var3 var0 var1 var12 var15))))
(assert (forall ((var0 Int) (var1 Addr) (var2 HeapObject) (var3 node) (var4 Addr) (var5 node) (var6 Int) (var7 node) (var8 HeapObject) (var9 Heap) (var10 HeapObject) (var11 Addr) (var12 Addr) (var13 Heap) (var14 Addr)) (or (not (and (_Glue4 var14 var13 var12 var11 var10) (and (and (and (and (and (and (and (and (and (and (and (and (and (= (read var9 var12) var8) (is-O_node var8)) (= (getnode var8) var7)) (= (|node::h| var7) var6)) (not (= var6 3))) (not (valid var9 var12))) (is-O_node var10)) (= (getnode var10) var5)) (= (|node::n| var5) var4)) (= (node 3 var4) var3)) (= (O_node var3) var2)) (= (write var13 var11 var2) var9)) (= var1 var14)) (= var0 1)))) (inv_main_21 var9 var0 var1 var14 var12))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap) (var6 Addr) (var7 Int) (var8 Addr)) (or (not (and (and (Inv_Heap_exp_exp var8 var7 var6) (inv_main_21 var5 var4 var3 var2 var8)) (and (and (and (= (O_node var1) var0) (= (node var7 var6) var1)) (= (read var5 var8) var0)) (valid var5 var8)))) (_Glue1 var2 var4 var3 var5 var8 var0))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap)) (or (not (and (inv_main_21 var5 var4 var3 var2 var1) (and (= (read var5 var1) var0) (not (valid var5 var1))))) (_Glue1 var2 var4 var3 var5 var1 var0))))
(assert (forall ((var0 Int) (var1 node) (var2 HeapObject) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Int) (var7 Addr)) (or (not (and (_Glue1 var7 var6 var5 var4 var3 var2) (and (and (and (and (and (is-O_node var2) (= (getnode var2) var1)) (= (|node::h| var1) var0)) (not (= var0 3))) (not (= var6 0))) (valid var4 var3)))) (Inv_Heap_exp_exp var3 var0 var5))))
(assert (forall ((var0 Int) (var1 Heap) (var2 HeapObject) (var3 node) (var4 Int) (var5 Addr) (var6 node) (var7 HeapObject) (var8 Addr) (var9 Heap) (var10 Addr) (var11 Int) (var12 Addr)) (or (not (and (_Glue1 var12 var11 var10 var9 var8 var7) (and (and (and (and (and (and (and (and (and (is-O_node var7) (= (getnode var7) var6)) (= (|node::n| var6) var5)) (= (|node::h| var6) var4)) (not (= var4 3))) (= (node var4 var10) var3)) (= (O_node var3) var2)) (= (write var9 var8 var2) var1)) (not (= var11 0))) (= var0 0)))) (inv_main_21 var1 var0 var8 var12 var5))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Heap) (var3 Addr) (var4 Addr)) (not (and (and (Inv_Heap_exp_exp var4 2 var3) (inv_main_38 var2 var4)) (and (and (and (and (= (O_node var1) var0) (= (node 2 var3) var1)) (= (read var2 var4) var0)) (not (= 4 4))) (valid var2 var4))))))
(assert (forall ((var0 node) (var1 HeapObject) (var2 Addr) (var3 Heap)) (not (and (inv_main_38 var3 var2) (and (and (and (and (and (= (read var3 var2) var1) (is-O_node var1)) (= (getnode var1) var0)) (= (|node::h| var0) 2)) (not (= 4 4))) (not (valid var3 var2)))))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap) (var6 Addr) (var7 Int) (var8 Addr)) (not (and (and (Inv_Heap_exp_exp var8 var7 var6) (inv_main_21 var5 var4 var3 var2 var8)) (and (and (and (and (and (and (= (O_node var1) var0) (= (node var7 var6) var1)) (= (read var5 var8) var0)) (not (= 4 4))) (not (= var4 0))) (not (= var7 3))) (valid var5 var8))))))
(assert (forall ((var0 Int) (var1 node) (var2 HeapObject) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Int) (var7 Heap)) (not (and (inv_main_21 var7 var6 var5 var4 var3) (and (and (and (and (and (and (and (= (read var7 var3) var2) (is-O_node var2)) (= (getnode var2) var1)) (= (|node::h| var1) var0)) (not (= 4 4))) (not (= var6 0))) (not (= var0 3))) (not (valid var7 var3)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 AllocResHeap) (var3 Heap) (var4 Addr) (var5 Int) (var6 HeapObject) (var7 node)) (or (not (and (and (and (and (and (and (= (O_node var7) var6) (= (node var5 var4) var7)) (= (alloc var3 var6) var2)) (= (newAddr var2) var1)) (not (= var1 var0))) (= nullAddr var0)) (= emptyHeap var3))) (Inv_Heap_exp_exp (newAddr var2) var5 var4))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 AllocResHeap) (var6 Heap) (var7 HeapObject) (var8 node)) (or (not (and (and (and (and (and (and (and (and (= (O_node var8) var7) (= (alloc var6 var7) var5)) (= (newHeap var5) var4)) (= (newAddr var5) var3)) (not (= var3 var2))) (= nullAddr var2)) (= emptyHeap var6)) (= var1 var3)) (= var0 1))) (inv_main540_3 var4 var0 var1 var3))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Int) (var7 Addr)) (not (and (and (Inv_Heap_exp_exp var7 var6 var5) (inv_main_21 var4 0 var3 var2 var7)) (and (and (and (and (and (= (O_node var1) var0) (= (node var6 var5) var1)) (= (read var4 var7) var0)) (not (= 4 4))) (not (= var6 3))) (valid var4 var7))))))
(assert (forall ((var0 Int) (var1 node) (var2 HeapObject) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap)) (not (and (inv_main_21 var6 0 var5 var4 var3) (and (and (and (and (and (and (is-O_node var2) (= (read var6 var3) var2)) (= (getnode var2) var1)) (= (|node::h| var1) var0)) (not (= 4 4))) (not (= var0 3))) (not (valid var6 var3)))))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Int) (var7 Addr)) (not (and (and (Inv_Heap_exp_exp var7 var6 var5) (inv_main_21 var4 0 var3 var2 var7)) (and (and (and (and (and (= (O_node var1) var0) (= (node var6 var5) var1)) (= (read var4 var7) var0)) (not (= 4 4))) (not (= var6 3))) (valid var4 var7))))))
(assert (forall ((var0 Int) (var1 node) (var2 HeapObject) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap)) (not (and (inv_main_21 var6 0 var5 var4 var3) (and (and (and (and (and (and (= (read var6 var3) var2) (is-O_node var2)) (= (getnode var2) var1)) (= (|node::h| var1) var0)) (not (= 4 4))) (not (= var0 3))) (not (valid var6 var3)))))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr)) (or (not (and (and (Inv_Heap_exp_exp var5 1 var4) (inv_main_32 var3 var2 var5)) (and (and (and (and (and (= (O_node var1) var0) (= (node 1 var4) var1)) (= (read var3 var5) var0)) (= nullAddr var4)) (not (= var2 var4))) (valid var3 var5)))) (inv_main_38 var3 var2))))
(assert (forall ((var0 Addr) (var1 node) (var2 HeapObject) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main_32 var5 var4 var3) (and (and (and (and (and (and (and (is-O_node var2) (= (read var5 var3) var2)) (= (getnode var2) var1)) (= (|node::n| var1) var0)) (= nullAddr var0)) (= (|node::h| var1) 1)) (not (= var4 var0))) (not (valid var5 var3))))) (inv_main_38 var5 var4))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Int) (var6 Addr)) (not (and (and (Inv_Heap_exp_exp var6 var5 var4) (inv_main_32 var3 var2 var6)) (and (and (and (and (= (O_node var1) var0) (= (node var5 var4) var1)) (not (= 4 4))) (= (read var3 var6) var0)) (valid var3 var6))))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_32 var3 var2 var1) (and (and (not (is-O_node var0)) (= (read var3 var1) var0)) (not (valid var3 var1)))))))
(assert (forall ((var0 Addr) (var1 HeapObject) (var2 node) (var3 Heap) (var4 Addr) (var5 Addr)) (or (not (and (and (Inv_Heap_exp_exp var5 2 var4) (inv_main_38 var3 var5)) (and (and (and (and (and (= (O_node var2) var1) (= (node 2 var4) var2)) (= (read var3 var5) var1)) (= nullAddr var0)) (not (= var4 var0))) (valid var3 var5)))) (inv_main_38 var3 var4))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 node) (var3 HeapObject) (var4 Addr) (var5 Heap)) (or (not (and (inv_main_38 var5 var4) (and (and (and (and (and (and (and (is-O_node var3) (= (read var5 var4) var3)) (= (getnode var3) var2)) (= (|node::n| var2) var1)) (= nullAddr var0)) (= (|node::h| var2) 2)) (not (= var1 var0))) (not (valid var5 var4))))) (inv_main_38 var5 var1))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Int) (var6 Addr)) (not (and (and (Inv_Heap_exp_exp var6 var5 var4) (inv_main540_3 var3 0 var2 var6)) (and (and (and (and (= (O_node var1) var0) (= (node var5 var4) var1)) (not (= 4 4))) (= (read var3 var6) var0)) (valid var3 var6))))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main540_3 var3 0 var2 var1) (and (and (not (is-O_node var0)) (= (read var3 var1) var0)) (not (valid var3 var1)))))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr)) (not (and (and (Inv_Heap_exp_exp var5 1 var4) (inv_main_32 var3 var2 var5)) (and (and (and (and (= (O_node var1) var0) (= (node 1 var4) var1)) (= (read var3 var5) var0)) (not (= 4 4))) (valid var3 var5))))))
(assert (forall ((var0 node) (var1 HeapObject) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main_32 var4 var3 var2) (and (and (and (and (and (= (read var4 var2) var1) (is-O_node var1)) (= (getnode var1) var0)) (= (|node::h| var0) 1)) (not (= 4 4))) (not (valid var4 var2)))))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Int) (var4 Heap) (var5 Addr) (var6 Int) (var7 Addr)) (not (and (and (Inv_Heap_exp_exp var7 var6 var5) (inv_main540_3 var4 var3 var2 var7)) (and (and (and (and (= (O_node var1) var0) (= (node var6 var5) var1)) (= (read var4 var7) var0)) (not (= 4 4))) (valid var4 var7))))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap)) (not (and (inv_main540_3 var4 var3 var2 var1) (and (and (and (is-O_node var0) (= (read var4 var1) var0)) (not (= 4 4))) (not (valid var4 var1)))))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap) (var6 Addr) (var7 Int) (var8 Addr)) (not (and (and (Inv_Heap_exp_exp var8 var7 var6) (inv_main_21 var5 var4 var3 var2 var8)) (and (and (and (and (= (O_node var1) var0) (= (node var7 var6) var1)) (not (= 4 4))) (= (read var5 var8) var0)) (valid var5 var8))))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap)) (not (and (inv_main_21 var5 var4 var3 var2 var1) (and (and (not (is-O_node var0)) (= (read var5 var1) var0)) (not (valid var5 var1)))))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap) (var6 Addr) (var7 Int) (var8 Addr)) (or (not (and (and (Inv_Heap_exp_exp var8 var7 var6) (inv_main_9 var5 var4 var3 var2 var8)) (and (and (and (= (O_node var1) var0) (= (node var7 var6) var1)) (= (read var5 var8) var0)) (valid var5 var8)))) (_Glue13 var4 var3 var5 var2 var8 var0))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap)) (or (not (and (inv_main_9 var5 var4 var3 var2 var1) (and (= (read var5 var1) var0) (not (valid var5 var1))))) (_Glue13 var4 var3 var5 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 node) (var2 HeapObject) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Int)) (or (not (and (_Glue13 var7 var6 var5 var4 var3 var2) (and (and (and (is-O_node var2) (= (getnode var2) var1)) (= (|node::h| var1) var0)) (valid var5 var3)))) (Inv_Heap_exp_exp var3 var0 var4))))
(assert (forall ((var0 node) (var1 Heap) (var2 HeapObject) (var3 node) (var4 Int) (var5 HeapObject) (var6 node) (var7 HeapObject) (var8 Addr) (var9 Heap) (var10 Addr) (var11 Int) (var12 Addr) (var13 Int) (var14 Addr)) (or (not (and (and (Inv_Heap_exp_exp var14 var13 var12) (_Glue13 var11 var10 var9 var8 var14 var7)) (and (and (and (and (and (and (and (and (and (= (O_node var6) var5) (= (node var4 var8) var3)) (= (O_node var3) var2)) (= (node var13 var12) var6)) (= (read var1 var14) var5)) (valid var1 var14)) (is-O_node var7)) (= (getnode var7) var0)) (= (|node::h| var0) var4)) (= (write var9 var14 var2) var1)))) (inv_main540_3 var1 var11 var10 var12))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Int) (var3 node) (var4 Addr) (var5 node) (var6 HeapObject) (var7 Heap) (var8 HeapObject) (var9 Addr) (var10 Addr) (var11 Heap) (var12 Addr) (var13 Int)) (or (not (and (_Glue13 var13 var12 var11 var10 var9 var8) (and (and (and (and (and (and (and (and (and (and (= (read var7 var9) var6) (is-O_node var6)) (= (getnode var6) var5)) (= (|node::n| var5) var4)) (not (valid var7 var9))) (is-O_node var8)) (= (getnode var8) var3)) (= (|node::h| var3) var2)) (= (node var2 var10) var1)) (= (O_node var1) var0)) (= (write var11 var9 var0) var7)))) (inv_main540_3 var7 var13 var12 var4))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap) (var6 Addr) (var7 Int) (var8 Addr)) (or (not (and (and (Inv_Heap_exp_exp var8 var7 var6) (inv_main_9 var5 var4 var3 var2 var8)) (and (and (and (= (O_node var1) var0) (= (node var7 var6) var1)) (= (read var5 var8) var0)) (valid var5 var8)))) (_Glue2 var5 var2 var8 var0))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap)) (or (not (and (inv_main_9 var5 var4 var3 var2 var1) (and (= (read var5 var1) var0) (not (valid var5 var1))))) (_Glue2 var5 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 node) (var2 HeapObject) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (_Glue2 var5 var4 var3 var2) (and (and (and (is-O_node var2) (= (getnode var2) var1)) (= (|node::h| var1) var0)) (valid var5 var3)))) (Inv_Heap_exp_exp var3 var0 var4))))
(assert (forall ((var0 node) (var1 Heap) (var2 HeapObject) (var3 node) (var4 Int) (var5 HeapObject) (var6 node) (var7 HeapObject) (var8 Addr) (var9 Heap) (var10 Addr) (var11 Int) (var12 Addr)) (not (and (and (Inv_Heap_exp_exp var12 var11 var10) (_Glue2 var9 var8 var12 var7)) (and (and (and (and (and (and (and (and (and (and (= (O_node var6) var5) (= (node var4 var8) var3)) (= (O_node var3) var2)) (= (node var11 var10) var6)) (= (read var1 var12) var5)) (not (= 4 4))) (valid var1 var12)) (is-O_node var7)) (= (getnode var7) var0)) (= (|node::h| var0) var4)) (= (write var9 var12 var2) var1))))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Int) (var3 node) (var4 HeapObject) (var5 Heap) (var6 HeapObject) (var7 Addr) (var8 Addr) (var9 Heap)) (not (and (_Glue2 var9 var8 var7 var6) (and (and (and (and (and (and (and (and (= (read var5 var7) var4) (not (is-O_node var4))) (not (valid var5 var7))) (is-O_node var6)) (= (getnode var6) var3)) (= (|node::h| var3) var2)) (= (node var2 var8) var1)) (= (O_node var1) var0)) (= (write var9 var7 var0) var5))))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap) (var6 Addr) (var7 Int) (var8 Addr)) (not (and (and (Inv_Heap_exp_exp var8 var7 var6) (inv_main_9 var5 var4 var3 var2 var8)) (and (and (and (and (= (O_node var1) var0) (= (node var7 var6) var1)) (= (read var5 var8) var0)) (not (= 4 4))) (valid var5 var8))))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap)) (not (and (inv_main_9 var5 var4 var3 var2 var1) (and (and (and (is-O_node var0) (= (read var5 var1) var0)) (not (= 4 4))) (not (valid var5 var1)))))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap) (var6 Addr) (var7 Int) (var8 Addr)) (not (and (and (Inv_Heap_exp_exp var8 var7 var6) (inv_main_21 var5 var4 var3 var2 var8)) (and (and (and (and (and (and (= (O_node var1) var0) (= (node var7 var6) var1)) (= (read var5 var8) var0)) (not (= 4 4))) (not (= var4 0))) (not (= var7 3))) (valid var5 var8))))))
(assert (forall ((var0 Int) (var1 node) (var2 HeapObject) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Int) (var7 Heap)) (not (and (inv_main_21 var7 var6 var5 var4 var3) (and (and (and (and (and (and (and (is-O_node var2) (= (read var7 var3) var2)) (= (getnode var2) var1)) (= (|node::h| var1) var0)) (not (= 4 4))) (not (= var6 0))) (not (= var0 3))) (not (valid var7 var3)))))))
(assert (forall ((var0 Addr) (var1 HeapObject) (var2 node) (var3 Addr) (var4 Addr) (var5 Int) (var6 Heap) (var7 Addr) (var8 Addr)) (or (not (and (and (Inv_Heap_exp_exp var8 3 var7) (inv_main_21 var6 var5 var4 var3 var8)) (and (and (and (and (and (= (O_node var2) var1) (= (node 3 var7) var2)) (not (= var4 var0))) (= (read var6 var8) var1)) (= nullAddr var0)) (valid var6 var8)))) (inv_main_32 var6 var3 var4))))
(assert (forall ((var0 node) (var1 Addr) (var2 HeapObject) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Int) (var7 Heap)) (or (not (and (inv_main_21 var7 var6 var5 var4 var3) (and (and (and (and (and (and (is-O_node var2) (not (= var5 var1))) (= (read var7 var3) var2)) (= (getnode var2) var0)) (= (|node::h| var0) 3)) (= nullAddr var1)) (not (valid var7 var3))))) (inv_main_32 var7 var4 var5))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap) (var6 Addr) (var7 Addr)) (or (not (and (and (Inv_Heap_exp_exp var7 3 var6) (inv_main_21 var5 var4 var3 var2 var7)) (and (and (and (and (and (= (O_node var1) var0) (= (node 3 var6) var1)) (not (= var2 var3))) (= (read var5 var7) var0)) (= nullAddr var3)) (valid var5 var7)))) (inv_main_38 var5 var2))))
(assert (forall ((var0 node) (var1 HeapObject) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Int) (var6 Heap)) (or (not (and (inv_main_21 var6 var5 var4 var3 var2) (and (and (and (and (and (and (is-O_node var1) (not (= var3 var4))) (= (read var6 var2) var1)) (= (getnode var1) var0)) (= (|node::h| var0) 3)) (= nullAddr var4)) (not (valid var6 var2))))) (inv_main_38 var6 var3))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap) (var6 Addr) (var7 Int) (var8 Addr)) (not (and (and (Inv_Heap_exp_exp var8 var7 var6) (inv_main_21 var5 var4 var3 var2 var8)) (and (and (and (and (and (= (O_node var1) var0) (= (node var7 var6) var1)) (= (read var5 var8) var0)) (not (= 4 4))) (not (= var7 3))) (valid var5 var8))))))
(assert (forall ((var0 Int) (var1 node) (var2 HeapObject) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Int) (var7 Heap)) (not (and (inv_main_21 var7 var6 var5 var4 var3) (and (and (and (and (and (and (= (read var7 var3) var2) (is-O_node var2)) (= (getnode var2) var1)) (= (|node::h| var1) var0)) (not (= 4 4))) (not (= var0 3))) (not (valid var7 var3)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 HeapObject) (var4 node) (var5 Addr) (var6 Int) (var7 Heap) (var8 Addr) (var9 Int) (var10 Addr)) (or (not (and (and (Inv_Heap_exp_exp var10 var9 var8) (inv_main540_3 var7 var6 var5 var10)) (and (and (and (and (= (O_node var4) var3) (= (node var9 var8) var4)) (= nullAddr var2)) (= (read var7 var10) var3)) (valid var7 var10)))) (_Glue6_exp_exp var2 var1 var0 var5 var6 var7 var10 var3))))
(assert (forall ((var0 Addr) (var1 Int) (var2 HeapObject) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Int) (var7 Heap)) (or (not (and (inv_main540_3 var7 var6 var5 var4) (and (and (= nullAddr var3) (= (read var7 var4) var2)) (not (valid var7 var4))))) (_Glue6_exp_exp var3 var1 var0 var5 var6 var7 var4 var2))))
(assert (forall ((var0 Int) (var1 Addr) (var2 node) (var3 HeapObject) (var4 Addr) (var5 Heap) (var6 Int) (var7 Addr) (var8 Addr) (var9 Int) (var10 Addr)) (or (not (and (_Glue6_exp_exp var10 var9 var8 var7 var6 var5 var4 var3) (and (and (and (and (is-O_node var3) (= (getnode var3) var2)) (= (|node::n| var2) var1)) (valid var5 var4)) (= var0 1)))) (Inv_Heap_exp_exp var4 var0 var1))))
(assert (forall ((var0 node) (var1 Addr) (var2 AllocResHeap) (var3 Heap) (var4 HeapObject) (var5 node) (var6 Addr) (var7 HeapObject) (var8 node) (var9 HeapObject) (var10 Addr) (var11 Heap) (var12 Int) (var13 Addr) (var14 Addr) (var15 Int) (var16 Addr)) (or (not (and (_Glue6_exp_exp var16 var15 var14 var13 var12 var11 var10 var9) (and (and (and (and (and (and (and (and (and (and (and (= (O_node var8) var7) (= (node 1 var6) var5)) (= (O_node var5) var4)) (= (node var15 var14) var8)) (= (alloc var3 var7) var2)) (= (newAddr var2) var1)) (is-O_node var9)) (= (getnode var9) var0)) (= (|node::n| var0) var6)) (= (write var11 var10 var4) var3)) (not (= var1 var16))) (not (= var12 0))))) (Inv_Heap_exp_exp (newAddr var2) var15 var14))))
(assert (forall ((var0 Int) (var1 node) (var2 Addr) (var3 Heap) (var4 AllocResHeap) (var5 Heap) (var6 HeapObject) (var7 node) (var8 Addr) (var9 HeapObject) (var10 node) (var11 HeapObject) (var12 Addr) (var13 Heap) (var14 Int) (var15 Addr) (var16 Addr) (var17 Int) (var18 Addr)) (or (not (and (_Glue6_exp_exp var18 var17 var16 var15 var14 var13 var12 var11) (and (and (and (and (and (and (and (and (and (and (and (and (and (= (O_node var10) var9) (= (node 1 var8) var7)) (= (O_node var7) var6)) (= (node var17 var16) var10)) (= (alloc var5 var9) var4)) (= (newHeap var4) var3)) (= (newAddr var4) var2)) (not (= var2 var18))) (not (= var14 0))) (is-O_node var11)) (= (getnode var11) var1)) (= (|node::n| var1) var8)) (= (write var13 var12 var6) var5)) (= var0 0)))) (inv_main_9 var3 var0 var15 var2 var12))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 HeapObject) (var4 node) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Int) (var9 Addr)) (or (not (and (and (Inv_Heap_exp_exp var9 var8 var7) (inv_main540_3 var6 0 var5 var9)) (and (and (and (and (= (O_node var4) var3) (= (node var8 var7) var4)) (= nullAddr var2)) (= (read var6 var9) var3)) (valid var6 var9)))) (_Glue9_exp_exp var2 var1 var0 var5 var6 var9 var3))))
(assert (forall ((var0 Addr) (var1 Int) (var2 HeapObject) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main540_3 var6 0 var5 var4) (and (and (= nullAddr var3) (= (read var6 var4) var2)) (not (valid var6 var4))))) (_Glue9_exp_exp var3 var1 var0 var5 var6 var4 var2))))
(assert (forall ((var0 Int) (var1 Addr) (var2 node) (var3 HeapObject) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Int) (var9 Addr)) (or (not (and (_Glue9_exp_exp var9 var8 var7 var6 var5 var4 var3) (and (and (and (and (is-O_node var3) (= (getnode var3) var2)) (= (|node::n| var2) var1)) (valid var5 var4)) (= var0 2)))) (Inv_Heap_exp_exp var4 var0 var1))))
(assert (forall ((var0 node) (var1 Addr) (var2 AllocResHeap) (var3 Heap) (var4 HeapObject) (var5 node) (var6 Addr) (var7 HeapObject) (var8 node) (var9 HeapObject) (var10 Addr) (var11 Heap) (var12 Addr) (var13 Addr) (var14 Int) (var15 Addr)) (or (not (and (_Glue9_exp_exp var15 var14 var13 var12 var11 var10 var9) (and (and (and (and (and (and (and (and (and (and (= (O_node var8) var7) (= (node 2 var6) var5)) (= (O_node var5) var4)) (= (node var14 var13) var8)) (= (alloc var3 var7) var2)) (= (newAddr var2) var1)) (is-O_node var9)) (= (getnode var9) var0)) (= (|node::n| var0) var6)) (= (write var11 var10 var4) var3)) (not (= var1 var15))))) (Inv_Heap_exp_exp (newAddr var2) var14 var13))))
(assert (forall ((var0 Int) (var1 node) (var2 Addr) (var3 Heap) (var4 AllocResHeap) (var5 Heap) (var6 HeapObject) (var7 node) (var8 Addr) (var9 HeapObject) (var10 node) (var11 HeapObject) (var12 Addr) (var13 Heap) (var14 Addr) (var15 Addr) (var16 Int) (var17 Addr)) (or (not (and (_Glue9_exp_exp var17 var16 var15 var14 var13 var12 var11) (and (and (and (and (and (and (and (and (and (and (and (and (= (O_node var10) var9) (= (node 2 var8) var7)) (= (O_node var7) var6)) (= (node var16 var15) var10)) (= (alloc var5 var9) var4)) (= (newHeap var4) var3)) (= (newAddr var4) var2)) (not (= var2 var17))) (is-O_node var11)) (= (getnode var11) var1)) (= (|node::n| var1) var8)) (= (write var13 var12 var6) var5)) (= var0 1)))) (inv_main_9 var3 var0 var14 var2 var12))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Int) (var6 Addr)) (not (and (and (Inv_Heap_exp_exp var6 var5 var4) (inv_main540_3 var3 0 var2 var6)) (and (and (and (and (= (O_node var1) var0) (= (node var5 var4) var1)) (= (read var3 var6) var0)) (not (= 4 4))) (valid var3 var6))))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main540_3 var3 0 var2 var1) (and (and (and (is-O_node var0) (= (read var3 var1) var0)) (not (= 4 4))) (not (valid var3 var1)))))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Int) (var7 Addr)) (or (not (and (and (Inv_Heap_exp_exp var7 var6 var5) (inv_main_21 var4 0 var3 var2 var7)) (and (and (and (= (O_node var1) var0) (= (node var6 var5) var1)) (= (read var4 var7) var0)) (valid var4 var7)))) (_Glue0 var3 var4 var2 var7 var0))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main_21 var4 0 var3 var2 var1) (and (= (read var4 var1) var0) (not (valid var4 var1))))) (_Glue0 var3 var4 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 node) (var2 HeapObject) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr)) (or (not (and (_Glue0 var6 var5 var4 var3 var2) (and (and (and (and (is-O_node var2) (= (getnode var2) var1)) (= (|node::h| var1) var0)) (not (= var0 3))) (valid var5 var3)))) (Inv_Heap_exp_exp var3 var0 var4))))
(assert (forall ((var0 Int) (var1 Heap) (var2 HeapObject) (var3 node) (var4 Int) (var5 Addr) (var6 node) (var7 HeapObject) (var8 Addr) (var9 Addr) (var10 Heap) (var11 Addr)) (or (not (and (_Glue0 var11 var10 var9 var8 var7) (and (and (and (and (and (and (and (and (is-O_node var7) (= (getnode var7) var6)) (= (|node::n| var6) var5)) (= (|node::h| var6) var4)) (not (= var4 3))) (= (node var4 var9) var3)) (= (O_node var3) var2)) (= (write var10 var8 var2) var1)) (= var0 1)))) (inv_main_21 var1 var0 var11 var8 var5))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Int) (var4 Heap) (var5 Addr) (var6 Int) (var7 Addr)) (not (and (and (Inv_Heap_exp_exp var7 var6 var5) (inv_main540_3 var4 var3 var2 var7)) (and (and (and (and (and (= (O_node var1) var0) (= (node var6 var5) var1)) (not (= 4 4))) (= (read var4 var7) var0)) (not (= var3 0))) (valid var4 var7))))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap)) (not (and (inv_main540_3 var4 var3 var2 var1) (and (and (and (not (is-O_node var0)) (= (read var4 var1) var0)) (not (= var3 0))) (not (valid var4 var1)))))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Int) (var4 Heap) (var5 Addr) (var6 Int) (var7 Addr)) (not (and (and (Inv_Heap_exp_exp var7 var6 var5) (inv_main540_3 var4 var3 var2 var7)) (and (and (and (and (and (= (O_node var1) var0) (= (node var6 var5) var1)) (= (read var4 var7) var0)) (not (= 4 4))) (not (= var3 0))) (valid var4 var7))))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap)) (not (and (inv_main540_3 var4 var3 var2 var1) (and (and (and (and (is-O_node var0) (= (read var4 var1) var0)) (not (= 4 4))) (not (= var3 0))) (not (valid var4 var1)))))))
(check-sat)
