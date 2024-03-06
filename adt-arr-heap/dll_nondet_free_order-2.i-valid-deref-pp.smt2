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
   (node (|node::next| Addr) (|node::prev| Addr))
  )
))
(declare-fun _Glue19 (Heap Int Addr Addr HeapObject) Bool)
(declare-fun inv_main570_3 (Heap Int Addr Addr) Bool)
(declare-fun _Glue39 (Int Heap Addr Addr HeapObject) Bool)
(declare-fun _Glue38 (Heap Addr Int Addr Addr HeapObject) Bool)
(declare-fun _Glue17 (Int Heap Addr Addr HeapObject) Bool)
(declare-fun _Glue7 (Addr Heap HeapObject) Bool)
(declare-fun _Glue32 (Addr Heap HeapObject) Bool)
(declare-fun _Glue13 (Addr Int Addr Heap HeapObject) Bool)
(declare-fun _Glue28 (Addr Heap HeapObject) Bool)
(declare-fun Inv_Heap_exp_exp (Addr Addr Addr) Bool)
(declare-fun _Glue36 (Addr Int Addr Addr Heap HeapObject) Bool)
(declare-fun _Glue22 (Int Heap Addr Addr HeapObject) Bool)
(declare-fun _Glue24 (Heap Int Addr Addr HeapObject) Bool)
(declare-fun _Glue10 (Int Heap Addr Addr HeapObject) Bool)
(declare-fun _Glue34 (Heap Addr HeapObject) Bool)
(declare-fun _Glue3 (Addr Int Addr Heap HeapObject) Bool)
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Int) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr)) (not (and (and (Inv_Heap_exp_exp var7 var6 var5) (inv_main570_3 var4 var3 var7 var2)) (and (and (and (and (and (= (O_node var1) var0) (= (node var6 var5) var1)) (not (= 4 4))) (= (read var4 var7) var0)) (not (<= 0 (+ (+ (- 1) var3) (- 1))))) (valid var4 var7))))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap)) (not (and (inv_main570_3 var4 var3 var2 var1) (and (and (and (not (is-O_node var0)) (= (read var4 var2) var0)) (not (<= 0 (+ (+ (- 1) var3) (- 1))))) (not (valid var4 var2)))))))
(assert (forall ((var0 AllocResHeap) (var1 Heap) (var2 Addr) (var3 Addr) (var4 HeapObject) (var5 node)) (or (not (and (and (and (= (O_node var5) var4) (= (node var3 var2) var5)) (= (alloc var1 var4) var0)) (= emptyHeap var1))) (Inv_Heap_exp_exp (newAddr var0) var3 var2))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 HeapObject) (var3 node) (var4 AllocResHeap) (var5 Heap) (var6 HeapObject) (var7 node) (var8 Addr) (var9 Addr) (var10 Addr)) (not (and (Inv_Heap_exp_exp var10 var9 var8) (and (and (and (and (and (and (and (and (and (and (= (O_node var7) var6) (= (AllocResHeap var5 var10) var4)) (= (O_node var3) var2)) (= (node var9 var8) var7)) (not (= var1 var10))) (= (read var5 var10) var6)) (not (= 4 4))) (valid var5 var10)) (= (alloc var0 var2) var4)) (= nullAddr var1)) (= emptyHeap var0))))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 node) (var3 AllocResHeap) (var4 HeapObject) (var5 Heap) (var6 Addr) (var7 Addr)) (not (and (and (and (and (and (and (and (and (not (= var7 var6)) (= (read var5 var6) var4)) (not (is-O_node var4))) (not (valid var5 var6))) (= (AllocResHeap var5 var6) var3)) (= (O_node var2) var1)) (= (alloc var0 var1) var3)) (= nullAddr var7)) (= emptyHeap var0)))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Int) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr)) (not (and (and (Inv_Heap_exp_exp var7 var6 var5) (inv_main570_3 var4 var3 var7 var2)) (and (and (and (and (and (= (O_node var1) var0) (= (node var6 var5) var1)) (= (read var4 var7) var0)) (not (= 4 4))) (not (<= 0 (+ (+ (- 1) var3) (- 1))))) (valid var4 var7))))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap)) (not (and (inv_main570_3 var4 var3 var2 var1) (and (and (and (and (is-O_node var0) (= (read var4 var2) var0)) (not (= 4 4))) (not (<= 0 (+ (+ (- 1) var3) (- 1))))) (not (valid var4 var2)))))))
(assert (forall ((var0 AllocResHeap) (var1 Addr) (var2 Addr) (var3 HeapObject) (var4 node) (var5 Addr) (var6 Addr) (var7 Int) (var8 Heap)) (or (not (and (inv_main570_3 var8 var7 var6 var5) (and (and (and (= (O_node var4) var3) (= (node var2 var1) var4)) (not (= 4 4))) (= (alloc var8 var3) var0)))) (Inv_Heap_exp_exp (newAddr var0) var2 var1))))
(assert (forall ((var0 Addr) (var1 AllocResHeap) (var2 Heap) (var3 HeapObject) (var4 node) (var5 HeapObject) (var6 node) (var7 Addr) (var8 Addr) (var9 Int) (var10 Heap) (var11 Addr) (var12 Addr) (var13 Addr)) (not (and (and (Inv_Heap_exp_exp var13 var12 var11) (inv_main570_3 var10 var9 var8 var7)) (and (and (and (and (and (and (and (and (and (and (= (O_node var6) var5) (= (O_node var4) var3)) (= (AllocResHeap var2 var13) var1)) (= (node var12 var11) var6)) (not (= var0 var13))) (= (read var2 var13) var5)) (<= 0 (+ (+ (- 1) var9) (- 1)))) (valid var2 var13)) (not (= 4 4))) (= nullAddr var0)) (= (alloc var10 var3) var1))))))
(assert (forall ((var0 AllocResHeap) (var1 HeapObject) (var2 node) (var3 HeapObject) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Int) (var10 Heap)) (not (and (inv_main570_3 var10 var9 var8 var7) (and (and (and (and (and (and (and (and (and (not (= var6 var5)) (= (read var4 var5) var3)) (is-O_node var3)) (<= 0 (+ (+ (- 1) var9) (- 1)))) (not (valid var4 var5))) (= (O_node var2) var1)) (= (AllocResHeap var4 var5) var0)) (not (= 4 4))) (= nullAddr var6)) (= (alloc var10 var1) var0))))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Int) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr)) (or (not (and (and (Inv_Heap_exp_exp var7 var6 var5) (inv_main570_3 var4 var3 var7 var2)) (and (and (and (and (= (O_node var1) var0) (= (node var6 var5) var1)) (not (= 4 4))) (= (read var4 var7) var0)) (valid var4 var7)))) (_Glue17 var3 var4 var7 var2 var0))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap)) (or (not (and (inv_main570_3 var4 var3 var2 var1) (and (and (not (= 4 4)) (= (read var4 var2) var0)) (not (valid var4 var2))))) (_Glue17 var3 var4 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 node) (var2 HeapObject) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Int)) (or (not (and (_Glue17 var6 var5 var4 var3 var2) (and (and (and (is-O_node var2) (= (getnode var2) var1)) (= (|node::prev| var1) var0)) (valid var5 var4)))) (Inv_Heap_exp_exp var4 var3 var0))))
(assert (forall ((var0 node) (var1 Heap) (var2 HeapObject) (var3 node) (var4 Addr) (var5 HeapObject) (var6 node) (var7 HeapObject) (var8 Addr) (var9 Heap) (var10 Int) (var11 Addr) (var12 Addr) (var13 Addr)) (or (not (and (and (Inv_Heap_exp_exp var13 var12 var11) (_Glue17 var10 var9 var8 var13 var7)) (and (and (and (and (and (and (and (and (and (= (O_node var6) var5) (= (node var13 var4) var3)) (= (O_node var3) var2)) (= (node var12 var11) var6)) (= (read var1 var13) var5)) (valid var1 var13)) (is-O_node var7)) (= (getnode var7) var0)) (= (|node::prev| var0) var4)) (= (write var9 var8 var2) var1)))) (_Glue19 var1 var10 var8 var13 var5))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 node) (var4 HeapObject) (var5 Heap) (var6 HeapObject) (var7 Addr) (var8 Addr) (var9 Heap) (var10 Int)) (or (not (and (_Glue17 var10 var9 var8 var7 var6) (and (and (and (and (and (and (and (= (read var5 var7) var4) (not (valid var5 var7))) (is-O_node var6)) (= (getnode var6) var3)) (= (|node::prev| var3) var2)) (= (node var7 var2) var1)) (= (O_node var1) var0)) (= (write var9 var8 var0) var5)))) (_Glue19 var5 var10 var8 var7 var4))))
(assert (forall ((var0 Addr) (var1 node) (var2 HeapObject) (var3 Addr) (var4 Addr) (var5 Int) (var6 Heap)) (or (not (and (_Glue19 var6 var5 var4 var3 var2) (and (and (and (is-O_node var2) (= (getnode var2) var1)) (= (|node::next| var1) var0)) (valid var6 var3)))) (Inv_Heap_exp_exp var3 var0 var4))))
(assert (forall ((var0 node) (var1 Heap) (var2 HeapObject) (var3 node) (var4 Addr) (var5 HeapObject) (var6 node) (var7 HeapObject) (var8 Addr) (var9 Int) (var10 Heap) (var11 Addr) (var12 Addr) (var13 Addr)) (not (and (and (Inv_Heap_exp_exp var13 var12 var11) (_Glue19 var10 var9 var8 var13 var7)) (and (and (and (and (and (and (and (and (and (and (= (O_node var6) var5) (= (node var4 var8) var3)) (= (O_node var3) var2)) (= (node var12 var11) var6)) (= (read var1 var13) var5)) (not (<= 0 (+ (+ (- 1) var9) (- 1))))) (valid var1 var13)) (is-O_node var7)) (= (getnode var7) var0)) (= (|node::next| var0) var4)) (= (write var10 var13 var2) var1))))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 node) (var4 HeapObject) (var5 Heap) (var6 HeapObject) (var7 Addr) (var8 Addr) (var9 Int) (var10 Heap)) (not (and (_Glue19 var10 var9 var8 var7 var6) (and (and (and (and (and (and (and (and (and (= (read var5 var7) var4) (is-O_node var4)) (not (<= 0 (+ (+ (- 1) var9) (- 1))))) (not (valid var5 var7))) (is-O_node var6)) (= (getnode var6) var3)) (= (|node::next| var3) var2)) (= (node var2 var8) var1)) (= (O_node var1) var0)) (= (write var10 var7 var0) var5))))))
(assert (forall ((var0 AllocResHeap) (var1 Heap) (var2 Addr) (var3 Addr) (var4 HeapObject) (var5 node)) (or (not (and (and (and (= (O_node var5) var4) (= (node var3 var2) var5)) (= (alloc var1 var4) var0)) (= emptyHeap var1))) (Inv_Heap_exp_exp (newAddr var0) var3 var2))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 HeapObject) (var3 node) (var4 AllocResHeap) (var5 Heap) (var6 HeapObject) (var7 node) (var8 Addr) (var9 Addr) (var10 Addr)) (or (not (and (Inv_Heap_exp_exp var10 var9 var8) (and (and (and (and (and (and (and (and (and (= (O_node var7) var6) (= (AllocResHeap var5 var10) var4)) (= (O_node var3) var2)) (= (node var9 var8) var7)) (not (= var1 var10))) (= (read var5 var10) var6)) (valid var5 var10)) (= (alloc var0 var2) var4)) (= nullAddr var1)) (= emptyHeap var0)))) (_Glue28 var10 var5 var6))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 node) (var3 AllocResHeap) (var4 HeapObject) (var5 Heap) (var6 Addr) (var7 Addr)) (or (not (and (and (and (and (and (and (and (not (= var7 var6)) (= (read var5 var6) var4)) (not (valid var5 var6))) (= (AllocResHeap var5 var6) var3)) (= (O_node var2) var1)) (= (alloc var0 var1) var3)) (= nullAddr var7)) (= emptyHeap var0))) (_Glue28 var6 var5 var4))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 node) (var3 HeapObject) (var4 Heap) (var5 Addr)) (or (not (and (_Glue28 var5 var4 var3) (and (and (and (and (is-O_node var3) (= (getnode var3) var2)) (= (|node::prev| var2) var1)) (valid var4 var5)) (= var0 var5)))) (Inv_Heap_exp_exp var5 var0 var1))))
(assert (forall ((var0 node) (var1 Heap) (var2 HeapObject) (var3 node) (var4 Addr) (var5 HeapObject) (var6 node) (var7 HeapObject) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Addr)) (not (and (and (Inv_Heap_exp_exp var11 var10 var9) (_Glue28 var11 var8 var7)) (and (and (and (and (and (and (and (and (and (and (= (O_node var6) var5) (= (node var11 var4) var3)) (= (O_node var3) var2)) (= (node var10 var9) var6)) (= (read var1 var11) var5)) (not (= 4 4))) (valid var1 var11)) (is-O_node var7)) (= (getnode var7) var0)) (= (|node::prev| var0) var4)) (= (write var8 var11 var2) var1))))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 node) (var4 HeapObject) (var5 Heap) (var6 HeapObject) (var7 Heap) (var8 Addr)) (not (and (_Glue28 var8 var7 var6) (and (and (and (and (and (and (and (and (= (read var5 var8) var4) (not (is-O_node var4))) (not (valid var5 var8))) (is-O_node var6)) (= (getnode var6) var3)) (= (|node::prev| var3) var2)) (= (node var8 var2) var1)) (= (O_node var1) var0)) (= (write var7 var8 var0) var5))))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Int) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr)) (or (not (and (and (Inv_Heap_exp_exp var7 var6 var5) (inv_main570_3 var4 var3 var7 var2)) (and (and (and (= (O_node var1) var0) (= (node var6 var5) var1)) (= (read var4 var7) var0)) (valid var4 var7)))) (_Glue39 var3 var4 var7 var2 var0))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap)) (or (not (and (inv_main570_3 var4 var3 var2 var1) (and (= (read var4 var2) var0) (not (valid var4 var2))))) (_Glue39 var3 var4 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 node) (var2 HeapObject) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Int)) (or (not (and (_Glue39 var6 var5 var4 var3 var2) (and (and (and (is-O_node var2) (= (getnode var2) var1)) (= (|node::prev| var1) var0)) (valid var5 var4)))) (Inv_Heap_exp_exp var4 var3 var0))))
(assert (forall ((var0 node) (var1 Heap) (var2 HeapObject) (var3 node) (var4 Addr) (var5 HeapObject) (var6 node) (var7 HeapObject) (var8 Addr) (var9 Heap) (var10 Int) (var11 Addr) (var12 Addr) (var13 Addr)) (not (and (and (Inv_Heap_exp_exp var13 var12 var11) (_Glue39 var10 var9 var8 var13 var7)) (and (and (and (and (and (and (and (and (and (and (and (= (O_node var6) var5) (= (node var13 var4) var3)) (= (O_node var3) var2)) (= (node var12 var11) var6)) (= (read var1 var13) var5)) (not (= 4 4))) (not (<= 0 (+ (+ (- 1) var10) (- 1))))) (valid var1 var13)) (is-O_node var7)) (= (getnode var7) var0)) (= (|node::prev| var0) var4)) (= (write var9 var8 var2) var1))))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 node) (var4 HeapObject) (var5 Heap) (var6 HeapObject) (var7 Addr) (var8 Addr) (var9 Heap) (var10 Int)) (not (and (_Glue39 var10 var9 var8 var7 var6) (and (and (and (and (and (and (and (and (and (= (read var5 var7) var4) (not (is-O_node var4))) (not (<= 0 (+ (+ (- 1) var10) (- 1))))) (not (valid var5 var7))) (is-O_node var6)) (= (getnode var6) var3)) (= (|node::prev| var3) var2)) (= (node var7 var2) var1)) (= (O_node var1) var0)) (= (write var9 var8 var0) var5))))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Int) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr)) (or (not (and (and (Inv_Heap_exp_exp var7 var6 var5) (inv_main570_3 var4 var3 var7 var2)) (and (and (and (and (= (O_node var1) var0) (= (node var6 var5) var1)) (not (= 4 4))) (= (read var4 var7) var0)) (valid var4 var7)))) (_Glue10 var3 var4 var7 var2 var0))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap)) (or (not (and (inv_main570_3 var4 var3 var2 var1) (and (and (not (= 4 4)) (= (read var4 var2) var0)) (not (valid var4 var2))))) (_Glue10 var3 var4 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 node) (var2 HeapObject) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Int)) (or (not (and (_Glue10 var6 var5 var4 var3 var2) (and (and (and (is-O_node var2) (= (getnode var2) var1)) (= (|node::prev| var1) var0)) (valid var5 var4)))) (Inv_Heap_exp_exp var4 var3 var0))))
(assert (forall ((var0 node) (var1 Heap) (var2 HeapObject) (var3 node) (var4 Addr) (var5 HeapObject) (var6 node) (var7 HeapObject) (var8 Addr) (var9 Heap) (var10 Int) (var11 Addr) (var12 Addr) (var13 Addr)) (not (and (and (Inv_Heap_exp_exp var13 var12 var11) (_Glue10 var10 var9 var8 var13 var7)) (and (and (and (and (and (and (and (and (and (and (= (O_node var6) var5) (= (node var13 var4) var3)) (= (O_node var3) var2)) (= (node var12 var11) var6)) (= (read var1 var13) var5)) (not (<= 0 (+ (+ (- 1) var10) (- 1))))) (valid var1 var13)) (is-O_node var7)) (= (getnode var7) var0)) (= (|node::prev| var0) var4)) (= (write var9 var8 var2) var1))))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 node) (var4 HeapObject) (var5 Heap) (var6 HeapObject) (var7 Addr) (var8 Addr) (var9 Heap) (var10 Int)) (not (and (_Glue10 var10 var9 var8 var7 var6) (and (and (and (and (and (and (and (and (and (= (read var5 var7) var4) (is-O_node var4)) (not (<= 0 (+ (+ (- 1) var10) (- 1))))) (not (valid var5 var7))) (is-O_node var6)) (= (getnode var6) var3)) (= (|node::prev| var3) var2)) (= (node var7 var2) var1)) (= (O_node var1) var0)) (= (write var9 var8 var0) var5))))))
(assert (forall ((var0 AllocResHeap) (var1 Addr) (var2 Addr) (var3 HeapObject) (var4 node) (var5 Addr) (var6 Addr) (var7 Int) (var8 Heap)) (or (not (and (inv_main570_3 var8 var7 var6 var5) (and (and (= (O_node var4) var3) (= (node var2 var1) var4)) (= (alloc var8 var3) var0)))) (Inv_Heap_exp_exp (newAddr var0) var2 var1))))
(assert (forall ((var0 Addr) (var1 AllocResHeap) (var2 Heap) (var3 HeapObject) (var4 node) (var5 HeapObject) (var6 node) (var7 Addr) (var8 Addr) (var9 Int) (var10 Heap) (var11 Addr) (var12 Addr) (var13 Addr)) (not (and (and (Inv_Heap_exp_exp var13 var12 var11) (inv_main570_3 var10 var9 var8 var7)) (and (and (and (and (and (and (and (and (and (and (= (O_node var6) var5) (= (O_node var4) var3)) (= (AllocResHeap var2 var13) var1)) (= (node var12 var11) var6)) (not (= var0 var13))) (= (read var2 var13) var5)) (not (= 4 4))) (<= 0 (+ (+ (- 1) var9) (- 1)))) (valid var2 var13)) (= nullAddr var0)) (= (alloc var10 var3) var1))))))
(assert (forall ((var0 AllocResHeap) (var1 HeapObject) (var2 node) (var3 HeapObject) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Int) (var10 Heap)) (not (and (inv_main570_3 var10 var9 var8 var7) (and (and (and (and (and (and (and (and (not (= var6 var5)) (= (read var4 var5) var3)) (not (is-O_node var3))) (<= 0 (+ (+ (- 1) var9) (- 1)))) (not (valid var4 var5))) (= (O_node var2) var1)) (= (AllocResHeap var4 var5) var0)) (= nullAddr var6)) (= (alloc var10 var1) var0))))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Int) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr)) (or (not (and (and (Inv_Heap_exp_exp var7 var6 var5) (inv_main570_3 var4 var3 var7 var2)) (and (and (and (= (O_node var1) var0) (= (node var6 var5) var1)) (= (read var4 var7) var0)) (valid var4 var7)))) (_Glue22 var3 var4 var7 var2 var0))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap)) (or (not (and (inv_main570_3 var4 var3 var2 var1) (and (= (read var4 var2) var0) (not (valid var4 var2))))) (_Glue22 var3 var4 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 node) (var2 HeapObject) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Int)) (or (not (and (_Glue22 var6 var5 var4 var3 var2) (and (and (and (is-O_node var2) (= (getnode var2) var1)) (= (|node::prev| var1) var0)) (valid var5 var4)))) (Inv_Heap_exp_exp var4 var3 var0))))
(assert (forall ((var0 node) (var1 Heap) (var2 HeapObject) (var3 node) (var4 Addr) (var5 HeapObject) (var6 node) (var7 HeapObject) (var8 Addr) (var9 Heap) (var10 Int) (var11 Addr) (var12 Addr) (var13 Addr)) (or (not (and (and (Inv_Heap_exp_exp var13 var12 var11) (_Glue22 var10 var9 var8 var13 var7)) (and (and (and (and (and (and (and (and (and (= (O_node var6) var5) (= (node var13 var4) var3)) (= (O_node var3) var2)) (= (node var12 var11) var6)) (= (read var1 var13) var5)) (valid var1 var13)) (is-O_node var7)) (= (getnode var7) var0)) (= (|node::prev| var0) var4)) (= (write var9 var8 var2) var1)))) (_Glue24 var1 var10 var8 var13 var5))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 node) (var4 HeapObject) (var5 Heap) (var6 HeapObject) (var7 Addr) (var8 Addr) (var9 Heap) (var10 Int)) (or (not (and (_Glue22 var10 var9 var8 var7 var6) (and (and (and (and (and (and (and (= (read var5 var7) var4) (not (valid var5 var7))) (is-O_node var6)) (= (getnode var6) var3)) (= (|node::prev| var3) var2)) (= (node var7 var2) var1)) (= (O_node var1) var0)) (= (write var9 var8 var0) var5)))) (_Glue24 var5 var10 var8 var7 var4))))
(assert (forall ((var0 Addr) (var1 node) (var2 HeapObject) (var3 Addr) (var4 Addr) (var5 Int) (var6 Heap)) (or (not (and (_Glue24 var6 var5 var4 var3 var2) (and (and (and (is-O_node var2) (= (getnode var2) var1)) (= (|node::next| var1) var0)) (valid var6 var3)))) (Inv_Heap_exp_exp var3 var0 var4))))
(assert (forall ((var0 node) (var1 Heap) (var2 HeapObject) (var3 node) (var4 Addr) (var5 HeapObject) (var6 node) (var7 HeapObject) (var8 Addr) (var9 Int) (var10 Heap) (var11 Addr) (var12 Addr) (var13 Addr)) (not (and (and (Inv_Heap_exp_exp var13 var12 var11) (_Glue24 var10 var9 var8 var13 var7)) (and (and (and (and (and (and (and (and (and (and (and (= (O_node var6) var5) (= (node var4 var8) var3)) (= (O_node var3) var2)) (= (node var12 var11) var6)) (= (read var1 var13) var5)) (not (= 4 4))) (not (<= 0 (+ (+ (- 1) var9) (- 1))))) (valid var1 var13)) (is-O_node var7)) (= (getnode var7) var0)) (= (|node::next| var0) var4)) (= (write var10 var13 var2) var1))))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 node) (var4 HeapObject) (var5 Heap) (var6 HeapObject) (var7 Addr) (var8 Addr) (var9 Int) (var10 Heap)) (not (and (_Glue24 var10 var9 var8 var7 var6) (and (and (and (and (and (and (and (and (and (= (read var5 var7) var4) (not (is-O_node var4))) (not (<= 0 (+ (+ (- 1) var9) (- 1))))) (not (valid var5 var7))) (is-O_node var6)) (= (getnode var6) var3)) (= (|node::next| var3) var2)) (= (node var2 var8) var1)) (= (O_node var1) var0)) (= (write var10 var7 var0) var5))))))
(assert (forall ((var0 AllocResHeap) (var1 Heap) (var2 Addr) (var3 Addr) (var4 HeapObject) (var5 node)) (or (not (and (and (and (and (= (O_node var5) var4) (= (node var3 var2) var5)) (= (alloc var1 var4) var0)) (not (= 4 4))) (= emptyHeap var1))) (Inv_Heap_exp_exp (newAddr var0) var3 var2))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 HeapObject) (var3 node) (var4 AllocResHeap) (var5 Heap) (var6 HeapObject) (var7 node) (var8 Addr) (var9 Addr) (var10 Addr)) (or (not (and (Inv_Heap_exp_exp var10 var9 var8) (and (and (and (and (and (and (and (and (and (and (= (O_node var7) var6) (= (AllocResHeap var5 var10) var4)) (= (O_node var3) var2)) (= (node var9 var8) var7)) (not (= var1 var10))) (= (read var5 var10) var6)) (valid var5 var10)) (= (alloc var0 var2) var4)) (not (= 4 4))) (= nullAddr var1)) (= emptyHeap var0)))) (_Glue7 var10 var5 var6))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 node) (var3 AllocResHeap) (var4 HeapObject) (var5 Heap) (var6 Addr) (var7 Addr)) (or (not (and (and (and (and (and (and (and (and (not (= var7 var6)) (= (read var5 var6) var4)) (not (valid var5 var6))) (= (AllocResHeap var5 var6) var3)) (= (O_node var2) var1)) (= (alloc var0 var1) var3)) (not (= 4 4))) (= nullAddr var7)) (= emptyHeap var0))) (_Glue7 var6 var5 var4))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 node) (var3 HeapObject) (var4 Heap) (var5 Addr)) (or (not (and (_Glue7 var5 var4 var3) (and (and (and (and (is-O_node var3) (= (getnode var3) var2)) (= (|node::prev| var2) var1)) (valid var4 var5)) (= var0 var5)))) (Inv_Heap_exp_exp var5 var0 var1))))
(assert (forall ((var0 node) (var1 Heap) (var2 HeapObject) (var3 node) (var4 Addr) (var5 HeapObject) (var6 node) (var7 HeapObject) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Addr)) (not (and (and (Inv_Heap_exp_exp var11 var10 var9) (_Glue7 var11 var8 var7)) (and (and (and (and (and (and (and (and (and (= (O_node var6) var5) (= (node var11 var4) var3)) (= (O_node var3) var2)) (= (node var10 var9) var6)) (= (read var1 var11) var5)) (valid var1 var11)) (is-O_node var7)) (= (getnode var7) var0)) (= (|node::prev| var0) var4)) (= (write var8 var11 var2) var1))))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 node) (var4 HeapObject) (var5 Heap) (var6 HeapObject) (var7 Heap) (var8 Addr)) (not (and (_Glue7 var8 var7 var6) (and (and (and (and (and (and (and (and (= (read var5 var8) var4) (is-O_node var4)) (not (valid var5 var8))) (is-O_node var6)) (= (getnode var6) var3)) (= (|node::prev| var3) var2)) (= (node var8 var2) var1)) (= (O_node var1) var0)) (= (write var7 var8 var0) var5))))))
(assert (forall ((var0 AllocResHeap) (var1 Heap) (var2 Addr) (var3 Addr) (var4 HeapObject) (var5 node)) (or (not (and (and (and (and (= (O_node var5) var4) (= (node var3 var2) var5)) (= (alloc var1 var4) var0)) (not (= 4 4))) (= emptyHeap var1))) (Inv_Heap_exp_exp (newAddr var0) var3 var2))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 HeapObject) (var3 node) (var4 AllocResHeap) (var5 Heap) (var6 HeapObject) (var7 node) (var8 Addr) (var9 Addr) (var10 Addr)) (not (and (Inv_Heap_exp_exp var10 var9 var8) (and (and (and (and (and (and (and (and (and (and (= (O_node var7) var6) (= (AllocResHeap var5 var10) var4)) (= (O_node var3) var2)) (= (node var9 var8) var7)) (not (= var1 var10))) (= (read var5 var10) var6)) (valid var5 var10)) (= (alloc var0 var2) var4)) (not (= 4 4))) (= nullAddr var1)) (= emptyHeap var0))))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 node) (var3 AllocResHeap) (var4 HeapObject) (var5 Heap) (var6 Addr) (var7 Addr)) (not (and (and (and (and (and (and (and (and (and (not (= var7 var6)) (= (read var5 var6) var4)) (is-O_node var4)) (not (valid var5 var6))) (= (AllocResHeap var5 var6) var3)) (= (O_node var2) var1)) (= (alloc var0 var1) var3)) (not (= 4 4))) (= nullAddr var7)) (= emptyHeap var0)))))
(assert (forall ((var0 AllocResHeap) (var1 Addr) (var2 Addr) (var3 HeapObject) (var4 node) (var5 Addr) (var6 Addr) (var7 Int) (var8 Heap)) (or (not (and (inv_main570_3 var8 var7 var6 var5) (and (and (= (O_node var4) var3) (= (node var2 var1) var4)) (= (alloc var8 var3) var0)))) (Inv_Heap_exp_exp (newAddr var0) var2 var1))))
(assert (forall ((var0 Addr) (var1 AllocResHeap) (var2 Heap) (var3 HeapObject) (var4 node) (var5 HeapObject) (var6 node) (var7 Addr) (var8 Addr) (var9 Int) (var10 Heap) (var11 Addr) (var12 Addr) (var13 Addr)) (or (not (and (and (Inv_Heap_exp_exp var13 var12 var11) (inv_main570_3 var10 var9 var8 var7)) (and (and (and (and (and (and (and (and (= (O_node var6) var5) (= (O_node var4) var3)) (= (AllocResHeap var2 var13) var1)) (= (node var12 var11) var6)) (not (= var0 var13))) (= (read var2 var13) var5)) (valid var2 var13)) (= nullAddr var0)) (= (alloc var10 var3) var1)))) (_Glue13 var7 var9 var13 var2 var5))))
(assert (forall ((var0 AllocResHeap) (var1 HeapObject) (var2 node) (var3 HeapObject) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Int) (var10 Heap)) (or (not (and (inv_main570_3 var10 var9 var8 var7) (and (and (and (and (and (and (not (= var6 var5)) (= (read var4 var5) var3)) (not (valid var4 var5))) (= (O_node var2) var1)) (= (AllocResHeap var4 var5) var0)) (= nullAddr var6)) (= (alloc var10 var1) var0)))) (_Glue13 var7 var9 var5 var4 var3))))
(assert (forall ((var0 Addr) (var1 node) (var2 HeapObject) (var3 Heap) (var4 Addr) (var5 Int) (var6 Addr)) (or (not (and (_Glue13 var6 var5 var4 var3 var2) (and (and (and (is-O_node var2) (= (getnode var2) var1)) (= (|node::prev| var1) var0)) (valid var3 var4)))) (Inv_Heap_exp_exp var4 var6 var0))))
(assert (forall ((var0 node) (var1 Heap) (var2 HeapObject) (var3 node) (var4 Addr) (var5 HeapObject) (var6 node) (var7 HeapObject) (var8 Heap) (var9 Addr) (var10 Int) (var11 Addr) (var12 Addr) (var13 Addr)) (not (and (and (Inv_Heap_exp_exp var13 var12 var11) (_Glue13 var13 var10 var9 var8 var7)) (and (and (and (and (and (and (and (and (and (and (and (= (O_node var6) var5) (= (node var13 var4) var3)) (= (O_node var3) var2)) (= (node var12 var11) var6)) (= (read var1 var13) var5)) (not (= 4 4))) (<= 0 (+ (+ (- 1) var10) (- 1)))) (valid var1 var13)) (is-O_node var7)) (= (getnode var7) var0)) (= (|node::prev| var0) var4)) (= (write var8 var9 var2) var1))))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 node) (var4 HeapObject) (var5 Heap) (var6 HeapObject) (var7 Heap) (var8 Addr) (var9 Int) (var10 Addr)) (not (and (_Glue13 var10 var9 var8 var7 var6) (and (and (and (and (and (and (and (and (and (= (read var5 var10) var4) (not (is-O_node var4))) (<= 0 (+ (+ (- 1) var9) (- 1)))) (not (valid var5 var10))) (is-O_node var6)) (= (getnode var6) var3)) (= (|node::prev| var3) var2)) (= (node var10 var2) var1)) (= (O_node var1) var0)) (= (write var7 var8 var0) var5))))))
(assert (forall ((var0 AllocResHeap) (var1 Addr) (var2 Addr) (var3 HeapObject) (var4 node) (var5 Addr) (var6 Addr) (var7 Int) (var8 Heap)) (or (not (and (inv_main570_3 var8 (+ var7 1) var6 var5) (and (and (= (O_node var4) var3) (= (node var2 var1) var4)) (= (alloc var8 var3) var0)))) (Inv_Heap_exp_exp (newAddr var0) var2 var1))))
(assert (forall ((var0 Addr) (var1 AllocResHeap) (var2 Heap) (var3 HeapObject) (var4 node) (var5 HeapObject) (var6 node) (var7 Addr) (var8 Addr) (var9 Int) (var10 Heap) (var11 Addr) (var12 Addr) (var13 Addr)) (or (not (and (and (Inv_Heap_exp_exp var13 var12 var11) (inv_main570_3 var10 (+ var9 1) var8 var7)) (and (and (and (and (and (and (and (and (= (O_node var6) var5) (= (O_node var4) var3)) (= (AllocResHeap var2 var13) var1)) (= (node var12 var11) var6)) (not (= var0 var13))) (= (read var2 var13) var5)) (valid var2 var13)) (= nullAddr var0)) (= (alloc var10 var3) var1)))) (_Glue36 var7 var9 var8 var13 var2 var5))))
(assert (forall ((var0 AllocResHeap) (var1 HeapObject) (var2 node) (var3 HeapObject) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Int) (var10 Heap)) (or (not (and (inv_main570_3 var10 (+ var9 1) var8 var7) (and (and (and (and (and (and (not (= var6 var5)) (= (read var4 var5) var3)) (not (valid var4 var5))) (= (O_node var2) var1)) (= (AllocResHeap var4 var5) var0)) (= nullAddr var6)) (= (alloc var10 var1) var0)))) (_Glue36 var7 var9 var8 var5 var4 var3))))
(assert (forall ((var0 Addr) (var1 node) (var2 HeapObject) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Int) (var7 Addr)) (or (not (and (_Glue36 var7 var6 var5 var4 var3 var2) (and (and (and (is-O_node var2) (= (getnode var2) var1)) (= (|node::prev| var1) var0)) (valid var3 var4)))) (Inv_Heap_exp_exp var4 var7 var0))))
(assert (forall ((var0 node) (var1 Heap) (var2 HeapObject) (var3 node) (var4 Addr) (var5 HeapObject) (var6 node) (var7 HeapObject) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Int) (var12 Addr) (var13 Addr) (var14 Addr)) (or (not (and (and (Inv_Heap_exp_exp var14 var13 var12) (_Glue36 var14 var11 var10 var9 var8 var7)) (and (and (and (and (and (and (and (and (and (= (O_node var6) var5) (= (node var14 var4) var3)) (= (O_node var3) var2)) (= (node var13 var12) var6)) (= (read var1 var14) var5)) (valid var1 var14)) (is-O_node var7)) (= (getnode var7) var0)) (= (|node::prev| var0) var4)) (= (write var8 var9 var2) var1)))) (_Glue38 var1 var14 var11 var10 var9 var5))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 node) (var4 HeapObject) (var5 Heap) (var6 HeapObject) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Int) (var11 Addr)) (or (not (and (_Glue36 var11 var10 var9 var8 var7 var6) (and (and (and (and (and (and (and (= (read var5 var11) var4) (not (valid var5 var11))) (is-O_node var6)) (= (getnode var6) var3)) (= (|node::prev| var3) var2)) (= (node var11 var2) var1)) (= (O_node var1) var0)) (= (write var7 var8 var0) var5)))) (_Glue38 var5 var11 var10 var9 var8 var4))))
(assert (forall ((var0 Addr) (var1 node) (var2 HeapObject) (var3 Addr) (var4 Addr) (var5 Int) (var6 Addr) (var7 Heap)) (or (not (and (_Glue38 var7 var6 var5 var4 var3 var2) (and (and (and (and (is-O_node var2) (= (getnode var2) var1)) (= (|node::next| var1) var0)) (<= 0 (+ (+ (- 1) (+ var5 1)) (- 1)))) (valid var7 var6)))) (Inv_Heap_exp_exp var6 var0 var3))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 node) (var3 Addr) (var4 node) (var5 HeapObject) (var6 Addr) (var7 Addr) (var8 Int) (var9 Addr) (var10 Heap)) (or (not (and (_Glue38 var10 var9 var8 var7 var6 var5) (and (and (and (and (and (and (is-O_node var5) (= (getnode var5) var4)) (= (|node::next| var4) var3)) (= (node var3 var6) var2)) (= (O_node var2) var1)) (= (write var10 var9 var1) var0)) (<= 0 (+ (+ (- 1) (+ var8 1)) (- 1)))))) (inv_main570_3 var0 var8 var7 var6))))
(assert (forall ((var0 AllocResHeap) (var1 Heap) (var2 Addr) (var3 Addr) (var4 HeapObject) (var5 node)) (or (not (and (and (and (= (O_node var5) var4) (= (node var3 var2) var5)) (= (alloc var1 var4) var0)) (= emptyHeap var1))) (Inv_Heap_exp_exp (newAddr var0) var3 var2))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 HeapObject) (var3 node) (var4 AllocResHeap) (var5 Heap) (var6 HeapObject) (var7 node) (var8 Addr) (var9 Addr) (var10 Addr)) (or (not (and (Inv_Heap_exp_exp var10 var9 var8) (and (and (and (and (and (and (and (and (and (= (O_node var7) var6) (= (AllocResHeap var5 var10) var4)) (= (O_node var3) var2)) (= (node var9 var8) var7)) (not (= var1 var10))) (= (read var5 var10) var6)) (valid var5 var10)) (= (alloc var0 var2) var4)) (= nullAddr var1)) (= emptyHeap var0)))) (_Glue32 var10 var5 var6))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 node) (var3 AllocResHeap) (var4 HeapObject) (var5 Heap) (var6 Addr) (var7 Addr)) (or (not (and (and (and (and (and (and (and (not (= var7 var6)) (= (read var5 var6) var4)) (not (valid var5 var6))) (= (AllocResHeap var5 var6) var3)) (= (O_node var2) var1)) (= (alloc var0 var1) var3)) (= nullAddr var7)) (= emptyHeap var0))) (_Glue32 var6 var5 var4))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 node) (var3 HeapObject) (var4 Heap) (var5 Addr)) (or (not (and (_Glue32 var5 var4 var3) (and (and (and (and (is-O_node var3) (= (getnode var3) var2)) (= (|node::prev| var2) var1)) (valid var4 var5)) (= var0 var5)))) (Inv_Heap_exp_exp var5 var0 var1))))
(assert (forall ((var0 node) (var1 Heap) (var2 HeapObject) (var3 node) (var4 Addr) (var5 HeapObject) (var6 node) (var7 HeapObject) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Addr)) (or (not (and (and (Inv_Heap_exp_exp var11 var10 var9) (_Glue32 var11 var8 var7)) (and (and (and (and (and (and (and (and (and (= (O_node var6) var5) (= (node var11 var4) var3)) (= (O_node var3) var2)) (= (node var10 var9) var6)) (= (read var1 var11) var5)) (valid var1 var11)) (is-O_node var7)) (= (getnode var7) var0)) (= (|node::prev| var0) var4)) (= (write var8 var11 var2) var1)))) (_Glue34 var1 var11 var5))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 node) (var4 HeapObject) (var5 Heap) (var6 HeapObject) (var7 Heap) (var8 Addr)) (or (not (and (_Glue32 var8 var7 var6) (and (and (and (and (and (and (and (= (read var5 var8) var4) (not (valid var5 var8))) (is-O_node var6)) (= (getnode var6) var3)) (= (|node::prev| var3) var2)) (= (node var8 var2) var1)) (= (O_node var1) var0)) (= (write var7 var8 var0) var5)))) (_Glue34 var5 var8 var4))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 node) (var3 HeapObject) (var4 Addr) (var5 Heap)) (or (not (and (_Glue34 var5 var4 var3) (and (and (and (and (is-O_node var3) (= (getnode var3) var2)) (= (|node::next| var2) var1)) (valid var5 var4)) (= var0 var4)))) (Inv_Heap_exp_exp var4 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 HeapObject) (var4 node) (var5 Addr) (var6 node) (var7 HeapObject) (var8 Addr) (var9 Heap)) (or (not (and (_Glue34 var9 var8 var7) (and (and (and (and (and (and (and (is-O_node var7) (= (getnode var7) var6)) (= (|node::next| var6) var5)) (= (node var5 var8) var4)) (= (O_node var4) var3)) (= (write var9 var8 var3) var2)) (= var1 var8)) (= var0 3)))) (inv_main570_3 var2 var0 var8 var1))))
(assert (forall ((var0 AllocResHeap) (var1 Addr) (var2 Addr) (var3 HeapObject) (var4 node) (var5 Addr) (var6 Addr) (var7 Int) (var8 Heap)) (or (not (and (inv_main570_3 var8 var7 var6 var5) (and (and (and (= (O_node var4) var3) (= (node var2 var1) var4)) (not (= 4 4))) (= (alloc var8 var3) var0)))) (Inv_Heap_exp_exp (newAddr var0) var2 var1))))
(assert (forall ((var0 Addr) (var1 AllocResHeap) (var2 Heap) (var3 HeapObject) (var4 node) (var5 HeapObject) (var6 node) (var7 Addr) (var8 Addr) (var9 Int) (var10 Heap) (var11 Addr) (var12 Addr) (var13 Addr)) (or (not (and (and (Inv_Heap_exp_exp var13 var12 var11) (inv_main570_3 var10 var9 var8 var7)) (and (and (and (and (and (and (and (and (and (= (O_node var6) var5) (= (O_node var4) var3)) (= (AllocResHeap var2 var13) var1)) (= (node var12 var11) var6)) (not (= var0 var13))) (= (read var2 var13) var5)) (valid var2 var13)) (not (= 4 4))) (= nullAddr var0)) (= (alloc var10 var3) var1)))) (_Glue3 var7 var9 var13 var2 var5))))
(assert (forall ((var0 AllocResHeap) (var1 HeapObject) (var2 node) (var3 HeapObject) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Int) (var10 Heap)) (or (not (and (inv_main570_3 var10 var9 var8 var7) (and (and (and (and (and (and (and (not (= var6 var5)) (= (read var4 var5) var3)) (not (valid var4 var5))) (= (O_node var2) var1)) (= (AllocResHeap var4 var5) var0)) (not (= 4 4))) (= nullAddr var6)) (= (alloc var10 var1) var0)))) (_Glue3 var7 var9 var5 var4 var3))))
(assert (forall ((var0 Addr) (var1 node) (var2 HeapObject) (var3 Heap) (var4 Addr) (var5 Int) (var6 Addr)) (or (not (and (_Glue3 var6 var5 var4 var3 var2) (and (and (and (is-O_node var2) (= (getnode var2) var1)) (= (|node::prev| var1) var0)) (valid var3 var4)))) (Inv_Heap_exp_exp var4 var6 var0))))
(assert (forall ((var0 node) (var1 Heap) (var2 HeapObject) (var3 node) (var4 Addr) (var5 HeapObject) (var6 node) (var7 HeapObject) (var8 Heap) (var9 Addr) (var10 Int) (var11 Addr) (var12 Addr) (var13 Addr)) (not (and (and (Inv_Heap_exp_exp var13 var12 var11) (_Glue3 var13 var10 var9 var8 var7)) (and (and (and (and (and (and (and (and (and (and (= (O_node var6) var5) (= (node var13 var4) var3)) (= (O_node var3) var2)) (= (node var12 var11) var6)) (= (read var1 var13) var5)) (<= 0 (+ (+ (- 1) var10) (- 1)))) (valid var1 var13)) (is-O_node var7)) (= (getnode var7) var0)) (= (|node::prev| var0) var4)) (= (write var8 var9 var2) var1))))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 node) (var4 HeapObject) (var5 Heap) (var6 HeapObject) (var7 Heap) (var8 Addr) (var9 Int) (var10 Addr)) (not (and (_Glue3 var10 var9 var8 var7 var6) (and (and (and (and (and (and (and (and (and (= (read var5 var10) var4) (is-O_node var4)) (<= 0 (+ (+ (- 1) var9) (- 1)))) (not (valid var5 var10))) (is-O_node var6)) (= (getnode var6) var3)) (= (|node::prev| var3) var2)) (= (node var10 var2) var1)) (= (O_node var1) var0)) (= (write var7 var8 var0) var5))))))
(check-sat)
