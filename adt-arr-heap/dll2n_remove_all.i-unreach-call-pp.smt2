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
   (node (|node::data| Int) (|node::next| Addr) (|node::prev| Addr))
  )
))
(declare-fun _Glue0 (Addr Int Heap Addr HeapObject) Bool)
(declare-fun _Glue6 (Addr Int Heap) Bool)
(declare-fun _Glue11 (Addr Int Addr Heap HeapObject) Bool)
(declare-fun Inv_Heap (Addr HeapObject) Bool)
(declare-fun inv_main616_7 (Heap Addr Int) Bool)
(declare-fun _Glue7 (Heap Int Addr HeapObject) Bool)
(declare-fun inv_main586_3 (Heap Int Addr) Bool)
(declare-fun _Glue1 (Int Heap Addr HeapObject) Bool)
(declare-fun _Glue15 (Heap Addr Int Addr HeapObject) Bool)
(declare-fun _Glue5 (Int Addr Heap HeapObject) Bool)
(declare-fun _Glue17 (Heap Addr Int Addr HeapObject) Bool)
(declare-fun _Glue8 (Addr Int Addr Heap) Bool)
(declare-fun _Glue13 (Heap Addr Int Addr HeapObject) Bool)
(declare-fun _Glue2 (Addr Heap Int Addr HeapObject) Bool)
(declare-fun _Glue9 (Heap Addr Int Addr HeapObject) Bool)
(assert (forall ((var0 AllocResHeap) (var1 HeapObject) (var2 node) (var3 Addr) (var4 Int) (var5 Heap)) (or (not (and (inv_main586_3 var5 (+ var4 1) var3) (and (= (O_node var2) var1) (= (alloc var5 var1) var0)))) (Inv_Heap (newAddr var0) var1))))
(assert (forall ((var0 AllocResHeap) (var1 HeapObject) (var2 node) (var3 Heap) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Int) (var8 Heap) (var9 HeapObject) (var10 Addr)) (or (not (and (and (and (Inv_Heap var10 var9) (inv_main586_3 var8 (+ var7 1) var6)) (inv_main586_3 var5 (+ var7 1) var4)) (and (and (and (and (and (and (= (read var3 var10) var9) (valid var3 var10)) true) (= (O_node var2) var1)) (= (AllocResHeap var3 var10) var0)) (= (alloc var8 var1) var0)) true))) (_Glue5 var7 var10 var3 var9))))
(assert (forall ((var0 AllocResHeap) (var1 HeapObject) (var2 node) (var3 HeapObject) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Int) (var10 Heap)) (or (not (and (and (inv_main586_3 var10 (+ var9 1) var8) (inv_main586_3 var7 (+ var9 1) var6)) (and (and (and (and (and (= (read var5 var4) var3) (not (valid var5 var4))) (= (O_node var2) var1)) (= (AllocResHeap var5 var4) var0)) (= (alloc var10 var1) var0)) true))) (_Glue5 var9 var4 var5 var3))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Addr) (var4 node) (var5 Addr) (var6 Heap) (var7 HeapObject) (var8 Heap) (var9 Addr) (var10 Int)) (or (not (and (and (_Glue5 var10 var9 var8 var7) (inv_main586_3 var6 (+ var10 1) var5)) (and (and (and (and (and (= (getnode var7) var4) (= (|node::next| var4) var3)) (= (|node::prev| var4) var2)) (= (node 1 var3 var2) var1)) (= (O_node var1) var0)) (valid var8 var9)))) (Inv_Heap var9 var0))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 node) (var3 Addr) (var4 Addr) (var5 node) (var6 Addr) (var7 Heap) (var8 HeapObject) (var9 Heap) (var10 Addr) (var11 Int)) (or (not (and (and (_Glue5 var11 var10 var9 var8) (inv_main586_3 var7 (+ var11 1) var6)) (and (and (and (and (and (= (getnode var8) var5) (= (|node::next| var5) var4)) (= (|node::prev| var5) var3)) (= (node 1 var4 var3) var2)) (= (O_node var2) var1)) (= (write var9 var10 var1) var0)))) (_Glue6 var10 var11 var0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Heap) (var3 Int) (var4 HeapObject) (var5 Addr)) (or (not (and (and (and (Inv_Heap var5 var4) (_Glue6 var5 var3 var2)) (inv_main586_3 var1 (+ var3 1) var0)) (and (= (read var2 var5) var4) (valid var2 var5)))) (_Glue7 var2 var3 var5 var4))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Heap) (var3 Heap) (var4 Int) (var5 Addr)) (or (not (and (and (_Glue6 var5 var4 var3) (inv_main586_3 var2 (+ var4 1) var1)) (and (= (read var3 var5) var0) (not (valid var3 var5))))) (_Glue7 var3 var4 var5 var0))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Int) (var4 node) (var5 Addr) (var6 Heap) (var7 HeapObject) (var8 Addr) (var9 Int) (var10 Heap)) (or (not (and (and (_Glue7 var10 var9 var8 var7) (inv_main586_3 var6 (+ var9 1) var5)) (and (and (and (and (and (and (and (and (= (getnode var7) var4) (= (|node::data| var4) var3)) (= (|node::prev| var4) var2)) (<= 0 (+ (+ var9 1) (- 1)))) (= nullAddr var5)) (not (= var5 var8))) (= (node var3 var5 var2) var1)) (= (O_node var1) var0)) (valid var10 var8)))) (Inv_Heap var8 var0))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 node) (var3 Addr) (var4 Int) (var5 node) (var6 Addr) (var7 Heap) (var8 HeapObject) (var9 Addr) (var10 Int) (var11 Heap)) (or (not (and (and (_Glue7 var11 var10 var9 var8) (inv_main586_3 var7 (+ var10 1) var6)) (and (and (and (and (and (and (and (and (= (getnode var8) var5) (= (|node::data| var5) var4)) (= (|node::prev| var5) var3)) (<= 0 (+ (+ var10 1) (- 1)))) (= nullAddr var6)) (not (= var6 var9))) (= (node var4 var6 var3) var2)) (= (O_node var2) var1)) (= (write var11 var9 var1) var0)))) (_Glue8 var9 var10 var6 var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Int) (var3 HeapObject) (var4 Addr)) (or (not (and (and (Inv_Heap var4 var3) (_Glue8 var4 var2 var1 var0)) (and (= (read var0 var4) var3) (valid var0 var4)))) (_Glue9 var0 var1 var2 var4 var3))))
(assert (forall ((var0 HeapObject) (var1 Heap) (var2 Addr) (var3 Int) (var4 Addr)) (or (not (and (_Glue8 var4 var3 var2 var1) (and (= (read var1 var4) var0) (not (valid var1 var4))))) (_Glue9 var1 var2 var3 var4 var0))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Int) (var4 node) (var5 HeapObject) (var6 Addr) (var7 Int) (var8 Addr) (var9 Heap)) (or (not (and (_Glue9 var9 var8 var7 var6 var5) (and (and (and (and (and (= (getnode var5) var4) (= (|node::data| var4) var3)) (= (|node::next| var4) var2)) (= (node var3 var2 var8) var1)) (= (O_node var1) var0)) (valid var9 var6)))) (Inv_Heap var6 var0))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 node) (var3 Addr) (var4 Int) (var5 node) (var6 HeapObject) (var7 Addr) (var8 Int) (var9 Addr) (var10 Heap)) (or (not (and (_Glue9 var10 var9 var8 var7 var6) (and (and (and (and (and (= (getnode var6) var5) (= (|node::data| var5) var4)) (= (|node::next| var5) var3)) (= (node var4 var3 var9) var2)) (= (O_node var2) var1)) (= (write var10 var7 var1) var0)))) (inv_main586_3 var0 var8 var7))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Heap)) (not (and (inv_main616_7 var3 var2 var1) (and (and (not (<= 0 var1)) (not (= var0 var2))) (= nullAddr var0))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Heap)) (or (not (and (inv_main586_3 var3 var2 var1) (and (not (<= 0 (+ var2 (- 1)))) (= var0 1)))) (inv_main616_7 var3 var1 var0))))
(assert (forall ((var0 AllocResHeap) (var1 HeapObject) (var2 node) (var3 Addr) (var4 Int) (var5 Heap)) (or (not (and (inv_main586_3 var5 (+ var4 1) var3) (and (= (O_node var2) var1) (= (alloc var5 var1) var0)))) (Inv_Heap (newAddr var0) var1))))
(assert (forall ((var0 AllocResHeap) (var1 HeapObject) (var2 node) (var3 Heap) (var4 Addr) (var5 Int) (var6 Heap) (var7 HeapObject) (var8 Addr)) (or (not (and (and (Inv_Heap var8 var7) (inv_main586_3 var6 (+ var5 1) var4)) (and (and (and (and (and (= (read var3 var8) var7) (valid var3 var8)) true) (= (O_node var2) var1)) (= (AllocResHeap var3 var8) var0)) (= (alloc var6 var1) var0)))) (_Glue11 var4 var5 var8 var3 var7))))
(assert (forall ((var0 AllocResHeap) (var1 HeapObject) (var2 node) (var3 HeapObject) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Int) (var8 Heap)) (or (not (and (inv_main586_3 var8 (+ var7 1) var6) (and (and (and (and (= (read var5 var4) var3) (not (valid var5 var4))) (= (O_node var2) var1)) (= (AllocResHeap var5 var4) var0)) (= (alloc var8 var1) var0)))) (_Glue11 var6 var7 var4 var5 var3))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Addr) (var4 node) (var5 HeapObject) (var6 Heap) (var7 Addr) (var8 Int) (var9 Addr)) (or (not (and (_Glue11 var9 var8 var7 var6 var5) (and (and (and (and (and (= (getnode var5) var4) (= (|node::next| var4) var3)) (= (|node::prev| var4) var2)) (= (node 1 var3 var2) var1)) (= (O_node var1) var0)) (valid var6 var7)))) (Inv_Heap var7 var0))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Addr) (var4 node) (var5 Heap) (var6 HeapObject) (var7 Heap) (var8 Int) (var9 Addr) (var10 HeapObject) (var11 Addr)) (or (not (and (and (Inv_Heap var11 var10) (_Glue11 var9 var8 var11 var7 var6)) (and (and (and (and (and (and (and (and (= (read var5 var11) var10) (valid var5 var11)) true) (= (getnode var6) var4)) (= (|node::next| var4) var3)) (= (|node::prev| var4) var2)) (= (node 1 var3 var2) var1)) (= (O_node var1) var0)) (= (write var7 var11 var0) var5)))) (_Glue13 var5 var9 var8 var11 var10))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Addr) (var4 node) (var5 HeapObject) (var6 Heap) (var7 HeapObject) (var8 Heap) (var9 Addr) (var10 Int) (var11 Addr)) (or (not (and (_Glue11 var11 var10 var9 var8 var7) (and (and (and (and (and (and (and (= (read var6 var9) var5) (not (valid var6 var9))) (= (getnode var7) var4)) (= (|node::next| var4) var3)) (= (|node::prev| var4) var2)) (= (node 1 var3 var2) var1)) (= (O_node var1) var0)) (= (write var8 var9 var0) var6)))) (_Glue13 var6 var11 var10 var9 var5))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Int) (var4 node) (var5 HeapObject) (var6 Addr) (var7 Int) (var8 Addr) (var9 Heap)) (or (not (and (_Glue13 var9 var8 var7 var6 var5) (and (and (and (and (and (= (getnode var5) var4) (= (|node::data| var4) var3)) (= (|node::prev| var4) var2)) (= (node var3 var8 var2) var1)) (= (O_node var1) var0)) (valid var9 var6)))) (Inv_Heap var6 var0))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Int) (var4 node) (var5 Heap) (var6 HeapObject) (var7 Int) (var8 Addr) (var9 Heap) (var10 HeapObject) (var11 Addr)) (or (not (and (and (Inv_Heap var11 var10) (_Glue13 var9 var8 var7 var11 var6)) (and (and (and (and (and (and (and (and (= (read var5 var11) var10) (valid var5 var11)) true) (= (getnode var6) var4)) (= (|node::data| var4) var3)) (= (|node::prev| var4) var2)) (= (node var3 var8 var2) var1)) (= (O_node var1) var0)) (= (write var9 var11 var0) var5)))) (_Glue15 var5 var8 var7 var11 var10))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Int) (var4 node) (var5 HeapObject) (var6 Heap) (var7 HeapObject) (var8 Addr) (var9 Int) (var10 Addr) (var11 Heap)) (or (not (and (_Glue13 var11 var10 var9 var8 var7) (and (and (and (and (and (and (and (= (read var6 var8) var5) (not (valid var6 var8))) (= (getnode var7) var4)) (= (|node::data| var4) var3)) (= (|node::prev| var4) var2)) (= (node var3 var10 var2) var1)) (= (O_node var1) var0)) (= (write var11 var8 var0) var6)))) (_Glue15 var6 var10 var9 var8 var5))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Addr) (var4 Int) (var5 node) (var6 HeapObject) (var7 Addr) (var8 Int) (var9 Addr) (var10 Heap)) (or (not (and (_Glue15 var10 var9 var8 var7 var6) (and (and (and (and (and (and (and (and (and (= (getnode var6) var5) (= (|node::data| var5) var4)) (= (|node::next| var5) var3)) (<= 0 (+ (+ var8 1) (- 1)))) (= nullAddr var2)) (not (= var9 var2))) (not (= var2 var7))) (= (node var4 var3 var2) var1)) (= (O_node var1) var0)) (valid var10 var7)))) (Inv_Heap var7 var0))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Addr) (var4 Int) (var5 node) (var6 Heap) (var7 HeapObject) (var8 Addr) (var9 Int) (var10 Heap) (var11 HeapObject) (var12 Addr)) (or (not (and (and (Inv_Heap var12 var11) (_Glue15 var10 var12 var9 var8 var7)) (and (and (and (and (and (and (and (and (and (and (and (and (= (read var6 var12) var11) (valid var6 var12)) true) (= (getnode var7) var5)) (= (|node::data| var5) var4)) (= (|node::next| var5) var3)) (<= 0 (+ (+ var9 1) (- 1)))) (= nullAddr var2)) (not (= var12 var2))) (not (= var2 var8))) (= (node var4 var3 var2) var1)) (= (O_node var1) var0)) (= (write var10 var8 var0) var6)))) (_Glue17 var6 var12 var9 var8 var11))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Addr) (var4 Int) (var5 node) (var6 HeapObject) (var7 Heap) (var8 HeapObject) (var9 Addr) (var10 Int) (var11 Addr) (var12 Heap)) (or (not (and (_Glue15 var12 var11 var10 var9 var8) (and (and (and (and (and (and (and (and (and (and (and (= (read var7 var11) var6) (not (valid var7 var11))) (= (getnode var8) var5)) (= (|node::data| var5) var4)) (= (|node::next| var5) var3)) (<= 0 (+ (+ var10 1) (- 1)))) (= nullAddr var2)) (not (= var11 var2))) (not (= var2 var9))) (= (node var4 var3 var2) var1)) (= (O_node var1) var0)) (= (write var12 var9 var0) var7)))) (_Glue17 var7 var11 var10 var9 var6))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Int) (var4 node) (var5 HeapObject) (var6 Addr) (var7 Int) (var8 Addr) (var9 Heap)) (or (not (and (_Glue17 var9 var8 var7 var6 var5) (and (and (and (and (and (= (getnode var5) var4) (= (|node::data| var4) var3)) (= (|node::next| var4) var2)) (= (node var3 var2 var6) var1)) (= (O_node var1) var0)) (valid var9 var8)))) (Inv_Heap var8 var0))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 node) (var3 Addr) (var4 Int) (var5 node) (var6 HeapObject) (var7 Addr) (var8 Int) (var9 Addr) (var10 Heap)) (or (not (and (_Glue17 var10 var9 var8 var7 var6) (and (and (and (and (and (= (getnode var6) var5) (= (|node::data| var5) var4)) (= (|node::next| var5) var3)) (= (node var4 var3 var7) var2)) (= (O_node var2) var1)) (= (write var10 var9 var1) var0)))) (inv_main586_3 var0 var8 var7))))
(assert (forall ((var0 Int) (var1 Heap) (var2 Addr)) (or (not (and (and (= nullAddr var2) (= emptyHeap var1)) (= var0 2))) (inv_main586_3 var1 var0 var2))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Heap) (var3 HeapObject) (var4 Addr)) (or (not (and (and (Inv_Heap var4 var3) (inv_main616_7 var2 var4 (+ var1 1))) (and (and (= nullAddr var0) (= (read var2 var4) var3)) (valid var2 var4)))) (_Glue0 var0 var1 var2 var4 var3))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Int) (var3 Addr) (var4 Heap)) (or (not (and (inv_main616_7 var4 var3 (+ var2 1)) (and (and (= nullAddr var1) (= (read var4 var3) var0)) (not (valid var4 var3))))) (_Glue0 var1 var2 var4 var3 var0))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 HeapObject) (var3 Addr) (var4 Heap) (var5 Int) (var6 Addr)) (or (not (and (_Glue0 var6 var5 var4 var3 var2) (and (and (and (and (= (getnode var2) var1) (= (|node::next| var1) var6)) (<= 0 (+ var5 1))) (= defObj var0)) (valid var4 var3)))) (Inv_Heap var3 var0))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 node) (var3 HeapObject) (var4 Addr) (var5 Heap) (var6 Int) (var7 Addr)) (or (not (and (_Glue0 var7 var6 var5 var4 var3) (and (and (and (and (= (getnode var3) var2) (= (|node::next| var2) var7)) (<= 0 (+ var6 1))) (= defObj var1)) (= (write var5 var4 var1) var0)))) (inv_main616_7 var0 var7 var6))))
(assert (forall ((var0 Int) (var1 Heap) (var2 HeapObject) (var3 Addr)) (or (not (and (and (Inv_Heap var3 var2) (inv_main616_7 var1 var3 (+ var0 1))) (and (= (read var1 var3) var2) (valid var1 var3)))) (_Glue1 var0 var1 var3 var2))))
(assert (forall ((var0 HeapObject) (var1 Int) (var2 Addr) (var3 Heap)) (or (not (and (inv_main616_7 var3 var2 (+ var1 1)) (and (= (read var3 var2) var0) (not (valid var3 var2))))) (_Glue1 var1 var3 var2 var0))))
(assert (forall ((var0 node) (var1 HeapObject) (var2 Addr) (var3 Heap) (var4 Int) (var5 HeapObject) (var6 Addr)) (or (not (and (and (Inv_Heap var6 var5) (_Glue1 var4 var3 var2 var1)) (and (and (and (= (getnode var1) var0) (= (|node::next| var0) var6)) (= (read var3 var6) var5)) (valid var3 var6)))) (_Glue2 var2 var3 var4 var6 var5))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 node) (var3 HeapObject) (var4 Addr) (var5 Heap) (var6 Int)) (or (not (and (_Glue1 var6 var5 var4 var3) (and (and (and (= (getnode var3) var2) (= (|node::next| var2) var1)) (= (read var5 var1) var0)) (not (valid var5 var1))))) (_Glue2 var4 var5 var6 var1 var0))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Addr) (var4 Int) (var5 node) (var6 HeapObject) (var7 Addr) (var8 Int) (var9 Heap) (var10 Addr)) (or (not (and (_Glue2 var10 var9 var8 var7 var6) (and (and (and (and (and (and (and (and (= (getnode var6) var5) (= (|node::data| var5) var4)) (= (|node::next| var5) var3)) (<= 0 (+ var8 1))) (= nullAddr var2)) (not (= var7 var2))) (= (node var4 var3 var2) var1)) (= (O_node var1) var0)) (valid var9 var7)))) (Inv_Heap var7 var0))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Addr) (var4 Int) (var5 node) (var6 Heap) (var7 HeapObject) (var8 HeapObject) (var9 Addr) (var10 Int) (var11 Heap) (var12 Addr)) (or (not (and (_Glue2 var12 var11 var10 var9 var8) (and (and (and (and (and (and (and (and (and (and (= defObj var7) (valid var6 var12)) (= (getnode var8) var5)) (= (|node::data| var5) var4)) (= (|node::next| var5) var3)) (<= 0 (+ var10 1))) (= nullAddr var2)) (not (= var9 var2))) (= (node var4 var3 var2) var1)) (= (O_node var1) var0)) (= (write var11 var9 var0) var6)))) (Inv_Heap var12 var7))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Addr) (var4 Int) (var5 node) (var6 Heap) (var7 Heap) (var8 HeapObject) (var9 HeapObject) (var10 Addr) (var11 Int) (var12 Heap) (var13 Addr)) (or (not (and (_Glue2 var13 var12 var11 var10 var9) (and (and (and (and (and (and (and (and (and (and (= defObj var8) (= (write var7 var13 var8) var6)) (= (getnode var9) var5)) (= (|node::data| var5) var4)) (= (|node::next| var5) var3)) (<= 0 (+ var11 1))) (= nullAddr var2)) (not (= var10 var2))) (= (node var4 var3 var2) var1)) (= (O_node var1) var0)) (= (write var12 var10 var0) var7)))) (inv_main616_7 var6 var10 var11))))
(check-sat)