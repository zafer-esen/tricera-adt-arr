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
(declare-fun _Glue0 (Addr Addr Heap Addr Int HeapObject) Bool)
(declare-fun _Glue7 (Int Addr Addr Addr Heap HeapObject) Bool)
(declare-fun inv_main552_3 (Heap Addr Addr Int) Bool)
(declare-fun _Glue12 (Int Addr Addr Addr Heap HeapObject) Bool)
(declare-fun Inv_Heap_exp_exp (Addr Int Addr) Bool)
(declare-fun _Glue9_exp_exp (Addr Int Addr Addr Heap Addr Int HeapObject) Bool)
(declare-fun _Glue4_exp_exp (Addr Int Addr Addr Heap Addr Int HeapObject) Bool)
(declare-fun inv_main565_3 (Heap Addr Int Int) Bool)
(declare-fun _Glue2 (Heap Addr Addr Addr HeapObject) Bool)
(assert (forall ((var0 Int) (var1 Addr) (var2 HeapObject) (var3 node) (var4 Int) (var5 Int) (var6 Heap) (var7 Addr) (var8 Addr)) (or (not (and (and (Inv_Heap_exp_exp var8 12 var7) (inv_main565_3 var6 var8 var5 var4)) (and (and (and (and (and (and (= (O_node var3) var2) (= (node 12 var7) var3)) (= nullAddr var1)) (= (read var6 var8) var2)) (not (= var8 var1))) (valid var6 var8)) (= var0 1)))) (inv_main565_3 var6 var7 var5 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 node) (var3 HeapObject) (var4 Addr) (var5 Int) (var6 Int) (var7 Addr) (var8 Heap)) (or (not (and (inv_main565_3 var8 var7 var6 var5) (and (and (and (and (and (and (and (= nullAddr var4) (= (read var8 var7) var3)) (= (getnode var3) var2)) (= (|node::h| var2) 12)) (= (|node::n| var2) var1)) (not (= var7 var4))) (not (valid var8 var7))) (= var0 1)))) (inv_main565_3 var8 var1 var6 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 AllocResHeap) (var3 Heap) (var4 Addr) (var5 Int) (var6 HeapObject) (var7 node)) (or (not (and (and (and (and (and (and (= (O_node var7) var6) (= (node var5 var4) var7)) (= (alloc var3 var6) var2)) (= (newAddr var2) var1)) (not (= var1 var0))) (= nullAddr var0)) (= emptyHeap var3))) (Inv_Heap_exp_exp (newAddr var2) var5 var4))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 AllocResHeap) (var6 Heap) (var7 HeapObject) (var8 node)) (or (not (and (and (and (and (and (and (and (and (= (O_node var8) var7) (= (alloc var6 var7) var5)) (= (newHeap var5) var4)) (= (newAddr var5) var3)) (not (= var3 var2))) (= nullAddr var2)) (= emptyHeap var6)) (= var1 var3)) (= var0 0))) (inv_main552_3 var4 var1 var3 var0))))
(assert (forall ((var0 Addr) (var1 HeapObject) (var2 node) (var3 Int) (var4 Int) (var5 Heap) (var6 Addr) (var7 Int) (var8 Addr)) (or (not (and (and (Inv_Heap_exp_exp var8 var7 var6) (inv_main565_3 var5 var8 var4 var3)) (and (and (and (and (and (and (and (= (O_node var2) var1) (= (node var7 var6) var2)) (= nullAddr var0)) (= (read var5 var8) var1)) (not (= var8 var0))) (not (= var7 2))) (not (= var7 12))) (valid var5 var8)))) (inv_main565_3 var5 var6 var4 var3))))
(assert (forall ((var0 Addr) (var1 Int) (var2 node) (var3 HeapObject) (var4 Addr) (var5 Int) (var6 Int) (var7 Addr) (var8 Heap)) (or (not (and (inv_main565_3 var8 var7 var6 var5) (and (and (and (and (and (and (and (and (= nullAddr var4) (= (read var8 var7) var3)) (= (getnode var3) var2)) (= (|node::h| var2) var1)) (= (|node::n| var2) var0)) (not (= var7 var4))) (not (= var1 2))) (not (= var1 12))) (not (valid var8 var7))))) (inv_main565_3 var8 var0 var6 var5))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 HeapObject) (var4 node) (var5 Int) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Int) (var10 Addr)) (or (not (and (and (Inv_Heap_exp_exp var10 var9 var8) (inv_main552_3 var7 var6 var10 (+ var5 (- 1)))) (and (and (and (and (and (= (O_node var4) var3) (= (node var9 var8) var4)) (= nullAddr var2)) (<= 0 (+ (+ 10 (* (- 1) (+ var5 (- 1)))) (- 1)))) (= (read var7 var10) var3)) (valid var7 var10)))) (_Glue4_exp_exp var2 var1 var0 var6 var7 var10 var5 var3))))
(assert (forall ((var0 Addr) (var1 Int) (var2 HeapObject) (var3 Addr) (var4 Int) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main552_3 var7 var6 var5 (+ var4 (- 1))) (and (and (and (= nullAddr var3) (<= 0 (+ (+ 10 (* (- 1) (+ var4 (- 1)))) (- 1)))) (= (read var7 var5) var2)) (not (valid var7 var5))))) (_Glue4_exp_exp var3 var1 var0 var6 var7 var5 var4 var2))))
(assert (forall ((var0 Addr) (var1 node) (var2 HeapObject) (var3 Int) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Int) (var9 Addr)) (or (not (and (_Glue4_exp_exp var9 var8 var7 var6 var5 var4 (+ var3 1) var2) (and (and (= (getnode var2) var1) (= (|node::n| var1) var0)) (valid var5 var4)))) (Inv_Heap_exp_exp var4 var3 var0))))
(assert (forall ((var0 node) (var1 AllocResHeap) (var2 Heap) (var3 HeapObject) (var4 node) (var5 Addr) (var6 HeapObject) (var7 node) (var8 HeapObject) (var9 Int) (var10 Addr) (var11 Heap) (var12 Addr) (var13 Addr) (var14 Int) (var15 Addr)) (or (not (and (_Glue4_exp_exp var15 var14 var13 var12 var11 var10 var9 var8) (and (and (and (and (and (and (and (= (O_node var7) var6) (= (node (+ var9 (- 1)) var5) var4)) (= (O_node var4) var3)) (= (node var14 var13) var7)) (= (alloc var2 var6) var1)) (= (getnode var8) var0)) (= (|node::n| var0) var5)) (= (write var11 var10 var3) var2)))) (Inv_Heap_exp_exp (newAddr var1) var14 var13))))
(assert (forall ((var0 node) (var1 Heap) (var2 HeapObject) (var3 node) (var4 Addr) (var5 HeapObject) (var6 node) (var7 AllocResHeap) (var8 Addr) (var9 Heap) (var10 HeapObject) (var11 node) (var12 HeapObject) (var13 Int) (var14 Heap) (var15 Addr) (var16 Addr) (var17 Int) (var18 Addr) (var19 Addr) (var20 Int) (var21 Addr)) (or (not (and (and (Inv_Heap_exp_exp var21 var20 var19) (_Glue4_exp_exp var18 var17 var16 var15 var14 var21 var13 var12)) (and (and (and (and (and (and (and (and (and (and (and (and (and (= (O_node var11) var10) (= (AllocResHeap var9 var8) var7)) (= (O_node var6) var5)) (= (node (+ var13 (- 1)) var4) var3)) (= (O_node var3) var2)) (= (node var20 var19) var11)) (= (node var17 var16) var6)) (not (= var8 var18))) (= (read var9 var21) var10)) (valid var9 var21)) (= (alloc var1 var5) var7)) (= (getnode var12) var0)) (= (|node::n| var0) var4)) (= (write var14 var21 var2) var1)))) (_Glue7 var13 var21 var15 var8 var9 var10))))
(assert (forall ((var0 node) (var1 Heap) (var2 HeapObject) (var3 HeapObject) (var4 node) (var5 Addr) (var6 HeapObject) (var7 node) (var8 AllocResHeap) (var9 Addr) (var10 Heap) (var11 HeapObject) (var12 Int) (var13 Addr) (var14 Heap) (var15 Addr) (var16 Addr) (var17 Int) (var18 Addr)) (or (not (and (_Glue4_exp_exp var18 var17 var16 var15 var14 var13 var12 var11) (and (and (and (and (and (and (and (and (and (and (and (= (AllocResHeap var10 var9) var8) (= (O_node var7) var6)) (= (node (+ var12 (- 1)) var5) var4)) (= (O_node var4) var3)) (= (node var17 var16) var7)) (not (= var9 var18))) (= (read var10 var13) var2)) (not (valid var10 var13))) (= (alloc var1 var6) var8)) (= (getnode var11) var0)) (= (|node::n| var0) var5)) (= (write var14 var13 var3) var1)))) (_Glue7 var12 var13 var15 var9 var10 var2))))
(assert (forall ((var0 Int) (var1 node) (var2 HeapObject) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Int)) (or (not (and (_Glue7 var7 var6 var5 var4 var3 var2) (and (and (= (getnode var2) var1) (= (|node::h| var1) var0)) (valid var3 var6)))) (Inv_Heap_exp_exp var6 var0 var4))))
(assert (forall ((var0 node) (var1 Heap) (var2 HeapObject) (var3 node) (var4 Int) (var5 HeapObject) (var6 node) (var7 HeapObject) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Int) (var12 Addr) (var13 Int) (var14 Addr)) (or (not (and (and (Inv_Heap_exp_exp var14 var13 var12) (_Glue7 var11 var14 var10 var9 var8 var7)) (and (and (and (and (and (and (and (and (= (O_node var6) var5) (= (node var4 var9) var3)) (= (O_node var3) var2)) (= (node var13 var12) var6)) (= (read var1 var14) var5)) (valid var1 var14)) (= (getnode var7) var0)) (= (|node::h| var0) var4)) (= (write var8 var14 var2) var1)))) (inv_main552_3 var1 var10 var12 var11))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Int) (var3 node) (var4 Addr) (var5 node) (var6 HeapObject) (var7 Heap) (var8 HeapObject) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Int)) (or (not (and (_Glue7 var13 var12 var11 var10 var9 var8) (and (and (and (and (and (and (and (and (= (read var7 var12) var6) (= (getnode var6) var5)) (= (|node::n| var5) var4)) (not (valid var7 var12))) (= (getnode var8) var3)) (= (|node::h| var3) var2)) (= (node var2 var10) var1)) (= (O_node var1) var0)) (= (write var9 var12 var0) var7)))) (inv_main552_3 var7 var11 var4 var13))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap)) (not (and (inv_main565_3 var2 var1 0 var0) (= nullAddr var1)))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap)) (not (and (inv_main565_3 var2 var1 var0 0) (= nullAddr var1)))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 HeapObject) (var4 node) (var5 Int) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Int) (var10 Addr)) (or (not (and (and (Inv_Heap_exp_exp var10 var9 var8) (inv_main552_3 var7 var6 var10 (+ var5 (- 1)))) (and (and (and (and (and (= (O_node var4) var3) (= (node var9 var8) var4)) (= nullAddr var2)) (not (<= 0 (+ (+ 10 (* (- 1) (+ var5 (- 1)))) (- 1))))) (= (read var7 var10) var3)) (valid var7 var10)))) (_Glue9_exp_exp var2 var1 var0 var6 var7 var10 var5 var3))))
(assert (forall ((var0 Addr) (var1 Int) (var2 HeapObject) (var3 Addr) (var4 Int) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main552_3 var7 var6 var5 (+ var4 (- 1))) (and (and (and (= nullAddr var3) (not (<= 0 (+ (+ 10 (* (- 1) (+ var4 (- 1)))) (- 1))))) (= (read var7 var5) var2)) (not (valid var7 var5))))) (_Glue9_exp_exp var3 var1 var0 var6 var7 var5 var4 var2))))
(assert (forall ((var0 Addr) (var1 node) (var2 HeapObject) (var3 Int) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Int) (var9 Addr)) (or (not (and (_Glue9_exp_exp var9 var8 var7 var6 var5 var4 (+ var3 1) var2) (and (and (= (getnode var2) var1) (= (|node::n| var1) var0)) (valid var5 var4)))) (Inv_Heap_exp_exp var4 var3 var0))))
(assert (forall ((var0 node) (var1 AllocResHeap) (var2 Heap) (var3 HeapObject) (var4 node) (var5 Addr) (var6 HeapObject) (var7 node) (var8 HeapObject) (var9 Int) (var10 Addr) (var11 Heap) (var12 Addr) (var13 Addr) (var14 Int) (var15 Addr)) (or (not (and (_Glue9_exp_exp var15 var14 var13 var12 var11 var10 var9 var8) (and (and (and (and (and (and (and (= (O_node var7) var6) (= (node (+ var9 (- 1)) var5) var4)) (= (O_node var4) var3)) (= (node var14 var13) var7)) (= (alloc var2 var6) var1)) (= (getnode var8) var0)) (= (|node::n| var0) var5)) (= (write var11 var10 var3) var2)))) (Inv_Heap_exp_exp (newAddr var1) var14 var13))))
(assert (forall ((var0 node) (var1 Heap) (var2 HeapObject) (var3 node) (var4 Addr) (var5 HeapObject) (var6 node) (var7 AllocResHeap) (var8 Addr) (var9 Heap) (var10 HeapObject) (var11 node) (var12 HeapObject) (var13 Int) (var14 Heap) (var15 Addr) (var16 Addr) (var17 Int) (var18 Addr) (var19 Addr) (var20 Int) (var21 Addr)) (or (not (and (and (Inv_Heap_exp_exp var21 var20 var19) (_Glue9_exp_exp var18 var17 var16 var15 var14 var21 var13 var12)) (and (and (and (and (and (and (and (and (and (and (and (and (and (= (O_node var11) var10) (= (AllocResHeap var9 var8) var7)) (= (O_node var6) var5)) (= (node (+ var13 (- 1)) var4) var3)) (= (O_node var3) var2)) (= (node var20 var19) var11)) (= (node var17 var16) var6)) (not (= var8 var18))) (= (read var9 var21) var10)) (valid var9 var21)) (= (alloc var1 var5) var7)) (= (getnode var12) var0)) (= (|node::n| var0) var4)) (= (write var14 var21 var2) var1)))) (_Glue12 var13 var21 var15 var8 var9 var10))))
(assert (forall ((var0 node) (var1 Heap) (var2 HeapObject) (var3 HeapObject) (var4 node) (var5 Addr) (var6 HeapObject) (var7 node) (var8 AllocResHeap) (var9 Addr) (var10 Heap) (var11 HeapObject) (var12 Int) (var13 Addr) (var14 Heap) (var15 Addr) (var16 Addr) (var17 Int) (var18 Addr)) (or (not (and (_Glue9_exp_exp var18 var17 var16 var15 var14 var13 var12 var11) (and (and (and (and (and (and (and (and (and (and (and (= (AllocResHeap var10 var9) var8) (= (O_node var7) var6)) (= (node (+ var12 (- 1)) var5) var4)) (= (O_node var4) var3)) (= (node var17 var16) var7)) (not (= var9 var18))) (= (read var10 var13) var2)) (not (valid var10 var13))) (= (alloc var1 var6) var8)) (= (getnode var11) var0)) (= (|node::n| var0) var5)) (= (write var14 var13 var3) var1)))) (_Glue12 var12 var13 var15 var9 var10 var2))))
(assert (forall ((var0 Int) (var1 node) (var2 HeapObject) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Int)) (or (not (and (_Glue12 var7 var6 var5 var4 var3 var2) (and (and (= (getnode var2) var1) (= (|node::h| var1) var0)) (valid var3 var6)))) (Inv_Heap_exp_exp var6 var0 var4))))
(assert (forall ((var0 node) (var1 Heap) (var2 HeapObject) (var3 node) (var4 Int) (var5 HeapObject) (var6 node) (var7 HeapObject) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Int) (var12 Addr) (var13 Int) (var14 Addr)) (or (not (and (and (Inv_Heap_exp_exp var14 var13 var12) (_Glue12 var11 var14 var10 var9 var8 var7)) (and (and (and (and (and (and (and (and (= (O_node var6) var5) (= (node var4 var9) var3)) (= (O_node var3) var2)) (= (node var13 var12) var6)) (= (read var1 var14) var5)) (valid var1 var14)) (= (getnode var7) var0)) (= (|node::h| var0) var4)) (= (write var8 var14 var2) var1)))) (inv_main552_3 var1 var10 var12 var11))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Int) (var3 node) (var4 Addr) (var5 node) (var6 HeapObject) (var7 Heap) (var8 HeapObject) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Int)) (or (not (and (_Glue12 var13 var12 var11 var10 var9 var8) (and (and (and (and (and (and (and (and (= (read var7 var12) var6) (= (getnode var6) var5)) (= (|node::n| var5) var4)) (not (valid var7 var12))) (= (getnode var8) var3)) (= (|node::h| var3) var2)) (= (node var2 var10) var1)) (= (O_node var1) var0)) (= (write var9 var12 var0) var7)))) (inv_main552_3 var7 var11 var4 var13))))
(assert (forall ((var0 Int) (var1 Addr) (var2 HeapObject) (var3 node) (var4 Int) (var5 Int) (var6 Heap) (var7 Addr) (var8 Addr)) (or (not (and (and (Inv_Heap_exp_exp var8 2 var7) (inv_main565_3 var6 var8 var5 var4)) (and (and (and (and (and (and (= (O_node var3) var2) (= (node 2 var7) var3)) (= nullAddr var1)) (= (read var6 var8) var2)) (not (= var8 var1))) (valid var6 var8)) (= var0 1)))) (inv_main565_3 var6 var7 var0 var4))))
(assert (forall ((var0 Int) (var1 Addr) (var2 node) (var3 HeapObject) (var4 Addr) (var5 Int) (var6 Int) (var7 Addr) (var8 Heap)) (or (not (and (inv_main565_3 var8 var7 var6 var5) (and (and (and (and (and (and (and (= nullAddr var4) (= (read var8 var7) var3)) (= (getnode var3) var2)) (= (|node::h| var2) 2)) (= (|node::n| var2) var1)) (not (= var7 var4))) (not (valid var8 var7))) (= var0 1)))) (inv_main565_3 var8 var1 var0 var5))))
(assert (forall ((var0 Addr) (var1 HeapObject) (var2 node) (var3 Int) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Int) (var8 Addr)) (or (not (and (and (Inv_Heap_exp_exp var8 var7 var6) (inv_main552_3 var5 var4 var8 var3)) (and (and (and (and (= (O_node var2) var1) (= (node var7 var6) var2)) (not (<= 0 (+ (+ 10 (* (- 1) var3)) (- 1))))) (= (read var5 var8) var1)) (valid var5 var8)))) (_Glue0 var0 var4 var5 var8 var3 var1))))
(assert (forall ((var0 Addr) (var1 HeapObject) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main552_3 var5 var4 var3 var2) (and (and (not (<= 0 (+ (+ 10 (* (- 1) var2)) (- 1)))) (= (read var5 var3) var1)) (not (valid var5 var3))))) (_Glue0 var0 var4 var5 var3 var2 var1))))
(assert (forall ((var0 Addr) (var1 node) (var2 HeapObject) (var3 Int) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr)) (or (not (and (_Glue0 var7 var6 var5 var4 var3 var2) (and (and (= (getnode var2) var1) (= (|node::n| var1) var0)) (valid var5 var4)))) (Inv_Heap_exp_exp var4 var3 var0))))
(assert (forall ((var0 node) (var1 Heap) (var2 HeapObject) (var3 node) (var4 Addr) (var5 HeapObject) (var6 node) (var7 HeapObject) (var8 Int) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Int) (var14 Addr)) (or (not (and (and (Inv_Heap_exp_exp var14 var13 var12) (_Glue0 var11 var10 var9 var14 var8 var7)) (and (and (and (and (and (and (and (and (= (O_node var6) var5) (= (node var8 var4) var3)) (= (O_node var3) var2)) (= (node var13 var12) var6)) (= (read var1 var14) var5)) (valid var1 var14)) (= (getnode var7) var0)) (= (|node::n| var0) var4)) (= (write var9 var14 var2) var1)))) (_Glue2 var1 var11 var10 var14 var5))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 node) (var4 HeapObject) (var5 Heap) (var6 HeapObject) (var7 Int) (var8 Addr) (var9 Heap) (var10 Addr) (var11 Addr)) (or (not (and (_Glue0 var11 var10 var9 var8 var7 var6) (and (and (and (and (and (and (= (read var5 var8) var4) (not (valid var5 var8))) (= (getnode var6) var3)) (= (|node::n| var3) var2)) (= (node var7 var2) var1)) (= (O_node var1) var0)) (= (write var9 var8 var0) var5)))) (_Glue2 var5 var11 var10 var8 var4))))
(assert (forall ((var0 Addr) (var1 Int) (var2 node) (var3 HeapObject) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (_Glue2 var6 var5 var5 var4 var3) (and (and (and (= (getnode var3) var2) (= (|node::h| var2) var1)) (valid var6 var4)) (= var0 0)))) (Inv_Heap_exp_exp var4 var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Heap) (var3 HeapObject) (var4 node) (var5 Int) (var6 node) (var7 HeapObject) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (_Glue2 var10 var9 var9 var8 var7) (and (and (and (and (and (and (= (getnode var7) var6) (= (|node::h| var6) var5)) (= (node var5 0) var4)) (= (O_node var4) var3)) (= (write var10 var8 var3) var2)) (= var1 0)) (= var0 0)))) (inv_main565_3 var2 var9 var0 var1))))
(check-sat)
