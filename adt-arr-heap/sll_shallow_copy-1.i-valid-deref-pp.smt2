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
   (node (|node::next| Addr))
  )
))
(declare-fun Inv_Heap_exp_exp (Addr Addr) Bool)
(declare-fun _Glue22 (Heap Heap Addr HeapObject) Bool)
(declare-fun _Glue12 (Heap Addr HeapObject) Bool)
(declare-fun _Glue17 (Heap Addr HeapObject) Bool)
(declare-fun _Glue24 (Heap Addr HeapObject) Bool)
(declare-fun _Glue7 (Heap Addr HeapObject) Bool)
(assert (forall ((var0 AllocResHeap) (var1 Heap) (var2 Addr) (var3 HeapObject) (var4 node)) (or (not (and (and (and (and (= (O_node var4) var3) (= (node var2) var4)) (= (alloc var1 var3) var0)) (not (= 4 4))) (= emptyHeap var1))) (Inv_Heap_exp_exp (newAddr var0) var2))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 AllocResHeap) (var3 Addr) (var4 HeapObject) (var5 node) (var6 AllocResHeap) (var7 Addr) (var8 Heap) (var9 HeapObject) (var10 node)) (or (not (and (and (and (and (and (and (and (and (and (= (O_node var10) var9) (= (AllocResHeap var8 var7) var6)) (= (O_node var5) var4)) (= (node var3) var10)) (= (alloc var8 var9) var2)) (not (= var1 var7))) (= (alloc var0 var4) var6)) (not (= 4 4))) (= nullAddr var1)) (= emptyHeap var0))) (Inv_Heap_exp_exp (newAddr var2) var3))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 HeapObject) (var3 node) (var4 AllocResHeap) (var5 Addr) (var6 Heap) (var7 HeapObject) (var8 node) (var9 AllocResHeap) (var10 Addr) (var11 Heap)) (or (not (and (and (and (and (and (and (and (and (and (and (and (= (AllocResHeap var11 var10) var9) (= (O_node var8) var7)) (= (AllocResHeap var6 var5) var4)) (= (O_node var3) var2)) (not (= var1 var10))) (valid var11 var5)) (not (= var1 var5))) (= (alloc var6 var7) var9)) (= (alloc var0 var2) var4)) (not (= 4 4))) (= nullAddr var1)) (= emptyHeap var0))) (Inv_Heap_exp_exp var5 var10))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Heap) (var3 HeapObject) (var4 node) (var5 AllocResHeap) (var6 Heap) (var7 HeapObject) (var8 node) (var9 AllocResHeap) (var10 Heap) (var11 HeapObject) (var12 node) (var13 Addr) (var14 HeapObject) (var15 node) (var16 Addr) (var17 Addr)) (or (not (and (Inv_Heap_exp_exp var17 var16) (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (= (O_node var15) var14) (= (node var13) var12)) (= (O_node var12) var11)) (= (AllocResHeap var10 var13) var9)) (= (O_node var8) var7)) (= (AllocResHeap var6 var17) var5)) (= (O_node var4) var3)) (= (node var16) var15)) (= (read var2 var17) var14)) (valid var2 var17)) (not (= var1 var13))) (= (write var10 var17 var11) var2)) (not (= var1 var17))) (= (alloc var6 var7) var9)) (= (alloc var0 var3) var5)) (not (= 4 4))) (= nullAddr var1)) (= emptyHeap var0)))) (_Glue12 var10 var17 var14))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 node) (var3 AllocResHeap) (var4 Heap) (var5 HeapObject) (var6 node) (var7 AllocResHeap) (var8 Heap) (var9 Addr) (var10 HeapObject) (var11 node) (var12 Addr) (var13 HeapObject) (var14 Addr) (var15 Heap)) (or (not (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (= (read var15 var14) var13) (not (valid var15 var14))) (= (node var12) var11)) (= (O_node var11) var10)) (not (= var9 var12))) (= (write var8 var14 var10) var15)) (= (AllocResHeap var8 var12) var7)) (= (O_node var6) var5)) (not (= var9 var14))) (= (alloc var4 var5) var7)) (= (AllocResHeap var4 var14) var3)) (= (O_node var2) var1)) (= (alloc var0 var1) var3)) (not (= 4 4))) (= nullAddr var9)) (= emptyHeap var0))) (_Glue12 var8 var14 var13))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 HeapObject) (var3 Heap) (var4 Addr) (var5 Addr)) (not (and (and (Inv_Heap_exp_exp var5 var4) (_Glue12 var3 var5 var2)) (and (and (and (and (= (O_node var1) var0) (= (node var4) var1)) (is-O_node var2)) (= (read var3 var5) var0)) (valid var3 var5))))))
(assert (forall ((var0 HeapObject) (var1 HeapObject) (var2 Addr) (var3 Heap)) (not (and (_Glue12 var3 var2 var1) (and (and (and (is-O_node var1) (= (read var3 var2) var0)) (is-O_node var0)) (not (valid var3 var2)))))))
(assert (forall ((var0 AllocResHeap) (var1 Heap) (var2 Addr) (var3 HeapObject) (var4 node)) (or (not (and (and (and (= (O_node var4) var3) (= (node var2) var4)) (= (alloc var1 var3) var0)) (= emptyHeap var1))) (Inv_Heap_exp_exp (newAddr var0) var2))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 AllocResHeap) (var3 Addr) (var4 HeapObject) (var5 node) (var6 AllocResHeap) (var7 Addr) (var8 Heap) (var9 HeapObject) (var10 node)) (or (not (and (and (and (and (and (and (and (and (= (O_node var10) var9) (= (AllocResHeap var8 var7) var6)) (= (O_node var5) var4)) (= (node var3) var10)) (= (alloc var8 var9) var2)) (not (= var1 var7))) (= (alloc var0 var4) var6)) (= nullAddr var1)) (= emptyHeap var0))) (Inv_Heap_exp_exp (newAddr var2) var3))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 HeapObject) (var3 node) (var4 AllocResHeap) (var5 Addr) (var6 Heap) (var7 HeapObject) (var8 node) (var9 AllocResHeap) (var10 Addr) (var11 Heap)) (or (not (and (and (and (and (and (and (and (and (and (and (= (AllocResHeap var11 var10) var9) (= (O_node var8) var7)) (= (AllocResHeap var6 var5) var4)) (= (O_node var3) var2)) (not (= var1 var10))) (valid var11 var5)) (not (= var1 var5))) (= (alloc var6 var7) var9)) (= (alloc var0 var2) var4)) (= nullAddr var1)) (= emptyHeap var0))) (Inv_Heap_exp_exp var5 var10))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Heap) (var3 HeapObject) (var4 node) (var5 AllocResHeap) (var6 Heap) (var7 HeapObject) (var8 node) (var9 AllocResHeap) (var10 Heap) (var11 HeapObject) (var12 node) (var13 Addr) (var14 HeapObject) (var15 node) (var16 Addr) (var17 Addr)) (or (not (and (Inv_Heap_exp_exp var17 var16) (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (= (O_node var15) var14) (= (node var13) var12)) (= (O_node var12) var11)) (= (AllocResHeap var10 var13) var9)) (= (O_node var8) var7)) (= (AllocResHeap var6 var17) var5)) (= (O_node var4) var3)) (= (node var16) var15)) (= (read var2 var17) var14)) (valid var2 var17)) (not (= var1 var13))) (= (write var10 var17 var11) var2)) (not (= var1 var17))) (= (alloc var6 var7) var9)) (= (alloc var0 var3) var5)) (= nullAddr var1)) (= emptyHeap var0)))) (_Glue17 var10 var17 var14))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 node) (var3 AllocResHeap) (var4 Heap) (var5 HeapObject) (var6 node) (var7 AllocResHeap) (var8 Heap) (var9 Addr) (var10 HeapObject) (var11 node) (var12 Addr) (var13 HeapObject) (var14 Addr) (var15 Heap)) (or (not (and (and (and (and (and (and (and (and (and (and (and (and (and (and (= (read var15 var14) var13) (not (valid var15 var14))) (= (node var12) var11)) (= (O_node var11) var10)) (not (= var9 var12))) (= (write var8 var14 var10) var15)) (= (AllocResHeap var8 var12) var7)) (= (O_node var6) var5)) (not (= var9 var14))) (= (alloc var4 var5) var7)) (= (AllocResHeap var4 var14) var3)) (= (O_node var2) var1)) (= (alloc var0 var1) var3)) (= nullAddr var9)) (= emptyHeap var0))) (_Glue17 var8 var14 var13))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 HeapObject) (var3 Heap) (var4 Addr) (var5 Addr)) (not (and (and (Inv_Heap_exp_exp var5 var4) (_Glue17 var3 var5 var2)) (and (and (and (and (= (O_node var1) var0) (= (node var4) var1)) (not (is-O_node var2))) (= (read var3 var5) var0)) (valid var3 var5))))))
(assert (forall ((var0 HeapObject) (var1 HeapObject) (var2 Addr) (var3 Heap)) (not (and (_Glue17 var3 var2 var1) (and (and (and (not (is-O_node var1)) (= (read var3 var2) var0)) (is-O_node var0)) (not (valid var3 var2)))))))
(assert (forall ((var0 AllocResHeap) (var1 Heap) (var2 Addr) (var3 HeapObject) (var4 node)) (or (not (and (and (and (and (= (O_node var4) var3) (= (node var2) var4)) (= (alloc var1 var3) var0)) (not (= 4 4))) (= emptyHeap var1))) (Inv_Heap_exp_exp (newAddr var0) var2))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 AllocResHeap) (var3 Addr) (var4 HeapObject) (var5 node) (var6 AllocResHeap) (var7 Addr) (var8 Heap) (var9 HeapObject) (var10 node)) (or (not (and (and (and (and (and (and (and (and (and (= (O_node var10) var9) (= (AllocResHeap var8 var7) var6)) (= (O_node var5) var4)) (= (node var3) var10)) (= (alloc var8 var9) var2)) (not (= var1 var7))) (= (alloc var0 var4) var6)) (not (= 4 4))) (= nullAddr var1)) (= emptyHeap var0))) (Inv_Heap_exp_exp (newAddr var2) var3))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 HeapObject) (var3 node) (var4 AllocResHeap) (var5 Heap) (var6 HeapObject) (var7 node) (var8 AllocResHeap) (var9 Addr) (var10 Heap) (var11 HeapObject) (var12 node) (var13 Addr) (var14 Addr)) (not (and (Inv_Heap_exp_exp var14 var13) (and (and (and (and (and (and (and (and (and (and (and (and (and (and (= (O_node var12) var11) (= (AllocResHeap var10 var9) var8)) (= (O_node var7) var6)) (= (AllocResHeap var5 var14) var4)) (= (O_node var3) var2)) (= (node var13) var12)) (not (= var1 var9))) (= (read var10 var14) var11)) (valid var10 var14)) (not (= var1 var14))) (= (alloc var5 var6) var8)) (= (alloc var0 var2) var4)) (not (= 4 4))) (= nullAddr var1)) (= emptyHeap var0))))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 node) (var3 AllocResHeap) (var4 Heap) (var5 HeapObject) (var6 node) (var7 AllocResHeap) (var8 HeapObject) (var9 Addr) (var10 Heap) (var11 Addr) (var12 Addr)) (not (and (and (and (and (and (and (and (and (and (and (and (and (and (not (= var12 var11)) (= (read var10 var9) var8)) (is-O_node var8)) (not (valid var10 var9))) (= (AllocResHeap var10 var11) var7)) (= (O_node var6) var5)) (not (= var12 var9))) (= (alloc var4 var5) var7)) (= (AllocResHeap var4 var9) var3)) (= (O_node var2) var1)) (= (alloc var0 var1) var3)) (not (= 4 4))) (= nullAddr var12)) (= emptyHeap var0)))))
(assert (forall ((var0 AllocResHeap) (var1 Heap) (var2 Addr) (var3 HeapObject) (var4 node)) (or (not (and (and (and (and (= (O_node var4) var3) (= (node var2) var4)) (= (alloc var1 var3) var0)) (not (= 4 4))) (= emptyHeap var1))) (Inv_Heap_exp_exp (newAddr var0) var2))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 AllocResHeap) (var3 Addr) (var4 HeapObject) (var5 node) (var6 AllocResHeap) (var7 Addr) (var8 Heap) (var9 HeapObject) (var10 node)) (or (not (and (and (and (and (and (and (and (and (and (= (O_node var10) var9) (= (AllocResHeap var8 var7) var6)) (= (O_node var5) var4)) (= (node var3) var10)) (= (alloc var8 var9) var2)) (not (= var1 var7))) (= (alloc var0 var4) var6)) (not (= 4 4))) (= nullAddr var1)) (= emptyHeap var0))) (Inv_Heap_exp_exp (newAddr var2) var3))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 HeapObject) (var3 node) (var4 AllocResHeap) (var5 Addr) (var6 Heap) (var7 HeapObject) (var8 node) (var9 AllocResHeap) (var10 Addr) (var11 Heap)) (or (not (and (and (and (and (and (and (and (and (and (and (and (= (AllocResHeap var11 var10) var9) (= (O_node var8) var7)) (= (AllocResHeap var6 var5) var4)) (= (O_node var3) var2)) (not (= var1 var10))) (valid var11 var5)) (not (= var1 var5))) (= (alloc var6 var7) var9)) (= (alloc var0 var2) var4)) (not (= 4 4))) (= nullAddr var1)) (= emptyHeap var0))) (Inv_Heap_exp_exp var5 var10))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Heap) (var3 HeapObject) (var4 node) (var5 AllocResHeap) (var6 Heap) (var7 HeapObject) (var8 node) (var9 AllocResHeap) (var10 Heap) (var11 HeapObject) (var12 node) (var13 Addr) (var14 HeapObject) (var15 node) (var16 Addr) (var17 Addr)) (or (not (and (Inv_Heap_exp_exp var17 var16) (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (= (O_node var15) var14) (= (node var13) var12)) (= (O_node var12) var11)) (= (AllocResHeap var10 var13) var9)) (= (O_node var8) var7)) (= (AllocResHeap var6 var17) var5)) (= (O_node var4) var3)) (= (node var16) var15)) (= (read var2 var17) var14)) (valid var2 var17)) (not (= var1 var13))) (= (write var10 var17 var11) var2)) (not (= var1 var17))) (= (alloc var6 var7) var9)) (= (alloc var0 var3) var5)) (not (= 4 4))) (= nullAddr var1)) (= emptyHeap var0)))) (_Glue7 var10 var17 var14))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 node) (var3 AllocResHeap) (var4 Heap) (var5 HeapObject) (var6 node) (var7 AllocResHeap) (var8 Heap) (var9 Addr) (var10 HeapObject) (var11 node) (var12 Addr) (var13 HeapObject) (var14 Addr) (var15 Heap)) (or (not (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (= (read var15 var14) var13) (not (valid var15 var14))) (= (node var12) var11)) (= (O_node var11) var10)) (not (= var9 var12))) (= (write var8 var14 var10) var15)) (= (AllocResHeap var8 var12) var7)) (= (O_node var6) var5)) (not (= var9 var14))) (= (alloc var4 var5) var7)) (= (AllocResHeap var4 var14) var3)) (= (O_node var2) var1)) (= (alloc var0 var1) var3)) (not (= 4 4))) (= nullAddr var9)) (= emptyHeap var0))) (_Glue7 var8 var14 var13))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 HeapObject) (var3 Heap) (var4 Addr) (var5 Addr)) (not (and (and (Inv_Heap_exp_exp var5 var4) (_Glue7 var3 var5 var2)) (and (and (and (and (= (O_node var1) var0) (= (node var4) var1)) (is-O_node var2)) (= (read var3 var5) var0)) (valid var3 var5))))))
(assert (forall ((var0 HeapObject) (var1 HeapObject) (var2 Addr) (var3 Heap)) (not (and (_Glue7 var3 var2 var1) (and (and (and (is-O_node var1) (= (read var3 var2) var0)) (is-O_node var0)) (not (valid var3 var2)))))))
(assert (forall ((var0 AllocResHeap) (var1 Heap) (var2 Addr) (var3 HeapObject) (var4 node)) (or (not (and (and (and (= (O_node var4) var3) (= (node var2) var4)) (= (alloc var1 var3) var0)) (= emptyHeap var1))) (Inv_Heap_exp_exp (newAddr var0) var2))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 AllocResHeap) (var3 Addr) (var4 HeapObject) (var5 node) (var6 AllocResHeap) (var7 Addr) (var8 Heap) (var9 HeapObject) (var10 node)) (or (not (and (and (and (and (and (and (and (and (= (O_node var10) var9) (= (AllocResHeap var8 var7) var6)) (= (O_node var5) var4)) (= (node var3) var10)) (= (alloc var8 var9) var2)) (not (= var1 var7))) (= (alloc var0 var4) var6)) (= nullAddr var1)) (= emptyHeap var0))) (Inv_Heap_exp_exp (newAddr var2) var3))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 HeapObject) (var3 node) (var4 AllocResHeap) (var5 Heap) (var6 HeapObject) (var7 node) (var8 AllocResHeap) (var9 Addr) (var10 Heap) (var11 HeapObject) (var12 node) (var13 Addr) (var14 Addr)) (not (and (Inv_Heap_exp_exp var14 var13) (and (and (and (and (and (and (and (and (and (and (and (and (and (and (= (O_node var12) var11) (= (AllocResHeap var10 var9) var8)) (= (O_node var7) var6)) (= (AllocResHeap var5 var14) var4)) (= (O_node var3) var2)) (= (node var13) var12)) (not (= var1 var9))) (= (read var10 var14) var11)) (not (= 4 4))) (valid var10 var14)) (not (= var1 var14))) (= (alloc var5 var6) var8)) (= (alloc var0 var2) var4)) (= nullAddr var1)) (= emptyHeap var0))))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 node) (var3 AllocResHeap) (var4 Heap) (var5 HeapObject) (var6 node) (var7 AllocResHeap) (var8 HeapObject) (var9 Addr) (var10 Heap) (var11 Addr) (var12 Addr)) (not (and (and (and (and (and (and (and (and (and (and (and (and (not (= var12 var11)) (= (read var10 var9) var8)) (not (is-O_node var8))) (not (valid var10 var9))) (= (AllocResHeap var10 var11) var7)) (= (O_node var6) var5)) (not (= var12 var9))) (= (alloc var4 var5) var7)) (= (AllocResHeap var4 var9) var3)) (= (O_node var2) var1)) (= (alloc var0 var1) var3)) (= nullAddr var12)) (= emptyHeap var0)))))
(assert (forall ((var0 AllocResHeap) (var1 Heap) (var2 Addr) (var3 HeapObject) (var4 node)) (or (not (and (and (and (= (O_node var4) var3) (= (node var2) var4)) (= (alloc var1 var3) var0)) (= emptyHeap var1))) (Inv_Heap_exp_exp (newAddr var0) var2))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 AllocResHeap) (var3 Addr) (var4 HeapObject) (var5 node) (var6 AllocResHeap) (var7 Addr) (var8 Heap) (var9 HeapObject) (var10 node)) (or (not (and (and (and (and (and (and (and (and (= (O_node var10) var9) (= (AllocResHeap var8 var7) var6)) (= (O_node var5) var4)) (= (node var3) var10)) (= (alloc var8 var9) var2)) (not (= var1 var7))) (= (alloc var0 var4) var6)) (= nullAddr var1)) (= emptyHeap var0))) (Inv_Heap_exp_exp (newAddr var2) var3))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 HeapObject) (var3 node) (var4 AllocResHeap) (var5 Addr) (var6 Heap) (var7 HeapObject) (var8 node) (var9 AllocResHeap) (var10 Addr) (var11 Heap)) (or (not (and (and (and (and (and (and (and (and (and (and (= (AllocResHeap var11 var10) var9) (= (O_node var8) var7)) (= (AllocResHeap var6 var5) var4)) (= (O_node var3) var2)) (not (= var1 var10))) (valid var11 var5)) (not (= var1 var5))) (= (alloc var6 var7) var9)) (= (alloc var0 var2) var4)) (= nullAddr var1)) (= emptyHeap var0))) (Inv_Heap_exp_exp var5 var10))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Heap) (var3 HeapObject) (var4 node) (var5 AllocResHeap) (var6 Heap) (var7 HeapObject) (var8 node) (var9 AllocResHeap) (var10 Heap) (var11 HeapObject) (var12 node) (var13 Addr) (var14 HeapObject) (var15 node) (var16 Addr) (var17 Addr)) (or (not (and (Inv_Heap_exp_exp var17 var16) (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (= (O_node var15) var14) (= (node var13) var12)) (= (O_node var12) var11)) (= (AllocResHeap var10 var13) var9)) (= (O_node var8) var7)) (= (AllocResHeap var6 var17) var5)) (= (O_node var4) var3)) (= (node var16) var15)) (= (read var2 var17) var14)) (valid var2 var17)) (not (= var1 var13))) (= (write var10 var17 var11) var2)) (not (= var1 var17))) (= (alloc var6 var7) var9)) (= (alloc var0 var3) var5)) (= nullAddr var1)) (= emptyHeap var0)))) (_Glue22 var2 var10 var17 var14))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 node) (var3 AllocResHeap) (var4 Heap) (var5 HeapObject) (var6 node) (var7 AllocResHeap) (var8 Heap) (var9 Addr) (var10 HeapObject) (var11 node) (var12 Addr) (var13 HeapObject) (var14 Addr) (var15 Heap)) (or (not (and (and (and (and (and (and (and (and (and (and (and (and (and (and (= (read var15 var14) var13) (not (valid var15 var14))) (= (node var12) var11)) (= (O_node var11) var10)) (not (= var9 var12))) (= (write var8 var14 var10) var15)) (= (AllocResHeap var8 var12) var7)) (= (O_node var6) var5)) (not (= var9 var14))) (= (alloc var4 var5) var7)) (= (AllocResHeap var4 var14) var3)) (= (O_node var2) var1)) (= (alloc var0 var1) var3)) (= nullAddr var9)) (= emptyHeap var0))) (_Glue22 var15 var8 var14 var13))))
(assert (forall ((var0 node) (var1 Addr) (var2 HeapObject) (var3 Addr) (var4 Heap) (var5 Heap)) (or (not (and (_Glue22 var5 var4 var3 var2) (and (and (and (= (node var1) var0) (is-O_node var2)) (= (getnode var2) var0)) (valid var5 var3)))) (Inv_Heap_exp_exp var3 var1))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 node) (var3 HeapObject) (var4 node) (var5 HeapObject) (var6 Heap) (var7 Heap) (var8 Addr) (var9 Addr)) (or (not (and (and (Inv_Heap_exp_exp var9 var8) (_Glue22 var7 var6 var9 var5)) (and (and (and (and (and (and (and (= (O_node var4) var3) (= (O_node var2) var1)) (= (node var8) var4)) (= (read var0 var9) var3)) (valid var0 var9)) (is-O_node var5)) (= (getnode var5) var2)) (= (write var7 var9 var1) var0)))) (_Glue24 var6 var9 var3))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 HeapObject) (var3 Heap) (var4 HeapObject) (var5 Addr) (var6 Heap) (var7 Heap)) (or (not (and (_Glue22 var7 var6 var5 var4) (and (and (and (and (and (= (read var3 var5) var2) (not (valid var3 var5))) (is-O_node var4)) (= (getnode var4) var1)) (= (O_node var1) var0)) (= (write var7 var5 var0) var3)))) (_Glue24 var6 var5 var2))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 HeapObject) (var3 Heap) (var4 Addr) (var5 Addr)) (not (and (and (Inv_Heap_exp_exp var5 var4) (_Glue24 var3 var5 var2)) (and (and (and (and (= (O_node var1) var0) (= (node var4) var1)) (not (is-O_node var2))) (= (read var3 var5) var0)) (valid var3 var5))))))
(assert (forall ((var0 HeapObject) (var1 HeapObject) (var2 Addr) (var3 Heap)) (not (and (_Glue24 var3 var2 var1) (and (and (and (not (is-O_node var1)) (= (read var3 var2) var0)) (is-O_node var0)) (not (valid var3 var2)))))))
(check-sat)
