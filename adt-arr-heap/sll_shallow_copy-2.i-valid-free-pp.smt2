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
(declare-fun _Glue4_exp (Heap Addr HeapObject) Bool)
(declare-fun _Glue5_exp (Addr Heap HeapObject) Bool)
(assert (forall ((var0 AllocResHeap) (var1 Heap) (var2 Addr) (var3 HeapObject) (var4 node)) (or (not (and (and (and (= (O_node var4) var3) (= (node var2) var4)) (= (alloc var1 var3) var0)) (= emptyHeap var1))) (Inv_Heap_exp_exp (newAddr var0) var2))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 AllocResHeap) (var3 Addr) (var4 HeapObject) (var5 node) (var6 AllocResHeap) (var7 Addr) (var8 Heap) (var9 HeapObject) (var10 node)) (or (not (and (and (and (and (and (and (and (and (and (= (O_node var10) var9) (= (AllocResHeap var8 var7) var6)) (= (O_node var5) var4)) (= (node var3) var10)) (= (alloc var8 var9) var2)) (not (= var1 var7))) (not (= var7 var1))) (= (alloc var0 var4) var6)) (= nullAddr var1)) (= emptyHeap var0))) (Inv_Heap_exp_exp (newAddr var2) var3))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 HeapObject) (var3 node) (var4 AllocResHeap) (var5 Addr) (var6 Heap) (var7 HeapObject) (var8 node) (var9 AllocResHeap) (var10 Addr) (var11 Heap)) (or (not (and (and (and (and (and (and (and (and (and (and (and (= (AllocResHeap var11 var10) var9) (= (O_node var8) var7)) (= (AllocResHeap var6 var5) var4)) (= (O_node var3) var2)) (not (= var1 var10))) (valid var11 var5)) (= (alloc var6 var7) var9)) (not (= var1 var5))) (not (= var5 var1))) (= (alloc var0 var2) var4)) (= nullAddr var1)) (= emptyHeap var0))) (Inv_Heap_exp_exp var5 var10))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Heap) (var3 HeapObject) (var4 node) (var5 AllocResHeap) (var6 Heap) (var7 HeapObject) (var8 node) (var9 AllocResHeap) (var10 Heap) (var11 HeapObject) (var12 node) (var13 Addr) (var14 HeapObject) (var15 node) (var16 Addr) (var17 Addr)) (or (not (and (Inv_Heap_exp_exp var17 var16) (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (= (O_node var15) var14) (= (node var13) var12)) (= (O_node var12) var11)) (= (AllocResHeap var10 var13) var9)) (= (O_node var8) var7)) (= (AllocResHeap var6 var17) var5)) (= (O_node var4) var3)) (= (node var16) var15)) (= (read var2 var17) var14)) (valid var2 var17)) (= (write var10 var17 var11) var2)) (not (= var1 var13))) (= (alloc var6 var7) var9)) (not (= var1 var17))) (not (= var17 var1))) (= (alloc var0 var3) var5)) (= nullAddr var1)) (= emptyHeap var0)))) (_Glue4_exp var2 var17 var14))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 node) (var3 AllocResHeap) (var4 Heap) (var5 HeapObject) (var6 node) (var7 AllocResHeap) (var8 Addr) (var9 Heap) (var10 HeapObject) (var11 node) (var12 Addr) (var13 HeapObject) (var14 Addr) (var15 Heap)) (or (not (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (= (read var15 var14) var13) (not (valid var15 var14))) (= (node var12) var11)) (= (O_node var11) var10)) (= (write var9 var14 var10) var15)) (not (= var8 var12))) (= (AllocResHeap var9 var12) var7)) (= (O_node var6) var5)) (= (alloc var4 var5) var7)) (not (= var8 var14))) (not (= var14 var8))) (= (AllocResHeap var4 var14) var3)) (= (O_node var2) var1)) (= (alloc var0 var1) var3)) (= nullAddr var8)) (= emptyHeap var0))) (_Glue4_exp var15 var14 var13))))
(assert (forall ((var0 node) (var1 HeapObject) (var2 node) (var3 HeapObject) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr)) (or (not (and (and (Inv_Heap_exp_exp var7 var6) (_Glue4_exp var5 var4 var3)) (and (and (and (and (and (= (O_node var2) var1) (= (node var6) var2)) (= (getnode var3) var0)) (= (|node::next| var0) var7)) (= (read var5 var7) var1)) (valid var5 var7)))) (_Glue5_exp var4 var5 var1))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 node) (var3 HeapObject) (var4 Addr) (var5 Heap)) (or (not (and (_Glue4_exp var5 var4 var3) (and (and (and (= (getnode var3) var2) (= (|node::next| var2) var1)) (= (read var5 var1) var0)) (not (valid var5 var1))))) (_Glue5_exp var4 var5 var0))))
(assert (forall ((var0 node) (var1 Addr) (var2 HeapObject) (var3 Heap) (var4 Addr)) (or (not (and (_Glue5_exp var4 var3 var2) (and (and (= (node var1) var0) (= (getnode var2) var0)) (valid var3 var4)))) (Inv_Heap_exp_exp var4 var1))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 HeapObject) (var3 Heap) (var4 HeapObject) (var5 Heap) (var6 Addr)) (not (and (_Glue5_exp var6 var5 var4) (and (and (and (and (and (= (read var3 var6) var2) (not (valid var3 var6))) (= defObj var2)) (= (getnode var4) var1)) (= (O_node var1) var0)) (= (write var5 var6 var0) var3))))))
(check-sat)
