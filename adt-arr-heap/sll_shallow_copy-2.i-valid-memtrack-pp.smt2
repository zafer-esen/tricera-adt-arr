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
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 node) (var3 AllocResHeap) (var4 AllocResHeap) (var5 Heap) (var6 HeapObject) (var7 node) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Bool)) (not (and (and (and (and (and (and (and (and (and (and (and (not var11) (not (= var10 var9))) (not (= var10 var8))) (not (= var9 var8))) (= (O_node var7) var6)) (= (alloc var5 var6) var4)) (= (newAddr var4) var8)) (= (AllocResHeap var5 var9) var3)) (= (O_node var2) var1)) (= (alloc var0 var1) var3)) (= nullAddr var10)) (= emptyHeap var0)))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 node) (var3 AllocResHeap) (var4 AllocResHeap) (var5 Heap) (var6 HeapObject) (var7 node) (var8 Addr) (var9 Addr) (var10 Addr)) (not (and (and (and (and (and (and (and (and (and (and (not (= var10 var9)) (not (= var10 var8))) (not (= var9 var8))) (= (O_node var7) var6)) (= (alloc var5 var6) var4)) (= (newAddr var4) var8)) (= (AllocResHeap var5 var9) var3)) (= (O_node var2) var1)) (= (alloc var0 var1) var3)) (= nullAddr var10)) (= emptyHeap var0)))))
(check-sat)
