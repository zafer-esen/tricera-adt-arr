(set-logic HORN)
(set-info :source |
    Benchmark: 
    Output by Princess (http://www.philipp.ruemmer.org/princess.shtml)
|)
;===============================================================================
; Encoding of Heap sorts and operations
;-------------------------------------------------------------------------------
(define-sort Addr() Int)
(declare-datatypes ((AddrRange 0))
                   (((AddrRange (AddrRangeStart Addr) (AddrRangeSize Int)))))

(declare-datatypes ((HeapObject 0) (node 0))
                   (((O_Int (getInt Int)) (O_UInt (getUInt Int)) (O_Addr (getAddr Addr)) (O_AddrRange (getAddrRange AddrRange)) (O_node (getnode node)) (defObj))
                   ((node (|node::h| Int) (|node::n| Addr)))))
(declare-datatypes ((BatchAllocResHeap 0) (AllocResHeap 0) (Heap 0))
                   (((BatchAllocResHeap   (newBatchHeap Heap) (newAddrRange AddrRange)))
                   ((AllocResHeap   (newHeap Heap) (newAddr Addr)))
                    ((HeapCtor (HeapSize Int)
                               (HeapContents (Array Addr HeapObject))))))
(define-fun nullAddr  () Addr 0)
(define-fun valid     ((h Heap) (p Addr)) Bool
  (and (>= (HeapSize h) p) (> p 0)))
(define-fun emptyHeap () Heap (
  HeapCtor 0 (( as const (Array Addr HeapObject)) defObj)))
(define-fun read ((h Heap) (p Addr)) HeapObject
  (ite (valid h p)
       (select (HeapContents h) p)
       defObj))
(define-fun write ((h Heap) (p Addr) (o HeapObject)) Heap
  (ite (valid h p)
       (HeapCtor (HeapSize h) (store (HeapContents h) p o))
       h))
(define-fun alloc   ((h Heap) (o HeapObject)) AllocResHeap
  (AllocResHeap (HeapCtor (+ 1 (HeapSize h))
                    (store (HeapContents h) (+ 1 (HeapSize h)) o))
          (+ 1 (HeapSize h))))

;===============================================================================
(declare-fun _Glue1 (Addr Addr Heap HeapObject) Bool)
(declare-fun inv_main (Heap Addr) Bool)
(declare-fun inv_main534_3 (Heap Addr) Bool)
(declare-fun _Glue3 (Heap Addr Addr HeapObject) Bool)
(declare-fun Inv_Heap_exp_exp (Addr Int Addr) Bool)
(assert (forall ((var0 Addr) (var1 Heap)) (or (not (inv_main534_3 var1 var0)) (inv_main var1 var0))))
(assert (forall ((var0 AllocResHeap) (var1 Addr) (var2 Int) (var3 HeapObject) (var4 node) (var5 Addr) (var6 Heap)) (or (not (and (inv_main534_3 var6 var5) (and (and (= (O_node var4) var3) (= (node var2 var1) var4)) (= (alloc var6 var3) var0)))) (Inv_Heap_exp_exp (newAddr var0) var2 var1))))
(assert (forall ((var0 Addr) (var1 AllocResHeap) (var2 Heap) (var3 HeapObject) (var4 node) (var5 HeapObject) (var6 node) (var7 Addr) (var8 Heap) (var9 Addr) (var10 Int) (var11 Addr)) (or (not (and (and (Inv_Heap_exp_exp var11 var10 var9) (inv_main534_3 var8 var7)) (and (and (and (and (and (and (and (and (= (O_node var6) var5) (= (O_node var4) var3)) (= (AllocResHeap var2 var11) var1)) (= (node var10 var9) var6)) (not (= var11 var0))) (= (read var2 var11) var5)) (valid var2 var11)) (= nullAddr var0)) (= (alloc var8 var3) var1)))) (_Glue1 var7 var11 var2 var5))))
(assert (forall ((var0 AllocResHeap) (var1 HeapObject) (var2 node) (var3 HeapObject) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main534_3 var8 var7) (and (and (and (and (and (and (not (= var6 var5)) (= (read var4 var6) var3)) (not (valid var4 var6))) (= (O_node var2) var1)) (= (AllocResHeap var4 var6) var0)) (= nullAddr var5)) (= (alloc var8 var1) var0)))) (_Glue1 var7 var6 var4 var3))))
(assert (forall ((var0 Int) (var1 Addr) (var2 node) (var3 HeapObject) (var4 Heap) (var5 Addr) (var6 Addr)) (or (not (and (_Glue1 var6 var5 var4 var3) (and (and (and (= (getnode var3) var2) (= (|node::n| var2) var1)) (valid var4 var5)) (= var0 1)))) (Inv_Heap_exp_exp var5 var0 var1))))
(assert (forall ((var0 node) (var1 Heap) (var2 HeapObject) (var3 node) (var4 Addr) (var5 HeapObject) (var6 node) (var7 HeapObject) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Int) (var12 Addr)) (or (not (and (and (Inv_Heap_exp_exp var12 var11 var10) (_Glue1 var9 var12 var8 var7)) (and (and (and (and (and (and (and (and (= (O_node var6) var5) (= (node 1 var4) var3)) (= (O_node var3) var2)) (= (node var11 var10) var6)) (= (read var1 var12) var5)) (valid var1 var12)) (= (getnode var7) var0)) (= (|node::n| var0) var4)) (= (write var8 var12 var2) var1)))) (_Glue3 var1 var9 var12 var5))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 node) (var4 HeapObject) (var5 Heap) (var6 HeapObject) (var7 Heap) (var8 Addr) (var9 Addr)) (or (not (and (_Glue1 var9 var8 var7 var6) (and (and (and (and (and (and (= (read var5 var8) var4) (not (valid var5 var8))) (= (getnode var6) var3)) (= (|node::n| var3) var2)) (= (node 1 var2) var1)) (= (O_node var1) var0)) (= (write var7 var8 var0) var5)))) (_Glue3 var5 var9 var8 var4))))
(assert (forall ((var0 Int) (var1 node) (var2 HeapObject) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (_Glue3 var5 var4 var3 var2) (and (and (= (getnode var2) var1) (= (|node::h| var1) var0)) (valid var5 var3)))) (Inv_Heap_exp_exp var3 var0 var4))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 node) (var3 Int) (var4 node) (var5 HeapObject) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (_Glue3 var8 var7 var6 var5) (and (and (and (and (= (getnode var5) var4) (= (|node::h| var4) var3)) (= (node var3 var7) var2)) (= (O_node var2) var1)) (= (write var8 var6 var1) var0)))) (inv_main534_3 var0 var6))))
(assert (forall ((var0 Addr) (var1 HeapObject) (var2 node) (var3 Heap) (var4 Addr) (var5 Int) (var6 Addr)) (not (and (and (Inv_Heap_exp_exp var6 var5 var4) (inv_main var3 var6)) (and (and (and (and (and (and (= (O_node var2) var1) (= (node var5 var4) var2)) (not (= var6 var0))) (not (= var5 1))) (= nullAddr var0)) (= (read var3 var6) var1)) (valid var3 var6))))))
(assert (forall ((var0 node) (var1 HeapObject) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap)) (not (and (inv_main var5 var4) (and (and (and (and (and (and (not (= var4 var3)) (not (= var2 1))) (= nullAddr var3)) (= (read var5 var4) var1)) (= (getnode var1) var0)) (= (|node::h| var0) var2)) (not (valid var5 var4)))))))
(assert (forall ((var0 Addr) (var1 Heap)) (or (not (and (= emptyHeap var1) (= nullAddr var0))) (inv_main534_3 var1 var0))))
(assert (forall ((var0 Addr) (var1 HeapObject) (var2 node) (var3 Heap) (var4 Addr) (var5 Addr)) (or (not (and (and (Inv_Heap_exp_exp var5 1 var4) (inv_main var3 var5)) (and (and (and (and (and (= (O_node var2) var1) (= (node 1 var4) var2)) (= nullAddr var0)) (= (read var3 var5) var1)) (not (= var5 var0))) (valid var3 var5)))) (inv_main var3 var4))))
(assert (forall ((var0 Addr) (var1 node) (var2 HeapObject) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main var5 var4) (and (and (and (and (and (and (= nullAddr var3) (= (read var5 var4) var2)) (= (getnode var2) var1)) (= (|node::h| var1) 1)) (= (|node::n| var1) var0)) (not (= var4 var3))) (not (valid var5 var4))))) (inv_main var5 var0))))
(check-sat)
