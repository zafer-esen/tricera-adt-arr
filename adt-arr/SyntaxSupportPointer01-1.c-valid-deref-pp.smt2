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

(declare-datatypes ((HeapObject 0))
                   (((O_Int (getInt Int)) (O_UInt (getUInt Int)) (O_Addr (getAddr Addr)) (O_AddrRange (getAddrRange AddrRange)) (defObj))))
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
(declare-fun Inv_Heap_exp (Addr Int) Bool)
(declare-fun _Glue7_exp (Int Addr Heap HeapObject) Bool)
(declare-fun inv_main (Heap Addr) Bool)
(declare-fun _Glue0 (Heap Addr HeapObject) Bool)
(assert (forall ((var0 HeapObject) (var1 Heap) (var2 Int) (var3 Addr)) (not (and (and (Inv_Heap_exp var3 var2) (inv_main var1 var3)) (and (and (and (and (= (O_Int var2) var0) (= (read var1 var3) var0)) (not (= 0 0))) (<= 0 var2)) (valid var1 var3))))))
(assert (forall ((var0 Int) (var1 HeapObject) (var2 Addr) (var3 Heap)) (not (and (inv_main var3 var2) (and (and (and (and (and (= (read var3 var2) var1) (is-O_Int var1)) (= (getInt var1) var0)) (not (= 0 0))) (<= 0 var0)) (not (valid var3 var2)))))))
(assert (forall ((var0 HeapObject) (var1 Heap) (var2 Int) (var3 Addr)) (not (and (and (Inv_Heap_exp var3 var2) (inv_main var1 var3)) (and (and (and (= (O_Int var2) var0) (not (= 0 0))) (= (read var1 var3) var0)) (valid var1 var3))))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Heap)) (not (and (inv_main var2 var1) (and (and (not (is-O_Int var0)) (= (read var2 var1) var0)) (not (valid var2 var1)))))))
(assert (forall ((var0 AllocResHeap) (var1 Heap) (var2 HeapObject) (var3 Int)) (or (not (and (and (= (O_Int var3) var2) (= (alloc var1 var2) var0)) (= emptyHeap var1))) (Inv_Heap_exp (newAddr var0) var3))))
(assert (forall ((var0 Int) (var1 Heap) (var2 HeapObject) (var3 Int) (var4 AllocResHeap) (var5 Heap) (var6 HeapObject) (var7 Int) (var8 Addr)) (or (not (and (Inv_Heap_exp var8 var7) (and (and (and (and (and (and (and (= (O_Int var7) var6) (= (read var5 var8) var6)) (valid var5 var8)) true) (= (AllocResHeap var5 var8) var4)) (= (O_Int var3) var2)) (= (alloc var1 var2) var4)) (= emptyHeap var1)))) (_Glue7_exp var0 var8 var5 var6))))
(assert (forall ((var0 Int) (var1 Heap) (var2 HeapObject) (var3 Int) (var4 AllocResHeap) (var5 HeapObject) (var6 Addr) (var7 Heap)) (or (not (and (and (and (and (and (= (read var7 var6) var5) (not (valid var7 var6))) (= (AllocResHeap var7 var6) var4)) (= (O_Int var3) var2)) (= (alloc var1 var2) var4)) (= emptyHeap var1))) (_Glue7_exp var0 var6 var7 var5))))
(assert (forall ((var0 HeapObject) (var1 Heap) (var2 Addr) (var3 Int)) (or (not (and (_Glue7_exp var3 var2 var1 var0) (and (is-O_Int var0) (valid var1 var2)))) (Inv_Heap_exp var2 var3))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 HeapObject) (var3 Heap) (var4 Addr) (var5 Int)) (or (not (and (_Glue7_exp var5 var4 var3 var2) (and (and (= (O_Int var5) var1) (is-O_Int var2)) (= (write var3 var4 var1) var0)))) (inv_main var0 var4))))
(assert (forall ((var0 AllocResHeap) (var1 Heap) (var2 HeapObject) (var3 Int)) (or (not (and (and (= (O_Int var3) var2) (= (alloc var1 var2) var0)) (= emptyHeap var1))) (Inv_Heap_exp (newAddr var0) var3))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 Int) (var3 AllocResHeap) (var4 Heap) (var5 HeapObject) (var6 Int) (var7 Addr)) (not (and (Inv_Heap_exp var7 var6) (and (and (and (and (and (and (and (and (= (O_Int var6) var5) (= (read var4 var7) var5)) (not (= 0 0))) (valid var4 var7)) true) (= (AllocResHeap var4 var7) var3)) (= (O_Int var2) var1)) (= (alloc var0 var1) var3)) (= emptyHeap var0))))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 Int) (var3 AllocResHeap) (var4 HeapObject) (var5 Addr) (var6 Heap)) (not (and (and (and (and (and (and (= (read var6 var5) var4) (not (is-O_Int var4))) (not (valid var6 var5))) (= (AllocResHeap var6 var5) var3)) (= (O_Int var2) var1)) (= (alloc var0 var1) var3)) (= emptyHeap var0)))))
(assert (forall ((var0 HeapObject) (var1 Heap) (var2 Int) (var3 Addr)) (or (not (and (and (Inv_Heap_exp var3 var2) (inv_main var1 var3)) (and (and (= (O_Int var2) var0) (= (read var1 var3) var0)) (valid var1 var3)))) (_Glue0 var1 var3 var0))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Heap)) (or (not (and (inv_main var2 var1) (and (= (read var2 var1) var0) (not (valid var2 var1))))) (_Glue0 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 HeapObject) (var2 Addr) (var3 Heap)) (or (not (and (_Glue0 var3 var2 var1) (and (and (and (is-O_Int var1) (= (getInt var1) (+ var0 1))) (<= 0 (+ var0 1))) (valid var3 var2)))) (Inv_Heap_exp var2 var0))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 Int) (var3 HeapObject) (var4 Addr) (var5 Heap)) (or (not (and (_Glue0 var5 var4 var3) (and (and (and (and (is-O_Int var3) (= (getInt var3) var2)) (<= 0 var2)) (= (O_Int (+ var2 (- 1))) var1)) (= (write var5 var4 var1) var0)))) (inv_main var0 var4))))
(assert (forall ((var0 HeapObject) (var1 Heap) (var2 Int) (var3 Addr)) (not (and (and (Inv_Heap_exp var3 var2) (inv_main var1 var3)) (and (and (and (and (= (O_Int var2) var0) (= (read var1 var3) var0)) (not (= 0 0))) (<= 0 var2)) (valid var1 var3))))))
(assert (forall ((var0 Int) (var1 HeapObject) (var2 Addr) (var3 Heap)) (not (and (inv_main var3 var2) (and (and (and (and (and (= (read var3 var2) var1) (is-O_Int var1)) (= (getInt var1) var0)) (not (= 0 0))) (<= 0 var0)) (not (valid var3 var2)))))))
(assert (forall ((var0 AllocResHeap) (var1 Heap) (var2 HeapObject) (var3 Int)) (or (not (and (and (and (= (O_Int var3) var2) (= (alloc var1 var2) var0)) (not (= 0 0))) (= emptyHeap var1))) (Inv_Heap_exp (newAddr var0) var3))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 Int) (var3 AllocResHeap) (var4 Heap) (var5 HeapObject) (var6 Int) (var7 Addr)) (not (and (Inv_Heap_exp var7 var6) (and (and (and (and (and (and (and (and (= (O_Int var6) var5) (= (read var4 var7) var5)) (valid var4 var7)) true) (= (AllocResHeap var4 var7) var3)) (= (O_Int var2) var1)) (= (alloc var0 var1) var3)) (not (= 0 0))) (= emptyHeap var0))))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 Int) (var3 AllocResHeap) (var4 HeapObject) (var5 Addr) (var6 Heap)) (not (and (and (and (and (and (and (and (= (read var6 var5) var4) (is-O_Int var4)) (not (valid var6 var5))) (= (AllocResHeap var6 var5) var3)) (= (O_Int var2) var1)) (= (alloc var0 var1) var3)) (not (= 0 0))) (= emptyHeap var0)))))
(check-sat)
