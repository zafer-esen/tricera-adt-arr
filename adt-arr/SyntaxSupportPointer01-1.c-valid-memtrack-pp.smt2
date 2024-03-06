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
(declare-fun inv_main (Heap Addr Addr) Bool)
(declare-fun _Glue2 (Addr Heap Addr HeapObject) Bool)
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Addr)) (not (and (and (Inv_Heap_exp var5 var4) (inv_main var3 var2 var5)) (and (and (and (and (and (and (not (= var5 var2)) (not (= var1 var2))) (<= 0 (+ (* (- 1) var4) (- 1)))) (= (O_Int var4) var0)) (= nullAddr var1)) (= (read var3 var5) var0)) (valid var3 var5))))))
(assert (forall ((var0 HeapObject) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (not (and (inv_main var5 var4 var3) (and (and (and (and (and (and (not (= var3 var4)) (not (= var2 var4))) (<= 0 (+ (* (- 1) var1) (- 1)))) (= nullAddr var2)) (= (read var5 var3) var0)) (= (getInt var0) var1)) (not (valid var5 var3)))))))
(assert (forall ((var0 AllocResHeap) (var1 Heap) (var2 HeapObject) (var3 Int)) (or (not (and (and (= (O_Int var3) var2) (= (alloc var1 var2) var0)) (= emptyHeap var1))) (Inv_Heap_exp (newAddr var0) var3))))
(assert (forall ((var0 Int) (var1 Heap) (var2 HeapObject) (var3 Int) (var4 AllocResHeap) (var5 Addr) (var6 Heap) (var7 Bool)) (or (not (and (and (and (and (and (not var7) (valid var6 var5)) (= (AllocResHeap var6 var5) var4)) (= (O_Int var3) var2)) (= (alloc var1 var2) var4)) (= emptyHeap var1))) (Inv_Heap_exp var5 var0))))
(assert (forall ((var0 Int) (var1 Heap) (var2 HeapObject) (var3 Int) (var4 AllocResHeap) (var5 Addr) (var6 Heap)) (or (not (and (and (and (and (valid var6 var5) (= (AllocResHeap var6 var5) var4)) (= (O_Int var3) var2)) (= (alloc var1 var2) var4)) (= emptyHeap var1))) (Inv_Heap_exp var5 var0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 HeapObject) (var3 Int) (var4 AllocResHeap) (var5 Heap) (var6 Addr) (var7 Heap) (var8 HeapObject) (var9 Int) (var10 Bool)) (or (not (and (and (and (and (and (and (and (not var10) (= (O_Int var9) var8)) (= (write var7 var6 var8) var5)) (= (AllocResHeap var7 var6) var4)) (= (O_Int var3) var2)) (= (alloc var1 var2) var4)) (= nullAddr var0)) (= emptyHeap var1))) (inv_main var5 var0 var6))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 HeapObject) (var3 Int) (var4 AllocResHeap) (var5 Heap) (var6 Addr) (var7 Heap) (var8 HeapObject) (var9 Int)) (or (not (and (and (and (and (and (and (= (O_Int var9) var8) (= (write var7 var6 var8) var5)) (= (AllocResHeap var7 var6) var4)) (= (O_Int var3) var2)) (= (alloc var1 var2) var4)) (= emptyHeap var1)) (= var0 var6))) (inv_main var5 var6 var0))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Heap) (var3 Int) (var4 Addr)) (or (not (and (and (Inv_Heap_exp var4 var3) (inv_main var2 var1 var4)) (and (and (= (O_Int var3) var0) (= (read var2 var4) var0)) (valid var2 var4)))) (_Glue2 var1 var2 var4 var0))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main var3 var2 var1) (and (= (read var3 var1) var0) (not (valid var3 var1))))) (_Glue2 var2 var3 var1 var0))))
(assert (forall ((var0 Int) (var1 HeapObject) (var2 Addr) (var3 Heap) (var4 Addr)) (or (not (and (_Glue2 var4 var3 var2 var1) (and (and (= (getInt var1) (+ var0 1)) (<= 0 (+ var0 1))) (valid var3 var2)))) (Inv_Heap_exp var2 var0))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 Int) (var3 HeapObject) (var4 Addr) (var5 Heap) (var6 Addr)) (or (not (and (_Glue2 var6 var5 var4 var3) (and (and (and (= (getInt var3) var2) (<= 0 var2)) (= (O_Int (+ var2 (- 1))) var1)) (= (write var5 var4 var1) var0)))) (inv_main var0 var6 var4))))
(check-sat)
