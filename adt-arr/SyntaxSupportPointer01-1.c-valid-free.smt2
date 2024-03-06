(set-logic HORN)
(set-info :source |
    Benchmark: C_VC
    Output by Princess (http://www.philipp.ruemmer.org/princess.shtml)
|)
(set-info :status sat)
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
(declare-fun inv_main (Heap Addr) Bool)
(declare-fun inv_main14_2 (Heap) Bool)
(declare-fun inv_main_2 (Heap Addr) Bool)
(assert (forall ((var0 Heap)) (or (not (= var0 emptyHeap)) (inv_main14_2 var0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Addr) (var4 Heap)) (or (not (and (inv_main var4 var3) (and (not (<= 0 var2)) (and (and (= var1 var4) (= var0 var3)) (= var2 (getInt (read var4 var3))))))) (inv_main_2 var1 var0))))
(assert (forall ((var0 Int) (var1 Heap) (var2 Addr) (var3 Int) (var4 Heap) (var5 Heap)) (or (not (and (inv_main14_2 var5) (and (and (= var4 (newHeap (alloc var5 (O_Int var3)))) (= var2 (newAddr (alloc var5 (O_Int var3))))) (= var1 (write var4 var2 (O_Int var0)))))) (inv_main var1 var2))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Heap) (var7 Addr) (var8 Heap)) (or (not (and (inv_main var8 var7) (and (and (and (and (= var6 var5) (= var4 var3)) (= var2 (getInt (read var5 var3)))) (and (<= 0 var1) (and (and (= var5 var8) (= var3 var7)) (= var1 (getInt (read var8 var7)))))) (= var0 (write var6 var4 (O_Int (+ var2 (- 1)))))))) (inv_main var0 var4))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main_2 var1 var0) (and (not (= var0 nullAddr)) (= (read var1 var0) defObj))))))
(check-sat)
