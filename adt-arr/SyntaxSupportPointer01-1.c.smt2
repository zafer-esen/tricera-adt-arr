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
(declare-datatypes ((HeapObject 0))
                   (((O_Int (getInt Int)) (O_UInt (getUInt Int)) (O_Addr (getAddr Addr)) (defObj))))
(declare-datatypes ((AllocResHeap 0) (Heap 0))
                   (((AllocResHeap   (newHeap Heap) (newAddr Addr)))
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
(declare-fun inv_main2 (Heap) Bool)
(declare-fun inv_main4 (Heap Addr) Bool)
(declare-fun inv_main5 (Heap Addr) Bool)
(declare-fun inv_main7 (Heap Addr) Bool)
(assert (inv_main2 emptyHeap))
(assert (forall ((var0 Addr) (var1 Int) (var2 Heap) (var3 Heap)) (or (not (and (inv_main2 var3) (and (= var2 (newHeap (alloc var3 (O_Int var1)))) (= var0 (newAddr (alloc var3 (O_Int var1))))))) (inv_main5 var2 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap)) (or (not (and (inv_main5 var2 var1) (is-O_Int (read var2 var1)))) (inv_main4 (write var2 var1 (O_Int var0)) var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Heap)) (or (not (and (inv_main7 var4 var3) (and (is-O_Int (read var4 var3)) (and (and (= var2 var4) (= var1 var3)) (= var0 (getInt (read var4 var3))))))) (inv_main4 (write var2 var1 (O_Int (+ var0 (- 1)))) var1))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Addr) (var4 Heap)) (or (not (and (inv_main4 var4 var3) (and (and (<= 0 var2) (is-O_Int (read var4 var3))) (and (and (= var1 var4) (= var0 var3)) (= var2 (getInt (read var4 var3))))))) (inv_main7 var1 var0))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main5 var1 var0) (not (is-O_Int (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main4 var1 var0) (not (is-O_Int (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main7 var1 var0) (not (is-O_Int (read var1 var0)))))))
(check-sat)
