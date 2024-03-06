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
(declare-fun inv_main19_2 (Heap) Bool)
(declare-fun inv_main22_9 (Heap Int Addr) Bool)
(declare-fun inv_main23_8 (Heap Int Addr Int Addr) Bool)
(declare-fun rec (Heap Addr Heap Addr) Bool)
(declare-fun rec10_3 (Heap Addr Heap Addr Int) Bool)
(declare-fun rec15_9 (Heap Addr Heap Addr Int) Bool)
(declare-fun rec15_9_3 (Heap Addr Heap Addr Addr) Bool)
(declare-fun rec8_1 (Heap Addr Heap Addr) Bool)
(declare-fun rec9_5 (Heap Addr Heap Addr) Bool)
(declare-fun rec9_5_0 (Heap Addr Heap Addr) Bool)
(declare-fun rec_1 (Heap Addr Heap Addr Int) Bool)
(declare-fun rec_2 (Heap Addr Heap Addr) Bool)
(declare-fun rec_post (Heap Addr Heap Int) Bool)
(declare-fun rec_pre (Heap Addr) Bool)
(assert (forall ((var0 Heap)) (or (not (= var0 emptyHeap)) (inv_main19_2 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Heap) (var4 Addr) (var5 Int) (var6 Heap)) (or (not (and (inv_main22_9 var6 var5 var4) (and (and (is-O_Int (read var6 var4)) (is-O_Int (read var6 var4))) (and (and (= var3 (write var6 var4 (O_Int var2))) (= var1 var5)) (= var0 var4))))) (inv_main23_8 var3 var1 var0 var1 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Heap) (var4 Int) (var5 Heap) (var6 Addr) (var7 Int) (var8 Addr) (var9 Int) (var10 Heap)) (or (not (and (and (inv_main23_8 var10 var9 var8 var7 var6) (rec_post var10 var6 var5 var4)) (and (and (and (= var3 (newHeap (alloc var5 (O_Int var2)))) (= var1 (+ var7 var4))) (= var0 (newAddr (alloc var5 (O_Int var2))))) (<= 0 (+ (+ var7 var4) (- 1)))))) (inv_main22_9 var3 var1 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Int) (var4 Heap) (var5 Heap)) (or (not (and (inv_main19_2 var5) (and (and (and (= var4 (newHeap (alloc var5 (O_Int var3)))) (= var2 var1)) (= var0 (newAddr (alloc var5 (O_Int var3))))) (<= 0 (+ var1 (- 1)))))) (inv_main22_9 var4 var2 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Heap)) (not (and (inv_main22_9 var2 var1 var0) (not (is-O_Int (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Heap)) (not (and (inv_main22_9 var2 var1 var0) (and (is-O_Int (read var2 var0)) (not (is-O_Int (read var2 var0))))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Int) (var4 Heap)) (or (not (inv_main23_8 var4 var3 var2 var1 var0)) (rec_pre var4 var0))))
(assert (forall ((var0 Addr) (var1 Heap)) (or (not (rec_pre var1 var0)) (rec8_1 var1 var0 var1 var0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Heap)) (or (not (and (rec8_1 var3 var2 var1 var0) (and (is-O_Int (read var3 var2)) (<= 0 (+ (* (- 1) (getInt (read var3 var2))) (- 1)))))) (rec9_5 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Heap)) (or (not (and (rec8_1 var3 var2 var1 var0) (and (is-O_Int (read var3 var2)) (not (<= 0 (+ (* (- 1) (getInt (read var3 var2))) (- 1))))))) (rec9_5_0 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Heap)) (or (not (and (rec9_5 var4 var3 var2 var1) (and (is-O_Int (read var4 var3)) (= var0 (getInt (read var4 var3)))))) (rec10_3 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Heap)) (or (not (and (rec10_3 var5 var4 var3 var2 var1) (= var0 (write var5 var4 defObj)))) (rec_1 var0 var4 var3 var2 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Heap)) (or (not (rec_1 var4 var3 var2 var1 var0)) (rec15_9 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Heap)) (or (not (rec9_5_0 var3 var2 var1 var0)) (rec var3 var2 var1 var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Heap)) (or (not (and (rec var4 var3 var2 var1) (and (and (is-O_Int (read var4 var3)) (is-O_Int (read var4 var3))) (= var0 (write var4 var3 (O_Int (+ (getInt (read var4 var3)) (- 1)))))))) (rec_2 var0 var3 var2 var1))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Heap)) (or (not (rec_2 var3 var2 var1 var0)) (rec15_9_3 var3 var2 var1 var0 var2))))
(assert (forall ((var0 Int) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Heap)) (or (not (and (rec15_9_3 var6 var5 var4 var3 var2) (rec_post var6 var2 var1 var0))) (rec15_9 var1 var5 var4 var3 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Heap)) (or (not (rec15_9 var4 var3 var2 var1 var0)) (rec_post var2 var1 var4 var0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Heap)) (not (and (rec8_1 var3 var2 var1 var0) (not (is-O_Int (read var3 var2)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Heap)) (not (and (rec9_5 var3 var2 var1 var0) (not (is-O_Int (read var3 var2)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Heap)) (not (and (rec var3 var2 var1 var0) (not (is-O_Int (read var3 var2)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Heap)) (not (and (rec var3 var2 var1 var0) (and (is-O_Int (read var3 var2)) (not (is-O_Int (read var3 var2))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Heap)) (or (not (rec15_9_3 var4 var3 var2 var1 var0)) (rec_pre var4 var0))))
(check-sat)
