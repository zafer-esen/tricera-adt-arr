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

(declare-datatypes ((HeapObject 0) (TData 0))
                   (((O_Int (getInt Int)) (O_UInt (getUInt Int)) (O_Addr (getAddr Addr)) (O_AddrRange (getAddrRange AddrRange)) (O_TData (getTData TData)) (defObj))
                   ((TData (|TData::lo| Addr) (|TData::hi| Addr)))))
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
(declare-fun inv_main538_9_7 (Heap TData Int Addr Addr) Bool)
(declare-fun inv_main547_5 (Heap TData) Bool)
(declare-fun inv_main_9 (Heap TData Int Addr Addr) Bool)
(assert (forall ((var0 TData) (var1 Heap)) (or (not (= var1 emptyHeap)) (inv_main547_5 var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 TData) (var3 Heap) (var4 Int) (var5 TData) (var6 Heap) (var7 Addr) (var8 Int) (var9 TData) (var10 Int) (var11 Heap) (var12 Addr) (var13 Int) (var14 Int) (var15 TData) (var16 TData) (var17 Int) (var18 Heap) (var19 Heap) (var20 TData) (var21 Heap) (var22 Addr) (var23 Int) (var24 TData) (var25 Heap) (var26 Addr) (var27 Addr) (var28 Addr) (var29 Int) (var30 Int) (var31 TData) (var32 TData) (var33 Heap) (var34 Addr) (var35 Heap) (var36 Int) (var37 TData) (var38 Heap)) (or (not (and (inv_main547_5 var38 var37) (and (and (and (and (<= 0 (+ var36 (* (- 1) (getInt (read var35 var34))))) (and (and (and (and (and (= var35 var33) (= var32 var31)) (= var30 var29)) (= var28 var27)) (= var34 var26)) (= var36 (getInt (read var33 var27))))) (and (and (and (and (= var33 var25) (= var31 var24)) (= var29 var23)) (= var27 var22)) (= var26 (|TData::hi| var24)))) (and (and (and (= var25 var21) (= var24 var20)) (= var23 1)) (= var22 (|TData::lo| var20)))) (and (and (and (and (and (and (and (and (= var19 (newHeap (alloc var18 (O_Int var17)))) (= var16 var15)) (= var14 var13)) (= var12 (newAddr (alloc var18 (O_Int var17))))) (and (and (and (= var11 (newHeap (alloc var38 (O_Int var10)))) (= var9 var37)) (= var8 1)) (= var7 (newAddr (alloc var38 (O_Int var10)))))) (and (and (= var18 var11) (= var15 (TData var7 (|TData::hi| var9)))) (= var13 var8))) (and (and (= var6 var19) (= var5 (TData (|TData::lo| var16) var12))) (= var4 var14))) (and (and (= var3 (write var6 (|TData::lo| var5) (O_Int 4))) (= var2 var5)) (= var1 var4))) (and (and (= var21 (write var3 (|TData::hi| var2) (O_Int 8))) (= var20 var2)) (= var0 var1)))))) (inv_main538_9_7 var35 var32 var30 var28 var34))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Int) (var4 TData) (var5 Heap)) (or (not (and (inv_main538_9_7 var5 var4 var3 var2 var1) (= var0 (write var5 var2 defObj)))) (inv_main_9 var0 var4 var3 var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 TData) (var4 Heap)) (not (and (inv_main538_9_7 var4 var3 var2 var1 var0) (and (not (= var1 nullAddr)) (= (read var4 var1) defObj))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 TData) (var4 Heap)) (not (and (inv_main_9 var4 var3 var2 var1 var0) (and (not (= var0 nullAddr)) (= (read var4 var0) defObj))))))
(check-sat)
