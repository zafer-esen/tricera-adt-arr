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

(declare-datatypes ((HeapObject 0) (sll 0))
                   (((O_Int (getInt Int)) (O_UInt (getUInt Int)) (O_Addr (getAddr Addr)) (O_AddrRange (getAddrRange AddrRange)) (O_sll (getsll sll)) (defObj))
                   ((sll (|sll::next| Addr)))))
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
(declare-fun inv_main2403_5 (Heap Addr Addr) Bool)
(declare-fun inv_main2412_5 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main2420_9 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main2427_5 (Heap) Bool)
(assert (forall ((var0 Heap)) (or (not (= var0 emptyHeap)) (inv_main2427_5 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main2412_5 var8 var7 var6 var5) (and (and (and (and (and (= var4 var8) (= var3 var7)) (= var2 var6)) (= var1 var5)) (= var0 (|sll::next| (getsll (read var8 var5))))) (not (= var5 nullAddr))))) (inv_main2412_5 var4 var3 var2 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main2403_5 var3 var2 var1) (= var0 0))) (inv_main2412_5 var3 var2 var2 var2))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 sll) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Heap) (var16 Heap) (var17 Addr) (var18 Addr) (var19 Heap)) (or (not (and (inv_main2403_5 var19 var18 var17) (and (and (and (and (and (= var16 var15) (= var14 var13)) (= var12 var11)) (= var10 (|sll::next| (getsll (read var15 var11))))) (and (and (and (and (and (= var9 (newHeap (alloc var19 (O_sll var8)))) (= var7 var18)) (= var6 var17)) (= var5 (newAddr (alloc var19 (O_sll var8))))) (and (and (and (= var4 (write var9 var5 (O_sll (sll nullAddr)))) (= var3 var7)) (= var2 var6)) (= var1 var5))) (not (= var0 0)))) (and (and (= var15 (write var4 var2 (O_sll (sll var1)))) (= var13 var3)) (= var11 var2))))) (inv_main2403_5 var16 var14 var10))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 sll) (var4 Heap) (var5 Heap)) (or (not (and (inv_main2427_5 var5) (and (and (= var4 (newHeap (alloc var5 (O_sll var3)))) (= var2 (newAddr (alloc var5 (O_sll var3))))) (and (= var1 (write var4 var2 (O_sll (sll nullAddr)))) (= var0 var2))))) (inv_main2403_5 var1 var0 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main2420_9 var8 var7 var6 var5) (and (and (not (= var4 nullAddr)) (and (and (and (= var3 (write var8 var6 defObj)) (= var2 var7)) (= var1 var6)) (= var4 var5))) (= var0 (|sll::next| (getsll (read var3 var4))))))) (inv_main2420_9 var3 var2 var4 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main2412_5 var4 var3 var2 var1) (and (and (not (= var3 nullAddr)) (= var1 nullAddr)) (= var0 (|sll::next| (getsll (read var4 var3))))))) (inv_main2420_9 var4 var3 var3 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main2420_9 var3 var2 var1 var0) (and (not (= var1 nullAddr)) (= (read var3 var1) defObj))))))
(check-sat)
