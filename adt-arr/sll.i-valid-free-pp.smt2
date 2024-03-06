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
(declare-fun inv_main2420_9 (Heap Addr Addr) Bool)
(declare-fun Inv_Heap (Addr HeapObject) Bool)
(declare-fun inv_main2412_5 (Heap Addr Addr) Bool)
(declare-fun inv_main2403_5 (Heap Addr Addr) Bool)
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 HeapObject) (var4 Addr)) (not (and (and (Inv_Heap var4 var3) (inv_main2420_9 var2 var4 var1)) (and (and (and (and (not (= var4 var0)) (= (read var2 var4) var3)) (= defObj var3)) (= nullAddr var0)) (valid var2 var4))))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main2420_9 var4 var3 var2) (and (and (and (and (not (= var3 var1)) (= (read var4 var3) var0)) (= defObj var0)) (= nullAddr var1)) (not (valid var4 var3)))))))
(assert (forall ((var0 Addr) (var1 sll) (var2 Addr) (var3 Heap) (var4 HeapObject) (var5 Addr)) (or (not (and (and (Inv_Heap var5 var4) (inv_main2412_5 var3 var5 var2)) (and (and (and (and (and (not (= var5 var2)) (= (read var3 var5) var4)) (= (getsll var4) var1)) (= (|sll::next| var1) var0)) (= nullAddr var2)) (valid var3 var5)))) (inv_main2420_9 var3 var5 var0))))
(assert (forall ((var0 Addr) (var1 sll) (var2 HeapObject) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main2412_5 var5 var4 var3) (and (and (and (and (and (not (= var4 var3)) (= (read var5 var4) var2)) (= (getsll var2) var1)) (= (|sll::next| var1) var0)) (= nullAddr var3)) (not (valid var5 var4))))) (inv_main2420_9 var5 var4 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main2403_5 var3 var2 var1) (= var0 var2))) (inv_main2412_5 var3 var0 var2))))
(assert (forall ((var0 Addr) (var1 sll) (var2 Addr) (var3 Addr) (var4 Heap) (var5 HeapObject) (var6 Addr)) (or (not (and (and (Inv_Heap var6 var5) (inv_main2412_5 var4 var3 var6)) (and (and (and (and (and (not (= var6 var2)) (= nullAddr var2)) (= (read var4 var6) var5)) (= (getsll var5) var1)) (= (|sll::next| var1) var0)) (valid var4 var6)))) (inv_main2412_5 var4 var3 var0))))
(assert (forall ((var0 Addr) (var1 sll) (var2 HeapObject) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main2412_5 var6 var5 var4) (and (and (and (and (and (not (= var4 var3)) (= nullAddr var3)) (= (read var6 var4) var2)) (= (getsll var2) var1)) (= (|sll::next| var1) var0)) (not (valid var6 var4))))) (inv_main2412_5 var6 var5 var0))))
(assert (forall ((var0 AllocResHeap) (var1 HeapObject) (var2 sll) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main2403_5 var5 var4 var3) (and (= (O_sll var2) var1) (= (alloc var5 var1) var0)))) (Inv_Heap (newAddr var0) var1))))
(assert (forall ((var0 AllocResHeap) (var1 HeapObject) (var2 sll) (var3 Addr) (var4 Heap) (var5 HeapObject) (var6 sll) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main2403_5 var10 var9 var8) (and (and (and (and (and (and (= (sll var7) var6) (= (O_sll var6) var5)) (= nullAddr var7)) (valid var4 var3)) (= (O_sll var2) var1)) (= (AllocResHeap var4 var3) var0)) (= (alloc var10 var1) var0)))) (Inv_Heap var3 var5))))
(assert (forall ((var0 AllocResHeap) (var1 HeapObject) (var2 sll) (var3 Heap) (var4 HeapObject) (var5 sll) (var6 Addr) (var7 Addr) (var8 Heap) (var9 HeapObject) (var10 sll) (var11 Addr) (var12 Addr) (var13 Heap)) (or (not (and (inv_main2403_5 var13 var12 var11) (and (and (and (and (and (and (and (and (and (= (O_sll var10) var9) (valid var8 var11)) (= (sll var7) var10)) (= (sll var6) var5)) (= (O_sll var5) var4)) (= nullAddr var6)) (= (write var3 var7 var4) var8)) (= (O_sll var2) var1)) (= (AllocResHeap var3 var7) var0)) (= (alloc var13 var1) var0)))) (Inv_Heap var11 var9))))
(assert (forall ((var0 AllocResHeap) (var1 HeapObject) (var2 sll) (var3 Heap) (var4 HeapObject) (var5 sll) (var6 Addr) (var7 Addr) (var8 Heap) (var9 HeapObject) (var10 sll) (var11 Addr) (var12 sll) (var13 Heap) (var14 Addr) (var15 Heap) (var16 HeapObject) (var17 Addr)) (or (not (and (and (Inv_Heap var17 var16) (inv_main2403_5 var15 var14 var17)) (and (and (and (and (and (and (and (and (and (and (and (and (and (and (= (read var13 var17) var16) (= (getsll var16) var12)) (= (|sll::next| var12) var11)) (valid var13 var17)) true) (= (O_sll var10) var9)) (= (write var8 var17 var9) var13)) (= (sll var7) var10)) (= (sll var6) var5)) (= (O_sll var5) var4)) (= nullAddr var6)) (= (write var3 var7 var4) var8)) (= (O_sll var2) var1)) (= (AllocResHeap var3 var7) var0)) (= (alloc var15 var1) var0)))) (inv_main2403_5 var13 var14 var11))))
(assert (forall ((var0 AllocResHeap) (var1 HeapObject) (var2 sll) (var3 Heap) (var4 HeapObject) (var5 sll) (var6 Addr) (var7 Addr) (var8 Heap) (var9 HeapObject) (var10 sll) (var11 Addr) (var12 sll) (var13 HeapObject) (var14 Heap) (var15 Addr) (var16 Addr) (var17 Heap)) (or (not (and (inv_main2403_5 var17 var16 var15) (and (and (and (and (and (and (and (and (and (and (and (and (and (= (read var14 var15) var13) (= (getsll var13) var12)) (= (|sll::next| var12) var11)) (not (valid var14 var15))) (= (O_sll var10) var9)) (= (write var8 var15 var9) var14)) (= (sll var7) var10)) (= (sll var6) var5)) (= (O_sll var5) var4)) (= nullAddr var6)) (= (write var3 var7 var4) var8)) (= (O_sll var2) var1)) (= (AllocResHeap var3 var7) var0)) (= (alloc var17 var1) var0)))) (inv_main2403_5 var14 var16 var11))))
(assert (forall ((var0 AllocResHeap) (var1 Heap) (var2 HeapObject) (var3 sll)) (or (not (and (and (= (O_sll var3) var2) (= (alloc var1 var2) var0)) (= emptyHeap var1))) (Inv_Heap (newAddr var0) var2))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 HeapObject) (var3 sll) (var4 AllocResHeap) (var5 Addr) (var6 Heap) (var7 HeapObject) (var8 sll)) (or (not (and (and (and (and (and (and (and (= (O_sll var8) var7) (valid var6 var5)) (= (AllocResHeap var6 var5) var4)) (= (O_sll var3) var2)) (= (alloc var1 var2) var4)) (= (sll var0) var8)) (= nullAddr var0)) (= emptyHeap var1))) (Inv_Heap var5 var7))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 HeapObject) (var4 sll) (var5 AllocResHeap) (var6 Heap) (var7 Addr) (var8 Heap) (var9 HeapObject) (var10 sll)) (or (not (and (and (and (and (and (and (and (and (= (O_sll var10) var9) (= (write var8 var7 var9) var6)) (= (AllocResHeap var8 var7) var5)) (= (O_sll var4) var3)) (= (alloc var2 var3) var5)) (= (sll var1) var10)) (= nullAddr var1)) (= emptyHeap var2)) (= var0 var7))) (inv_main2403_5 var6 var0 var7))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main2420_9 var4 var3 var2) (and (and (and (= nullAddr var1) (not (= var2 var1))) (= defObj var0)) (valid var4 var3)))) (Inv_Heap var3 var0))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 sll) (var4 Heap) (var5 Addr) (var6 Heap) (var7 HeapObject) (var8 Addr)) (or (not (and (and (Inv_Heap var8 var7) (inv_main2420_9 var6 var5 var8)) (and (and (and (and (and (and (and (and (= (read var4 var8) var7) (= (getsll var7) var3)) (= (|sll::next| var3) var2)) (valid var4 var8)) true) (= nullAddr var1)) (not (= var8 var1))) (= defObj var0)) (= (write var6 var5 var0) var4)))) (inv_main2420_9 var4 var8 var2))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 sll) (var4 HeapObject) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main2420_9 var8 var7 var6) (and (and (and (and (and (and (and (= (read var5 var6) var4) (= (getsll var4) var3)) (= (|sll::next| var3) var2)) (not (valid var5 var6))) (= nullAddr var1)) (not (= var6 var1))) (= defObj var0)) (= (write var8 var7 var0) var5)))) (inv_main2420_9 var5 var6 var2))))
(check-sat)
