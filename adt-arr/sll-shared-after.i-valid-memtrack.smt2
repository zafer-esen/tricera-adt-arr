(set-logic HORN)
(set-info :source |
    Benchmark: C_VC
    Output by Princess (http://www.philipp.ruemmer.org/princess.shtml)
|)
(set-info :status unknown)
(declare-datatype bool ((true) (false)))
;===============================================================================
; Encoding of Heap sorts and operations
;-------------------------------------------------------------------------------
(define-sort Addr() Int)
(declare-datatypes ((AddrRange 0))
                   (((AddrRange (AddrRangeStart Addr) (AddrRangeSize Int)))))

(declare-datatypes ((HeapObject 0) (sll 0))
                   (((O_Int (getInt Int)) (O_UInt (getUInt Int)) (O_Addr (getAddr Addr)) (O_AddrRange (getAddrRange AddrRange)) (O_sll (getsll sll)) (defObj))
                   ((sll (|sll::data| Addr) (|sll::next| Addr)))))
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
(declare-fun inv_main2409_5 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main2433_5 (Heap Addr) Bool)
(declare-fun inv_main2436_5 (Heap Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main2437_5 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main2439_12 (Heap Addr Int) Bool)
(assert (forall ((var0 Addr) (var1 Heap)) (or (not (and (= var1 emptyHeap) (= var0 nullAddr))) (inv_main2433_5 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Bool) (var10 Addr) (var11 sll) (var12 Heap) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Heap) (var21 Heap) (var22 Addr) (var23 Addr) (var24 Addr) (var25 Heap)) (or (not (and (inv_main2409_5 var25 var24 var23 var22) (and (and (and (and (and (and (= var21 var20) (= var19 var18)) (= var17 var16)) (= var15 var14)) (= var13 (|sll::next| (getsll (read var20 var14))))) (and (and (and (and (and (and (= var12 (newHeap (alloc var25 (O_sll var11)))) (or (and var9 (= var10 (newAddr (alloc var25 (O_sll var11))))) (and (not var9) (= var10 var24)))) (= var8 var23)) (= var7 var22)) (= var6 (newAddr (alloc var25 (O_sll var11))))) (and (and (and (and (= var5 (write var12 var6 (O_sll (sll (|sll::data| (getsll (read var12 var6))) nullAddr)))) (= var4 var10)) (= var3 var8)) (= var2 var7)) (= var1 var6))) (not (= var0 0)))) (and (and (and (= var20 (write var5 var2 (O_sll (sll (|sll::data| (getsll (read var5 var2))) var1)))) (= var18 var4)) (= var16 var3)) (= var14 var2))))) (inv_main2409_5 var21 var19 var17 var13))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Bool) (var5 Addr) (var6 sll) (var7 Heap) (var8 Addr) (var9 Heap)) (or (not (and (inv_main2433_5 var9 var8) (and (and (and (= var7 (newHeap (alloc var9 (O_sll var6)))) (or (and var4 (= var5 (newAddr (alloc var9 (O_sll var6))))) (and (not var4) (= var5 var8)))) (= var3 (newAddr (alloc var9 (O_sll var6))))) (and (and (= var2 (write var7 var3 (O_sll (sll (|sll::data| (getsll (read var7 var3))) nullAddr)))) (= var1 var5)) (= var0 var3))))) (inv_main2409_5 var2 var1 var0 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Heap) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Heap)) (or (not (and (inv_main2437_5 var16 var15 var14 var13 var12) (and (and (and (and (and (and (and (= var11 var16) (= var10 var15)) (= var9 var14)) (= var8 var13)) (= var7 var12)) (= var6 (|sll::next| (getsll (read var16 var12))))) (and (and (and (and (and (= var5 (write var11 var7 defObj)) (or (and (= var10 var7) (= var4 nullAddr)) (and (not (= var10 var7)) (= var4 var10)))) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var0 var6))) (not (= var12 nullAddr))))) (inv_main2437_5 var5 var4 var3 var2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main2436_5 var5 var4 var3 var2 var1 var0) (= var1 nullAddr))) (inv_main2437_5 var5 var4 var3 var2 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Heap) (var12 Heap) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Heap)) (or (not (and (inv_main2436_5 var18 var17 var16 var15 var14 var13) (and (and (and (and (and (and (and (and (= var12 var11) (= var10 var9)) (= var8 var7)) (= var6 var5)) (= var4 var3)) (= var2 var1)) (= var0 (|sll::next| (getsll (read var11 var3))))) (not (= var14 nullAddr))) (and (and (and (and (and (= var11 (write var18 var14 (O_sll (sll var13 (|sll::next| (getsll (read var18 var14))))))) (= var9 var17)) (= var7 var16)) (= var5 var15)) (= var3 var14)) (= var1 var13))))) (inv_main2436_5 var12 var10 var8 var6 var0 var2))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Bool) (var9 Addr) (var10 Int) (var11 Heap) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Heap)) (or (not (and (inv_main2409_5 var15 var14 var13 var12) (and (and (and (and (and (= var11 (newHeap (alloc var15 (O_Int var10)))) (or (and var8 (= var9 (newAddr (alloc var15 (O_Int var10))))) (and (not var8) (= var9 var14)))) (= var7 var13)) (= var6 (newAddr (alloc var15 (O_Int var10))))) (and (and (and (= var5 (write var11 var6 (O_Int var4))) (= var3 var9)) (= var2 var7)) (= var1 var6))) (= var0 0)))) (inv_main2436_5 var5 var3 var2 var1 var2 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main2437_5 var9 var8 var7 var6 var5) (and (and (= var5 nullAddr) (and (and (and (= var4 (write var9 var6 defObj)) (or (and (= var8 var6) (= var3 nullAddr)) (and (not (= var8 var6)) (= var3 var8)))) (= var2 var7)) (= var1 var6))) (= var0 0)))) (inv_main2439_12 var4 var3 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap)) (not (and (inv_main2439_12 var2 var1 var0) (not (= var1 nullAddr))))))
(check-sat)
