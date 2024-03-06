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
(declare-fun inv_main2421_9 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main2428_5 (Heap) Bool)
(declare-fun inv_main2430_5 (Heap Addr Addr) Bool)
(declare-fun inv_main_3 (Heap Addr Addr Addr Addr) Bool)
(assert (forall ((var0 Heap)) (or (not (= var0 emptyHeap)) (inv_main2428_5 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Int) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Heap) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 sll) (var18 Heap) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Addr) (var25 Addr) (var26 Addr) (var27 Addr) (var28 Heap) (var29 Heap) (var30 Addr) (var31 Addr) (var32 Addr) (var33 Addr) (var34 Heap)) (or (not (and (inv_main_3 var34 var33 var32 var31 var30) (and (and (and (and (and (and (and (= var29 var28) (= var27 var26)) (= var25 var24)) (= var23 var22)) (= var21 var20)) (= var19 (|sll::next| (getsll (read var28 var20))))) (and (and (and (and (and (and (and (and (= var18 (newHeap (alloc var34 (O_sll var17)))) (= var16 var33)) (= var15 var32)) (= var14 var31)) (= var13 var30)) (= var12 (newAddr (alloc var34 (O_sll var17))))) (and (and (and (and (and (= var11 (write var18 var12 (O_sll (sll (|sll::data| (getsll (read var18 var12))) nullAddr)))) (= var10 var16)) (= var9 var15)) (= var8 var14)) (= var7 var13)) (= var6 var12))) (not (= var5 0))) (and (and (and (and (= var4 (write var11 var7 (O_sll (sll (|sll::data| (getsll (read var11 var7))) var6)))) (= var3 var10)) (= var2 var9)) (= var1 var8)) (= var0 var7)))) (and (and (and (and (= var28 (write var4 (|sll::next| (getsll (read var4 var0))) (O_sll (sll var2 (|sll::next| (getsll (read var4 (|sll::next| (getsll (read var4 var0)))))))))) (= var26 var3)) (= var24 var2)) (= var22 var1)) (= var20 var0))))) (inv_main_3 var29 var27 var25 var23 var19))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Addr) (var3 Int) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 sll) (var14 Heap) (var15 Heap) (var16 Heap)) (or (not (and (inv_main2428_5 var16) (and (and (and (and (and (and (and (= var15 (newHeap (alloc var14 (O_sll var13)))) (= var12 var11)) (= var10 var11)) (= var9 (newAddr (alloc var14 (O_sll var13))))) (and (and (and (= var8 (write var15 var9 (O_sll (sll (|sll::data| (getsll (read var15 var9))) nullAddr)))) (= var7 var12)) (= var6 var10)) (= var5 var9))) (and (= var4 (newHeap (alloc var16 (O_Int var3)))) (= var2 (newAddr (alloc var16 (O_Int var3)))))) (and (= var14 (write var4 var2 (O_Int var1))) (= var11 var2))) (= var0 (write var8 var5 (O_sll (sll var6 (|sll::next| (getsll (read var8 var5)))))))))) (inv_main_3 var0 var7 var6 var5 var5))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main_3 var5 var4 var3 var2 var1) (= var0 0))) (inv_main2430_5 var5 var4 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main2421_9 var10 var9 var8 var7 var6) (and (and (not (= var5 nullAddr)) (and (and (and (and (= var4 (write var10 var7 defObj)) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var5 var6))) (= var0 (|sll::next| (getsll (read var4 var5))))))) (inv_main2421_9 var4 var3 var2 var5 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main2430_5 var6 var5 var4) (and (and (not (= var3 nullAddr)) (and (and (= var2 (write var6 var5 defObj)) (= var1 var5)) (= var3 var4))) (= var0 (|sll::next| (getsll (read var2 var3))))))) (inv_main2421_9 var2 var1 var3 var3 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main2430_5 var2 var1 var0) (and (not (= var1 nullAddr)) (= (read var2 var1) defObj))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main2421_9 var4 var3 var2 var1 var0) (and (not (= var1 nullAddr)) (= (read var4 var1) defObj))))))
(check-sat)
