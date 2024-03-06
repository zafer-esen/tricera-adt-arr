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
                   ((sll (|sll::next| Addr) (|sll::data| Addr)))))
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
(declare-fun inv_main2428_9 (Heap Addr Addr) Bool)
(declare-fun inv_main2431_9 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main2438_5 (Heap) Bool)
(declare-fun inv_main2439_5 (Heap Addr Addr) Bool)
(declare-fun inv_main_2 (Heap Addr Addr Addr) Bool)
(assert (forall ((var0 Heap)) (or (not (= var0 emptyHeap)) (inv_main2438_5 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 sll) (var15 Heap) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Heap) (var24 Heap) (var25 Addr) (var26 Addr) (var27 Addr) (var28 Heap)) (or (not (and (inv_main_2 var28 var27 var26 var25) (and (and (and (and (and (and (= var24 var23) (= var22 var21)) (= var20 var19)) (= var18 var17)) (= var16 (|sll::next| (getsll (read var23 var19))))) (and (and (and (and (and (and (and (= var15 (newHeap (alloc var28 (O_sll var14)))) (= var13 var27)) (= var12 var26)) (= var11 var25)) (= var10 (newAddr (alloc var28 (O_sll var14))))) (and (and (and (and (= var9 (write var15 var10 (O_sll (sll nullAddr (|sll::data| (getsll (read var15 var10))))))) (= var8 var13)) (= var7 var12)) (= var6 var11)) (= var5 var10))) (not (= var4 0))) (and (and (and (= var3 (write var9 var7 (O_sll (sll var5 (|sll::data| (getsll (read var9 var7))))))) (= var2 var8)) (= var1 var7)) (= var0 var6)))) (and (and (and (= var23 (write var3 (|sll::next| (getsll (read var3 var1))) (O_sll (sll (|sll::next| (getsll (read var3 (|sll::next| (getsll (read var3 var1)))))) var0)))) (= var21 var2)) (= var19 var1)) (= var17 var0))))) (inv_main_2 var24 var22 var16 var18))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 sll) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Int) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Int) (var14 Heap) (var15 Heap) (var16 Heap)) (or (not (and (inv_main2438_5 var16) (and (and (and (and (and (and (= var15 (newHeap (alloc var14 (O_Int var13)))) (= var12 var11)) (= var10 var11)) (= var9 (newAddr (alloc var14 (O_Int var13))))) (and (and (and (= var8 (write var15 var9 (O_Int var7))) (= var6 var12)) (= var5 var10)) (= var4 var9))) (and (and (= var3 (newHeap (alloc var16 (O_sll var2)))) (= var1 (newAddr (alloc var16 (O_sll var2))))) (and (= var14 (write var3 var1 (O_sll (sll nullAddr (|sll::data| (getsll (read var3 var1))))))) (= var11 var1)))) (= var0 (write var8 var5 (O_sll (sll (|sll::next| (getsll (read var8 var5))) var4))))))) (inv_main_2 var0 var6 var5 var4))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main2439_5 var10 var9 var8) (and (and (and (and (= var7 var6) (= var5 var4)) (= var3 var2)) (= var1 (|sll::next| (getsll (read var6 var2))))) (and (and (and (and (= var6 var10) (= var4 var9)) (= var2 var8)) (= var0 (|sll::data| (getsll (read var10 var8))))) (not (= var8 nullAddr)))))) (inv_main2439_5 var7 var5 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main_2 var4 var3 var2 var1) (= var0 0))) (inv_main2439_5 var4 var3 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main2428_9 var6 var5 var4) (and (and (not (= var3 nullAddr)) (and (and (= var2 (write var6 (|sll::data| (getsll (read var6 var4))) defObj)) (= var1 var5)) (= var3 var4))) (= var0 (|sll::next| (getsll (read var2 var3))))))) (inv_main2431_9 var2 var1 var3 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main2431_9 var8 var7 var6 var5) (and (and (not (= var4 nullAddr)) (and (and (and (= var3 (write var8 var6 defObj)) (= var2 var7)) (= var1 var6)) (= var4 var5))) (= var0 (|sll::next| (getsll (read var3 var4))))))) (inv_main2431_9 var3 var2 var4 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main2439_5 var3 var2 var1) (and (and (not (= var2 nullAddr)) (and (= var2 nullAddr) (= var1 nullAddr))) (= var0 (|sll::next| (getsll (read var3 var2))))))) (inv_main2431_9 var3 var2 var2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (and (inv_main2439_5 var2 var1 var0) (and (not (= var1 nullAddr)) (= var0 nullAddr)))) (inv_main2428_9 var2 var1 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main2428_9 var2 var1 var0) (and (not (= (|sll::data| (getsll (read var2 var0))) nullAddr)) (= (read var2 (|sll::data| (getsll (read var2 var0)))) defObj))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main2431_9 var3 var2 var1 var0) (and (not (= var1 nullAddr)) (= (read var3 var1) defObj))))))
(check-sat)
