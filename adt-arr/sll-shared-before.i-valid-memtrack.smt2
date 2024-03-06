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
(declare-fun inv_main2428_5 (Heap Addr) Bool)
(declare-fun inv_main2432_5 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main2433_12 (Heap Addr Int) Bool)
(declare-fun inv_main_3 (Heap Addr Addr Addr Addr Addr) Bool)
(assert (forall ((var0 Addr) (var1 Heap)) (or (not (and (= var1 emptyHeap) (= var0 nullAddr))) (inv_main2428_5 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Int) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Heap) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Bool) (var20 Addr) (var21 sll) (var22 Heap) (var23 Addr) (var24 Addr) (var25 Addr) (var26 Addr) (var27 Addr) (var28 Addr) (var29 Addr) (var30 Addr) (var31 Addr) (var32 Addr) (var33 Addr) (var34 Heap) (var35 Heap) (var36 Addr) (var37 Addr) (var38 Addr) (var39 Addr) (var40 Addr) (var41 Heap)) (or (not (and (inv_main_3 var41 var40 var39 var38 var37 var36) (and (and (and (and (and (and (and (and (= var35 var34) (= var33 var32)) (= var31 var30)) (= var29 var28)) (= var27 var26)) (= var25 var24)) (= var23 (|sll::next| (getsll (read var34 var24))))) (and (and (and (and (and (and (and (and (and (= var22 (newHeap (alloc var41 (O_sll var21)))) (or (and var19 (= var20 (newAddr (alloc var41 (O_sll var21))))) (and (not var19) (= var20 var40)))) (= var18 var39)) (= var17 var38)) (= var16 var37)) (= var15 var36)) (= var14 (newAddr (alloc var41 (O_sll var21))))) (and (and (and (and (and (and (= var13 (write var22 var14 (O_sll (sll (|sll::data| (getsll (read var22 var14))) nullAddr)))) (= var12 var20)) (= var11 var18)) (= var10 var17)) (= var9 var16)) (= var8 var15)) (= var7 var14))) (not (= var6 0))) (and (and (and (and (and (= var5 (write var13 var8 (O_sll (sll (|sll::data| (getsll (read var13 var8))) var7)))) (= var4 var12)) (= var3 var11)) (= var2 var10)) (= var1 var9)) (= var0 var8)))) (and (and (and (and (and (= var34 (write var5 (|sll::next| (getsll (read var5 var0))) (O_sll (sll var2 (|sll::next| (getsll (read var5 (|sll::next| (getsll (read var5 var0)))))))))) (= var32 var4)) (= var30 var3)) (= var28 var2)) (= var26 var1)) (= var24 var0))))) (inv_main_3 var35 var33 var31 var29 var27 var23))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Addr) (var3 Bool) (var4 Addr) (var5 Int) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Heap) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Bool) (var18 Addr) (var19 sll) (var20 Heap) (var21 Heap) (var22 Addr) (var23 Heap)) (or (not (and (inv_main2428_5 var23 var22) (and (and (and (and (and (and (and (and (= var21 (newHeap (alloc var20 (O_sll var19)))) (or (and var17 (= var18 (newAddr (alloc var20 (O_sll var19))))) (and (not var17) (= var18 var16)))) (= var15 var14)) (= var13 var14)) (= var12 (newAddr (alloc var20 (O_sll var19))))) (and (and (and (and (= var11 (write var21 var12 (O_sll (sll (|sll::data| (getsll (read var21 var12))) nullAddr)))) (= var10 var18)) (= var9 var15)) (= var8 var13)) (= var7 var12))) (and (and (= var6 (newHeap (alloc var23 (O_Int var5)))) (or (and var3 (= var4 (newAddr (alloc var23 (O_Int var5))))) (and (not var3) (= var4 var22)))) (= var2 (newAddr (alloc var23 (O_Int var5)))))) (and (and (= var20 (write var6 var2 (O_Int var1))) (= var16 var4)) (= var14 var2))) (= var0 (write var11 var7 (O_sll (sll var8 (|sll::next| (getsll (read var11 var7)))))))))) (inv_main_3 var0 var10 var9 var8 var7 var7))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Heap) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Heap)) (or (not (and (inv_main2432_5 var16 var15 var14 var13 var12) (and (and (and (and (and (and (and (= var11 var16) (= var10 var15)) (= var9 var14)) (= var8 var13)) (= var7 var12)) (= var6 (|sll::next| (getsll (read var16 var12))))) (and (and (and (and (and (= var5 (write var11 var7 defObj)) (or (and (= var10 var7) (= var4 nullAddr)) (and (not (= var10 var7)) (= var4 var10)))) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var0 var6))) (not (= var12 nullAddr))))) (inv_main2432_5 var5 var4 var3 var2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main_3 var10 var9 var8 var7 var6 var5) (and (= var4 0) (and (and (and (= var3 (write var10 var8 defObj)) (or (and (= var9 var8) (= var2 nullAddr)) (and (not (= var9 var8)) (= var2 var9)))) (= var1 var8)) (= var0 var6))))) (inv_main2432_5 var3 var2 var1 var0 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main2432_5 var5 var4 var3 var2 var1) (and (= var1 nullAddr) (= var0 0)))) (inv_main2433_12 var5 var4 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap)) (not (and (inv_main2433_12 var2 var1 var0) (not (= var1 nullAddr))))))
(check-sat)
