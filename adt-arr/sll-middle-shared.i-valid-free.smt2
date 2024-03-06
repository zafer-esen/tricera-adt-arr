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
                   ((sll (|sll::data1| Addr) (|sll::next| Addr) (|sll::data2| Addr)))))
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
(declare-fun inv_main2434_9 (Heap Addr Addr) Bool)
(declare-fun inv_main2439_9 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main2446_5 (Heap) Bool)
(declare-fun inv_main2447_5 (Heap Addr Addr) Bool)
(declare-fun inv_main_21 (Heap Addr Addr) Bool)
(declare-fun inv_main_4 (Heap Addr Addr Addr Addr) Bool)
(assert (forall ((var0 Heap)) (or (not (= var0 emptyHeap)) (inv_main2446_5 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap) (var10 Int) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Heap) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Addr) (var22 sll) (var23 Heap) (var24 Addr) (var25 Addr) (var26 Addr) (var27 Addr) (var28 Addr) (var29 Addr) (var30 Addr) (var31 Addr) (var32 Addr) (var33 Heap) (var34 Heap) (var35 Addr) (var36 Addr) (var37 Addr) (var38 Addr) (var39 Heap)) (or (not (and (inv_main_4 var39 var38 var37 var36 var35) (and (and (and (and (and (and (and (= var34 var33) (= var32 var31)) (= var30 var29)) (= var28 var27)) (= var26 var25)) (= var24 (|sll::next| (getsll (read var33 var29))))) (and (and (and (and (and (and (and (and (and (= var23 (newHeap (alloc var39 (O_sll var22)))) (= var21 var38)) (= var20 var37)) (= var19 var36)) (= var18 var35)) (= var17 (newAddr (alloc var39 (O_sll var22))))) (and (and (and (and (and (= var16 (write var23 var17 (O_sll (sll (|sll::data1| (getsll (read var23 var17))) nullAddr (|sll::data2| (getsll (read var23 var17))))))) (= var15 var21)) (= var14 var20)) (= var13 var19)) (= var12 var18)) (= var11 var17))) (not (= var10 0))) (and (and (and (and (= var9 (write var16 var14 (O_sll (sll (|sll::data1| (getsll (read var16 var14))) var11 (|sll::data2| (getsll (read var16 var14))))))) (= var8 var15)) (= var7 var14)) (= var6 var13)) (= var5 var12))) (and (and (and (and (= var4 (write var9 (|sll::next| (getsll (read var9 var7))) (O_sll (sll var6 (|sll::next| (getsll (read var9 (|sll::next| (getsll (read var9 var7)))))) (|sll::data2| (getsll (read var9 (|sll::next| (getsll (read var9 var7)))))))))) (= var3 var8)) (= var2 var7)) (= var1 var6)) (= var0 var5)))) (and (and (and (and (= var33 (write var4 (|sll::next| (getsll (read var4 var2))) (O_sll (sll (|sll::data1| (getsll (read var4 (|sll::next| (getsll (read var4 var2)))))) (|sll::next| (getsll (read var4 (|sll::next| (getsll (read var4 var2)))))) var0)))) (= var31 var3)) (= var29 var2)) (= var27 var1)) (= var25 var0))))) (inv_main_4 var34 var32 var24 var28 var26))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 sll) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Int) (var10 Heap) (var11 Heap) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Heap) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Int) (var22 Heap) (var23 Addr) (var24 Addr) (var25 Addr) (var26 Addr) (var27 Addr) (var28 Addr) (var29 Addr) (var30 Int) (var31 Heap) (var32 Heap) (var33 Heap)) (or (not (and (inv_main2446_5 var33) (and (and (and (and (and (and (and (and (and (and (= var32 (newHeap (alloc var31 (O_Int var30)))) (= var29 var28)) (= var27 var26)) (= var25 var24)) (= var23 (newAddr (alloc var31 (O_Int var30))))) (and (and (and (and (= var22 (write var32 var23 (O_Int var21))) (= var20 var29)) (= var19 var27)) (= var18 var25)) (= var17 var23))) (and (and (and (and (= var16 (write var22 var19 (O_sll (sll var18 (|sll::next| (getsll (read var22 var19))) (|sll::data2| (getsll (read var22 var19))))))) (= var15 var20)) (= var14 var19)) (= var13 var18)) (= var12 var17))) (and (and (and (= var11 (newHeap (alloc var10 (O_Int var9)))) (= var8 var7)) (= var6 var7)) (= var5 (newAddr (alloc var10 (O_Int var9)))))) (and (and (and (= var31 (write var11 var5 (O_Int var4))) (= var28 var8)) (= var26 var6)) (= var24 var5))) (and (and (= var3 (newHeap (alloc var33 (O_sll var2)))) (= var1 (newAddr (alloc var33 (O_sll var2))))) (and (= var10 (write var3 var1 (O_sll (sll (|sll::data1| (getsll (read var3 var1))) nullAddr (|sll::data2| (getsll (read var3 var1))))))) (= var7 var1)))) (= var0 (write var16 var14 (O_sll (sll (|sll::data1| (getsll (read var16 var14))) (|sll::next| (getsll (read var16 var14))) var12))))))) (inv_main_4 var0 var15 var14 var13 var12))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main_21 var6 var5 var4) (and (and (not (= var3 nullAddr)) (and (and (= var2 (write var6 (|sll::data2| (getsll (read var6 var4))) defObj)) (= var1 var5)) (= var3 var4))) (= var0 (|sll::next| (getsll (read var2 var3))))))) (inv_main2439_9 var2 var1 var3 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main2439_9 var8 var7 var6 var5) (and (and (not (= var4 nullAddr)) (and (and (and (= var3 (write var8 var6 defObj)) (= var2 var7)) (= var1 var6)) (= var4 var5))) (= var0 (|sll::next| (getsll (read var3 var4))))))) (inv_main2439_9 var3 var2 var4 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main2447_5 var3 var2 var1) (and (and (not (= var2 nullAddr)) (and (= var2 nullAddr) (= var1 nullAddr))) (= var0 (|sll::next| (getsll (read var3 var2))))))) (inv_main2439_9 var3 var2 var2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Heap)) (or (not (and (inv_main2447_5 var11 var10 var9) (and (and (and (and (= var8 var7) (= var6 var5)) (= var4 var3)) (= var2 (|sll::next| (getsll (read var7 var3))))) (and (and (and (and (and (= var7 var11) (= var5 var10)) (= var3 var9)) (= var1 (|sll::data1| (getsll (read var11 var9))))) (= var0 (|sll::data2| (getsll (read var11 var9))))) (not (= var9 nullAddr)))))) (inv_main2447_5 var8 var6 var2))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main_4 var5 var4 var3 var2 var1) (= var0 0))) (inv_main2447_5 var5 var4 var4))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (and (inv_main2447_5 var2 var1 var0) (and (not (= var1 nullAddr)) (= var0 nullAddr)))) (inv_main2434_9 var2 var1 var1))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main2434_9 var3 var2 var1) (= var0 (write var3 (|sll::data1| (getsll (read var3 var1))) defObj)))) (inv_main_21 var0 var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main2434_9 var2 var1 var0) (and (not (= (|sll::data1| (getsll (read var2 var0))) nullAddr)) (= (read var2 (|sll::data1| (getsll (read var2 var0)))) defObj))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_21 var2 var1 var0) (and (not (= (|sll::data2| (getsll (read var2 var0))) nullAddr)) (= (read var2 (|sll::data2| (getsll (read var2 var0)))) defObj))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main2439_9 var3 var2 var1 var0) (and (not (= var1 nullAddr)) (= (read var3 var1) defObj))))))
(check-sat)
