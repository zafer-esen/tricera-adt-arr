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
(declare-fun inv_main2446_5 (Heap Addr) Bool)
(declare-fun inv_main2447_5 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main2449_12 (Heap Addr Int) Bool)
(declare-fun inv_main_19 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main_4 (Heap Addr Addr Addr Addr Addr) Bool)
(assert (forall ((var0 Addr) (var1 Heap)) (or (not (and (= var1 emptyHeap) (= var0 nullAddr))) (inv_main2446_5 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap) (var10 Heap) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Heap)) (or (not (and (inv_main2447_5 var14 var13 var12 var11) (and (and (and (and (and (= var10 var9) (= var8 var7)) (= var6 var5)) (= var4 var3)) (= var2 (|sll::next| (getsll (read var9 var3))))) (and (and (and (and (and (and (= var9 var14) (= var7 var13)) (= var5 var12)) (= var3 var11)) (= var1 (|sll::data1| (getsll (read var14 var11))))) (= var0 (|sll::data2| (getsll (read var14 var11))))) (not (= var11 nullAddr)))))) (inv_main2447_5 var10 var8 var6 var2))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main_4 var6 var5 var4 var3 var2 var1) (= var0 0))) (inv_main2447_5 var6 var5 var4 var4))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main_19 var4 var3 var2 var1) (and (= var1 nullAddr) (= var0 0)))) (inv_main2449_12 var4 var3 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Heap) (var12 Int) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Heap) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Addr) (var25 Bool) (var26 Addr) (var27 sll) (var28 Heap) (var29 Addr) (var30 Addr) (var31 Addr) (var32 Addr) (var33 Addr) (var34 Addr) (var35 Addr) (var36 Addr) (var37 Addr) (var38 Addr) (var39 Addr) (var40 Heap) (var41 Heap) (var42 Addr) (var43 Addr) (var44 Addr) (var45 Addr) (var46 Addr) (var47 Heap)) (or (not (and (inv_main_4 var47 var46 var45 var44 var43 var42) (and (and (and (and (and (and (and (and (= var41 var40) (= var39 var38)) (= var37 var36)) (= var35 var34)) (= var33 var32)) (= var31 var30)) (= var29 (|sll::next| (getsll (read var40 var34))))) (and (and (and (and (and (and (and (and (and (and (= var28 (newHeap (alloc var47 (O_sll var27)))) (or (and var25 (= var26 (newAddr (alloc var47 (O_sll var27))))) (and (not var25) (= var26 var46)))) (= var24 var45)) (= var23 var44)) (= var22 var43)) (= var21 var42)) (= var20 (newAddr (alloc var47 (O_sll var27))))) (and (and (and (and (and (and (= var19 (write var28 var20 (O_sll (sll (|sll::data1| (getsll (read var28 var20))) nullAddr (|sll::data2| (getsll (read var28 var20))))))) (= var18 var26)) (= var17 var24)) (= var16 var23)) (= var15 var22)) (= var14 var21)) (= var13 var20))) (not (= var12 0))) (and (and (and (and (and (= var11 (write var19 var16 (O_sll (sll (|sll::data1| (getsll (read var19 var16))) var13 (|sll::data2| (getsll (read var19 var16))))))) (= var10 var18)) (= var9 var17)) (= var8 var16)) (= var7 var15)) (= var6 var14))) (and (and (and (and (and (= var5 (write var11 (|sll::next| (getsll (read var11 var8))) (O_sll (sll var7 (|sll::next| (getsll (read var11 (|sll::next| (getsll (read var11 var8)))))) (|sll::data2| (getsll (read var11 (|sll::next| (getsll (read var11 var8)))))))))) (= var4 var10)) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var0 var6)))) (and (and (and (and (and (= var40 (write var5 (|sll::next| (getsll (read var5 var2))) (O_sll (sll (|sll::data1| (getsll (read var5 (|sll::next| (getsll (read var5 var2)))))) (|sll::next| (getsll (read var5 (|sll::next| (getsll (read var5 var2)))))) var0)))) (= var38 var4)) (= var36 var3)) (= var34 var2)) (= var32 var1)) (= var30 var0))))) (inv_main_4 var41 var39 var37 var29 var33 var31))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Bool) (var3 Addr) (var4 sll) (var5 Heap) (var6 Int) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Bool) (var13 Addr) (var14 Int) (var15 Heap) (var16 Heap) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Heap) (var23 Addr) (var24 Addr) (var25 Addr) (var26 Addr) (var27 Addr) (var28 Int) (var29 Heap) (var30 Addr) (var31 Addr) (var32 Addr) (var33 Addr) (var34 Addr) (var35 Addr) (var36 Addr) (var37 Addr) (var38 Bool) (var39 Addr) (var40 Int) (var41 Heap) (var42 Heap) (var43 Addr) (var44 Heap)) (or (not (and (inv_main2446_5 var44 var43) (and (and (and (and (and (and (and (and (and (and (and (= var42 (newHeap (alloc var41 (O_Int var40)))) (or (and var38 (= var39 (newAddr (alloc var41 (O_Int var40))))) (and (not var38) (= var39 var37)))) (= var36 var35)) (= var34 var33)) (= var32 var31)) (= var30 (newAddr (alloc var41 (O_Int var40))))) (and (and (and (and (and (= var29 (write var42 var30 (O_Int var28))) (= var27 var39)) (= var26 var36)) (= var25 var34)) (= var24 var32)) (= var23 var30))) (and (and (and (and (and (= var22 (write var29 var25 (O_sll (sll var24 (|sll::next| (getsll (read var29 var25))) (|sll::data2| (getsll (read var29 var25))))))) (= var21 var27)) (= var20 var26)) (= var19 var25)) (= var18 var24)) (= var17 var23))) (and (and (and (and (= var16 (newHeap (alloc var15 (O_Int var14)))) (or (and var12 (= var13 (newAddr (alloc var15 (O_Int var14))))) (and (not var12) (= var13 var11)))) (= var10 var9)) (= var8 var9)) (= var7 (newAddr (alloc var15 (O_Int var14)))))) (and (and (and (and (= var41 (write var16 var7 (O_Int var6))) (= var37 var13)) (= var35 var10)) (= var33 var8)) (= var31 var7))) (and (and (and (= var5 (newHeap (alloc var44 (O_sll var4)))) (or (and var2 (= var3 (newAddr (alloc var44 (O_sll var4))))) (and (not var2) (= var3 var43)))) (= var1 (newAddr (alloc var44 (O_sll var4))))) (and (and (= var15 (write var5 var1 (O_sll (sll (|sll::data1| (getsll (read var5 var1))) nullAddr (|sll::data2| (getsll (read var5 var1))))))) (= var11 var3)) (= var9 var1)))) (= var0 (write var22 var19 (O_sll (sll (|sll::data1| (getsll (read var22 var19))) (|sll::next| (getsll (read var22 var19))) var17))))))) (inv_main_4 var0 var21 var20 var19 var18 var17))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Heap)) (or (not (and (inv_main_19 var13 var12 var11 var10) (and (and (and (and (and (and (= var9 var13) (= var8 var12)) (= var7 var11)) (= var6 var10)) (= var5 (|sll::next| (getsll (read var13 var10))))) (and (and (and (and (= var4 (write var9 var6 defObj)) (or (and (= var8 var6) (= var3 nullAddr)) (and (not (= var8 var6)) (= var3 var8)))) (= var2 var7)) (= var1 var6)) (= var0 var5))) (not (= var10 nullAddr))))) (inv_main_19 var4 var3 var2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main2447_5 var3 var2 var1 var0) (and (= var1 nullAddr) (= var0 nullAddr)))) (inv_main_19 var3 var2 var1 var1))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main2447_5 var9 var8 var7 var6) (and (and (and (and (not (= var7 nullAddr)) (and (and (and (= var5 (write var9 (|sll::data1| (getsll (read var9 var7))) defObj)) (or (and (= var8 (|sll::data1| (getsll (read var9 var7)))) (= var4 nullAddr)) (and (not (= var8 (|sll::data1| (getsll (read var9 var7))))) (= var4 var8)))) (= var3 var7)) (= var2 var7))) (= var6 nullAddr)) (= var1 (write var5 (|sll::data2| (getsll (read var5 var2))) defObj))) (or (and (= var4 (|sll::data2| (getsll (read var5 var2)))) (= var0 nullAddr)) (and (not (= var4 (|sll::data2| (getsll (read var5 var2))))) (= var0 var4)))))) (inv_main_19 var1 var0 var3 var2))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap)) (not (and (inv_main2449_12 var2 var1 var0) (not (= var1 nullAddr))))))
(check-sat)
