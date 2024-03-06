(set-logic HORN)
(set-info :source |
    Benchmark: C_VC
    Output by Princess (http://www.philipp.ruemmer.org/princess.shtml)
|)
(set-info :status unsat)
(declare-datatype bool ((true) (false)))
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
(declare-fun inv_main547_5 (Heap Addr TData) Bool)
(declare-fun inv_main549_12 (Heap Addr Int) Bool)
(assert (forall ((var0 TData) (var1 Addr) (var2 Heap)) (or (not (and (= var2 emptyHeap) (= var1 nullAddr))) (inv_main547_5 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 TData) (var4 Addr) (var5 Heap) (var6 Int) (var7 TData) (var8 Addr) (var9 Heap) (var10 Addr) (var11 Int) (var12 TData) (var13 Bool) (var14 Addr) (var15 Int) (var16 Heap) (var17 Addr) (var18 Int) (var19 Int) (var20 TData) (var21 TData) (var22 Addr) (var23 Bool) (var24 Addr) (var25 Int) (var26 Heap) (var27 Heap) (var28 Int) (var29 TData) (var30 Addr) (var31 Heap) (var32 TData) (var33 Addr) (var34 Heap) (var35 Addr) (var36 Int) (var37 TData) (var38 Addr) (var39 Heap) (var40 Addr) (var41 Addr) (var42 Int) (var43 TData) (var44 Addr) (var45 Heap) (var46 Int) (var47 Addr) (var48 Addr) (var49 Addr) (var50 Addr) (var51 Int) (var52 Int) (var53 TData) (var54 TData) (var55 Addr) (var56 Addr) (var57 Heap) (var58 Heap) (var59 TData) (var60 Addr) (var61 Heap)) (or (not (and (inv_main547_5 var61 var60 var59) (and (and (and (and (and (and (and (and (and (and (= var58 var57) (= var56 var55)) (= var54 (TData nullAddr (|TData::hi| var53)))) (= var52 var51)) (= var50 var49)) (= var48 var47)) (and (and (not (<= 0 (+ var46 (* (- 1) (getInt (read var57 var47)))))) (and (and (and (and (and (and (= var57 var45) (= var55 var44)) (= var53 var43)) (= var51 var42)) (= var49 var41)) (= var47 var40)) (= var46 (getInt (read var45 var41))))) (and (and (and (and (and (= var45 var39) (= var44 var38)) (= var43 var37)) (= var42 var36)) (= var41 var35)) (= var40 (|TData::hi| var37))))) (and (and (and (and (= var39 var34) (= var38 var33)) (= var37 var32)) (= var36 2)) (= var35 (|TData::lo| var32)))) (and (and (and (= var31 var58) (= var30 var56)) (= var29 (TData (|TData::lo| var54) nullAddr))) (= var28 var52))) (and (and (and (and (and (and (and (and (and (= var27 (newHeap (alloc var26 (O_Int var25)))) (or (and var23 (= var24 (newAddr (alloc var26 (O_Int var25))))) (and (not var23) (= var24 var22)))) (= var21 var20)) (= var19 var18)) (= var17 (newAddr (alloc var26 (O_Int var25))))) (and (and (and (and (= var16 (newHeap (alloc var61 (O_Int var15)))) (or (and var13 (= var14 (newAddr (alloc var61 (O_Int var15))))) (and (not var13) (= var14 var60)))) (= var12 var59)) (= var11 2)) (= var10 (newAddr (alloc var61 (O_Int var15)))))) (and (and (and (= var26 var16) (= var22 var14)) (= var20 (TData var10 (|TData::hi| var12)))) (= var18 var11))) (and (and (and (= var9 var27) (= var8 var24)) (= var7 (TData (|TData::lo| var21) var17))) (= var6 var19))) (and (and (and (= var5 (write var9 (|TData::lo| var7) (O_Int 4))) (= var4 var8)) (= var3 var7)) (= var2 var6))) (and (and (and (= var34 (write var5 (|TData::hi| var3) (O_Int 8))) (= var33 var4)) (= var32 var3)) (= var1 var2)))) (= var0 0)))) (inv_main549_12 var31 var30 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 TData) (var4 Addr) (var5 Heap) (var6 Int) (var7 TData) (var8 Addr) (var9 Heap) (var10 Addr) (var11 Int) (var12 TData) (var13 Bool) (var14 Addr) (var15 Int) (var16 Heap) (var17 Addr) (var18 Int) (var19 Int) (var20 TData) (var21 TData) (var22 Addr) (var23 Bool) (var24 Addr) (var25 Int) (var26 Heap) (var27 Heap) (var28 Int) (var29 TData) (var30 Addr) (var31 Heap) (var32 TData) (var33 Addr) (var34 Heap) (var35 Addr) (var36 Addr) (var37 Int) (var38 TData) (var39 Addr) (var40 Heap) (var41 Addr) (var42 Int) (var43 TData) (var44 Addr) (var45 Heap) (var46 Addr) (var47 Addr) (var48 Addr) (var49 Int) (var50 Int) (var51 TData) (var52 TData) (var53 Addr) (var54 Addr) (var55 Heap) (var56 Addr) (var57 Heap) (var58 Int) (var59 Addr) (var60 Addr) (var61 Addr) (var62 Addr) (var63 Int) (var64 Int) (var65 TData) (var66 TData) (var67 Addr) (var68 Addr) (var69 Heap) (var70 Heap) (var71 TData) (var72 Addr) (var73 Heap)) (or (not (and (inv_main547_5 var73 var72 var71) (and (and (and (and (and (and (and (and (and (and (and (= var70 var69) (= var68 var67)) (= var66 (TData nullAddr (|TData::hi| var65)))) (= var64 var63)) (= var62 var61)) (= var60 var59)) (and (and (and (<= 0 (+ var58 (* (- 1) (getInt (read var57 var56))))) (and (and (and (and (and (and (= var57 var55) (= var54 var53)) (= var52 var51)) (= var50 var49)) (= var48 var47)) (= var56 var46)) (= var58 (getInt (read var55 var47))))) (and (and (and (and (and (= var55 var45) (= var53 var44)) (= var51 var43)) (= var49 var42)) (= var47 var41)) (= var46 (|TData::hi| var43)))) (and (and (and (and (and (= var40 (write var57 var48 defObj)) (or (and (= var54 var48) (= var39 nullAddr)) (and (not (= var54 var48)) (= var39 var54)))) (= var38 var52)) (= var37 var50)) (= var36 var48)) (= var35 var56)))) (and (and (and (and (and (= var69 (write var40 var35 defObj)) (or (and (= var39 var35) (= var67 nullAddr)) (and (not (= var39 var35)) (= var67 var39)))) (= var65 var38)) (= var63 var37)) (= var61 var36)) (= var59 var35))) (and (and (and (and (= var45 var34) (= var44 var33)) (= var43 var32)) (= var42 2)) (= var41 (|TData::lo| var32)))) (and (and (and (= var31 var70) (= var30 var68)) (= var29 (TData (|TData::lo| var66) nullAddr))) (= var28 var64))) (and (and (and (and (and (and (and (and (and (= var27 (newHeap (alloc var26 (O_Int var25)))) (or (and var23 (= var24 (newAddr (alloc var26 (O_Int var25))))) (and (not var23) (= var24 var22)))) (= var21 var20)) (= var19 var18)) (= var17 (newAddr (alloc var26 (O_Int var25))))) (and (and (and (and (= var16 (newHeap (alloc var73 (O_Int var15)))) (or (and var13 (= var14 (newAddr (alloc var73 (O_Int var15))))) (and (not var13) (= var14 var72)))) (= var12 var71)) (= var11 2)) (= var10 (newAddr (alloc var73 (O_Int var15)))))) (and (and (and (= var26 var16) (= var22 var14)) (= var20 (TData var10 (|TData::hi| var12)))) (= var18 var11))) (and (and (and (= var9 var27) (= var8 var24)) (= var7 (TData (|TData::lo| var21) var17))) (= var6 var19))) (and (and (and (= var5 (write var9 (|TData::lo| var7) (O_Int 4))) (= var4 var8)) (= var3 var7)) (= var2 var6))) (and (and (and (= var34 (write var5 (|TData::hi| var3) (O_Int 8))) (= var33 var4)) (= var32 var3)) (= var1 var2)))) (= var0 0)))) (inv_main549_12 var31 var30 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap)) (not (and (inv_main549_12 var2 var1 var0) (not (= var1 nullAddr))))))
(check-sat)
