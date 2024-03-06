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

(declare-datatypes ((HeapObject 0) (list 0))
                   (((O_Int (getInt Int)) (O_UInt (getUInt Int)) (O_Addr (getAddr Addr)) (O_AddrRange (getAddrRange AddrRange)) (O_list (getlist list)) (defObj))
                   ((list (|list::key| Int) (|list::next| Addr)))))
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
(declare-fun inv_main14_7 (Heap Int Addr Int Addr Addr Int) Bool)
(declare-fun inv_main780_17 (Heap Int Addr Int Addr Addr Addr Addr) Bool)
(declare-fun inv_main807_2 (Heap Int Addr Int Addr Addr) Bool)
(declare-fun inv_main_43 (Heap Int Addr Int Addr Addr) Bool)
(declare-fun inv_main_47 (Heap Int Addr Int Addr Addr Addr Int) Bool)
(declare-fun inv_main_60 (Heap Int Addr Int Addr Addr) Bool)
(declare-fun inv_main_7 (Heap Int Addr Int Addr Addr) Bool)
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Addr) (var5 Int) (var6 Heap) (var7 Addr) (var8 Int) (var9 Heap)) (or (not (and (and (and (= var9 emptyHeap) (= var8 0)) (= var7 nullAddr)) (and (and (and (and (= var6 var9) (= var5 var8)) (= var4 var7)) (= var3 var2)) (= var1 nullAddr)))) (inv_main807_2 var6 var5 var4 var3 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Int) (var7 Addr) (var8 Int) (var9 Heap) (var10 Addr) (var11 Int) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Int) (var16 Int) (var17 list) (var18 Heap) (var19 Addr) (var20 Int) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Int) (var25 Addr) (var26 Int) (var27 Heap) (var28 Int) (var29 Addr) (var30 Addr) (var31 Addr) (var32 Int) (var33 Addr) (var34 Int) (var35 Heap) (var36 Addr) (var37 Int) (var38 Addr) (var39 Addr) (var40 Addr) (var41 Addr) (var42 Addr) (var43 Int) (var44 Int) (var45 Addr) (var46 Int) (var47 Int) (var48 list) (var49 Heap) (var50 Heap) (var51 Addr) (var52 Addr) (var53 Addr) (var54 Int) (var55 Addr) (var56 Int) (var57 Heap)) (or (not (and (inv_main807_2 var57 var56 var55 var54 var53 var52) (and (and (and (and (= var51 nullAddr) (and (and (and (and (and (and (and (and (= var50 (newHeap (alloc var49 (O_list var48)))) (= var47 var46)) (= var51 var45)) (= var44 var43)) (= var42 var41)) (= var40 var39)) (= var38 var41)) (= var37 5)) (= var36 (newAddr (alloc var49 (O_list var48)))))) (and (and (and (and (and (and (and (= var35 (write var50 var36 (O_list (list var37 (|list::next| (getlist (read var50 var36))))))) (= var34 var47)) (= var33 var51)) (= var32 var44)) (= var31 var42)) (= var30 var40)) (= var29 var36)) (= var28 var37))) (and (and (and (and (and (and (and (= var27 (write var35 var29 (O_list (list (|list::key| (getlist (read var35 var29))) nullAddr)))) (= var26 var34)) (= var25 var33)) (= var24 var32)) (= var23 var31)) (= var22 var30)) (= var21 var29)) (= var20 var28))) (and (and (and (= var19 nullAddr) (and (and (and (and (and (and (and (and (= var18 (newHeap (alloc var57 (O_list var17)))) (= var16 var56)) (= var19 var55)) (= var15 var54)) (= var14 var53)) (= var13 var52)) (= var12 var53)) (= var11 2)) (= var10 (newAddr (alloc var57 (O_list var17)))))) (and (and (and (and (and (and (and (= var9 (write var18 var10 (O_list (list var11 (|list::next| (getlist (read var18 var10))))))) (= var8 var16)) (= var7 var19)) (= var6 var15)) (= var5 var14)) (= var4 var13)) (= var3 var10)) (= var2 var11))) (and (and (and (and (and (and (and (= var49 (write var9 var3 (O_list (list (|list::key| (getlist (read var9 var3))) nullAddr)))) (= var46 var8)) (= var1 var7)) (= var43 var6)) (= var41 var5)) (= var39 var4)) (= var45 var3)) (= var0 var2)))))) (inv_main_7 var27 var26 var21 var24 var23 var22))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Int) (var7 Addr) (var8 Int) (var9 Heap) (var10 Addr) (var11 Int) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Int) (var16 Int) (var17 list) (var18 Heap) (var19 Addr) (var20 Int) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Int) (var25 Addr) (var26 Int) (var27 Heap) (var28 Int) (var29 Addr) (var30 Addr) (var31 Addr) (var32 Int) (var33 Addr) (var34 Int) (var35 Heap) (var36 Addr) (var37 Int) (var38 Addr) (var39 Addr) (var40 Addr) (var41 Addr) (var42 Addr) (var43 Int) (var44 Int) (var45 Addr) (var46 Int) (var47 Int) (var48 list) (var49 Heap) (var50 Heap) (var51 Addr) (var52 Addr) (var53 Addr) (var54 Int) (var55 Addr) (var56 Int) (var57 Heap)) (or (not (and (inv_main807_2 var57 var56 var55 var54 var53 var52) (and (and (and (and (not (= var51 nullAddr)) (and (and (and (and (and (and (and (and (= var50 (newHeap (alloc var49 (O_list var48)))) (= var47 var46)) (= var51 var45)) (= var44 var43)) (= var42 var41)) (= var40 var39)) (= var38 var41)) (= var37 5)) (= var36 (newAddr (alloc var49 (O_list var48)))))) (and (and (and (and (and (and (and (= var35 (write var50 var36 (O_list (list var37 (|list::next| (getlist (read var50 var36))))))) (= var34 var47)) (= var33 var51)) (= var32 var44)) (= var31 var42)) (= var30 var40)) (= var29 var36)) (= var28 var37))) (and (and (and (and (and (and (and (= var27 (write var35 var29 (O_list (list (|list::key| (getlist (read var35 var29))) var33)))) (= var26 var34)) (= var25 var33)) (= var24 var32)) (= var23 var31)) (= var22 var30)) (= var21 var29)) (= var20 var28))) (and (and (and (= var19 nullAddr) (and (and (and (and (and (and (and (and (= var18 (newHeap (alloc var57 (O_list var17)))) (= var16 var56)) (= var19 var55)) (= var15 var54)) (= var14 var53)) (= var13 var52)) (= var12 var53)) (= var11 2)) (= var10 (newAddr (alloc var57 (O_list var17)))))) (and (and (and (and (and (and (and (= var9 (write var18 var10 (O_list (list var11 (|list::next| (getlist (read var18 var10))))))) (= var8 var16)) (= var7 var19)) (= var6 var15)) (= var5 var14)) (= var4 var13)) (= var3 var10)) (= var2 var11))) (and (and (and (and (and (and (and (= var49 (write var9 var3 (O_list (list (|list::key| (getlist (read var9 var3))) nullAddr)))) (= var46 var8)) (= var1 var7)) (= var43 var6)) (= var41 var5)) (= var39 var4)) (= var45 var3)) (= var0 var2)))))) (inv_main_7 var27 var26 var21 var24 var23 var22))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Int) (var7 Addr) (var8 Int) (var9 Heap) (var10 Addr) (var11 Int) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Int) (var16 Int) (var17 list) (var18 Heap) (var19 Addr) (var20 Int) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Int) (var25 Addr) (var26 Int) (var27 Heap) (var28 Int) (var29 Addr) (var30 Addr) (var31 Addr) (var32 Int) (var33 Addr) (var34 Int) (var35 Heap) (var36 Addr) (var37 Int) (var38 Addr) (var39 Addr) (var40 Addr) (var41 Addr) (var42 Addr) (var43 Int) (var44 Int) (var45 Addr) (var46 Int) (var47 Int) (var48 list) (var49 Heap) (var50 Heap) (var51 Addr) (var52 Addr) (var53 Addr) (var54 Int) (var55 Addr) (var56 Int) (var57 Heap)) (or (not (and (inv_main807_2 var57 var56 var55 var54 var53 var52) (and (and (and (and (= var51 nullAddr) (and (and (and (and (and (and (and (and (= var50 (newHeap (alloc var49 (O_list var48)))) (= var47 var46)) (= var51 var45)) (= var44 var43)) (= var42 var41)) (= var40 var39)) (= var38 var41)) (= var37 5)) (= var36 (newAddr (alloc var49 (O_list var48)))))) (and (and (and (and (and (and (and (= var35 (write var50 var36 (O_list (list var37 (|list::next| (getlist (read var50 var36))))))) (= var34 var47)) (= var33 var51)) (= var32 var44)) (= var31 var42)) (= var30 var40)) (= var29 var36)) (= var28 var37))) (and (and (and (and (and (and (and (= var27 (write var35 var29 (O_list (list (|list::key| (getlist (read var35 var29))) nullAddr)))) (= var26 var34)) (= var25 var33)) (= var24 var32)) (= var23 var31)) (= var22 var30)) (= var21 var29)) (= var20 var28))) (and (and (and (not (= var19 nullAddr)) (and (and (and (and (and (and (and (and (= var18 (newHeap (alloc var57 (O_list var17)))) (= var16 var56)) (= var19 var55)) (= var15 var54)) (= var14 var53)) (= var13 var52)) (= var12 var53)) (= var11 2)) (= var10 (newAddr (alloc var57 (O_list var17)))))) (and (and (and (and (and (and (and (= var9 (write var18 var10 (O_list (list var11 (|list::next| (getlist (read var18 var10))))))) (= var8 var16)) (= var7 var19)) (= var6 var15)) (= var5 var14)) (= var4 var13)) (= var3 var10)) (= var2 var11))) (and (and (and (and (and (and (and (= var49 (write var9 var3 (O_list (list (|list::key| (getlist (read var9 var3))) var7)))) (= var46 var8)) (= var1 var7)) (= var43 var6)) (= var41 var5)) (= var39 var4)) (= var45 var3)) (= var0 var2)))))) (inv_main_7 var27 var26 var21 var24 var23 var22))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Int) (var7 Addr) (var8 Int) (var9 Heap) (var10 Addr) (var11 Int) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Int) (var16 Int) (var17 list) (var18 Heap) (var19 Addr) (var20 Int) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Int) (var25 Addr) (var26 Int) (var27 Heap) (var28 Int) (var29 Addr) (var30 Addr) (var31 Addr) (var32 Int) (var33 Addr) (var34 Int) (var35 Heap) (var36 Addr) (var37 Int) (var38 Addr) (var39 Addr) (var40 Addr) (var41 Addr) (var42 Addr) (var43 Int) (var44 Int) (var45 Addr) (var46 Int) (var47 Int) (var48 list) (var49 Heap) (var50 Heap) (var51 Addr) (var52 Addr) (var53 Addr) (var54 Int) (var55 Addr) (var56 Int) (var57 Heap)) (or (not (and (inv_main807_2 var57 var56 var55 var54 var53 var52) (and (and (and (and (not (= var51 nullAddr)) (and (and (and (and (and (and (and (and (= var50 (newHeap (alloc var49 (O_list var48)))) (= var47 var46)) (= var51 var45)) (= var44 var43)) (= var42 var41)) (= var40 var39)) (= var38 var41)) (= var37 5)) (= var36 (newAddr (alloc var49 (O_list var48)))))) (and (and (and (and (and (and (and (= var35 (write var50 var36 (O_list (list var37 (|list::next| (getlist (read var50 var36))))))) (= var34 var47)) (= var33 var51)) (= var32 var44)) (= var31 var42)) (= var30 var40)) (= var29 var36)) (= var28 var37))) (and (and (and (and (and (and (and (= var27 (write var35 var29 (O_list (list (|list::key| (getlist (read var35 var29))) var33)))) (= var26 var34)) (= var25 var33)) (= var24 var32)) (= var23 var31)) (= var22 var30)) (= var21 var29)) (= var20 var28))) (and (and (and (not (= var19 nullAddr)) (and (and (and (and (and (and (and (and (= var18 (newHeap (alloc var57 (O_list var17)))) (= var16 var56)) (= var19 var55)) (= var15 var54)) (= var14 var53)) (= var13 var52)) (= var12 var53)) (= var11 2)) (= var10 (newAddr (alloc var57 (O_list var17)))))) (and (and (and (and (and (and (and (= var9 (write var18 var10 (O_list (list var11 (|list::next| (getlist (read var18 var10))))))) (= var8 var16)) (= var7 var19)) (= var6 var15)) (= var5 var14)) (= var4 var13)) (= var3 var10)) (= var2 var11))) (and (and (and (and (and (and (and (= var49 (write var9 var3 (O_list (list (|list::key| (getlist (read var9 var3))) var7)))) (= var46 var8)) (= var1 var7)) (= var43 var6)) (= var41 var5)) (= var39 var4)) (= var45 var3)) (= var0 var2)))))) (inv_main_7 var27 var26 var21 var24 var23 var22))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Int) (var6 Addr) (var7 Int) (var8 Heap) (var9 Int) (var10 Addr) (var11 Int) (var12 Int) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Int) (var20 Int) (var21 Addr) (var22 Addr) (var23 Int) (var24 Int) (var25 Heap) (var26 Heap) (var27 Int) (var28 Addr) (var29 Addr) (var30 Addr) (var31 Int) (var32 Addr) (var33 Int) (var34 Heap)) (or (not (and (inv_main_47 var34 var33 var32 var31 var30 var29 var28 var27) (and (and (and (and (and (and (and (and (and (= var26 var25) (= var24 var23)) (= var22 var21)) (= var20 var19)) (= var18 var17)) (= var16 var15)) (= var14 var13)) (= var12 var11)) (= var10 (|list::next| (getlist (read var25 var13))))) (and (and (not (= var9 0)) (and (not (= var28 nullAddr)) (and (and (and (and (and (and (and (and (= var8 var34) (= var7 var33)) (= var6 var32)) (= var5 var31)) (= var4 var30)) (= var3 var29)) (= var2 var28)) (= var1 var27)) (= var0 (|list::key| (getlist (read var34 var28))))))) (and (and (and (and (and (and (and (and (= var25 var8) (= var23 var7)) (= var21 var6)) (= var19 var5)) (= var17 var4)) (= var15 var3)) (= var13 var2)) (= var11 var1)) (or (and (not (= var0 var1)) (= var9 1)) (and (= var0 var1) (= var9 0)))))))) (inv_main_47 var26 var24 var22 var20 var18 var16 var10 var12))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Addr) (var5 Int) (var6 Heap)) (or (not (and (inv_main_43 var6 var5 var4 var3 var2 var1) (and (= var2 nullAddr) (= var0 2)))) (inv_main_47 var6 var5 var4 var3 var2 var1 var4 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Int) (var7 Addr) (var8 Int) (var9 Heap) (var10 Addr) (var11 Int) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Int) (var16 Int) (var17 list) (var18 Heap) (var19 Addr) (var20 Int) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Int) (var25 Addr) (var26 Int) (var27 Heap) (var28 Int) (var29 Addr) (var30 Addr) (var31 Addr) (var32 Int) (var33 Addr) (var34 Int) (var35 Heap) (var36 Addr) (var37 Int) (var38 Addr) (var39 Addr) (var40 Addr) (var41 Addr) (var42 Addr) (var43 Int) (var44 Int) (var45 Addr) (var46 Int) (var47 Int) (var48 list) (var49 Heap) (var50 Heap) (var51 Addr) (var52 Addr) (var53 Addr) (var54 Int) (var55 Addr) (var56 Int) (var57 Heap)) (or (not (and (inv_main_7 var57 var56 var55 var54 var53 var52) (and (and (and (and (= var51 nullAddr) (and (and (and (and (and (and (and (and (= var50 (newHeap (alloc var49 (O_list var48)))) (= var47 var46)) (= var51 var45)) (= var44 var43)) (= var42 var41)) (= var40 var39)) (= var38 var41)) (= var37 3)) (= var36 (newAddr (alloc var49 (O_list var48)))))) (and (and (and (and (and (and (and (= var35 (write var50 var36 (O_list (list var37 (|list::next| (getlist (read var50 var36))))))) (= var34 var47)) (= var33 var51)) (= var32 var44)) (= var31 var42)) (= var30 var40)) (= var29 var36)) (= var28 var37))) (and (and (and (and (and (and (and (= var27 (write var35 var29 (O_list (list (|list::key| (getlist (read var35 var29))) nullAddr)))) (= var26 var34)) (= var25 var33)) (= var24 var32)) (= var23 var31)) (= var22 var30)) (= var21 var29)) (= var20 var28))) (and (and (and (= var19 nullAddr) (and (and (and (and (and (and (and (and (= var18 (newHeap (alloc var57 (O_list var17)))) (= var16 var56)) (= var19 var55)) (= var15 var54)) (= var14 var53)) (= var13 var52)) (= var12 var53)) (= var11 1)) (= var10 (newAddr (alloc var57 (O_list var17)))))) (and (and (and (and (and (and (and (= var9 (write var18 var10 (O_list (list var11 (|list::next| (getlist (read var18 var10))))))) (= var8 var16)) (= var7 var19)) (= var6 var15)) (= var5 var14)) (= var4 var13)) (= var3 var10)) (= var2 var11))) (and (and (and (and (and (and (and (= var49 (write var9 var3 (O_list (list (|list::key| (getlist (read var9 var3))) nullAddr)))) (= var46 var8)) (= var1 var7)) (= var43 var6)) (= var41 var5)) (= var39 var4)) (= var45 var3)) (= var0 var2)))))) (inv_main_43 var27 var26 var21 var24 var21 var22))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Int) (var7 Addr) (var8 Int) (var9 Heap) (var10 Addr) (var11 Int) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Int) (var16 Int) (var17 list) (var18 Heap) (var19 Addr) (var20 Int) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Int) (var25 Addr) (var26 Int) (var27 Heap) (var28 Int) (var29 Addr) (var30 Addr) (var31 Addr) (var32 Int) (var33 Addr) (var34 Int) (var35 Heap) (var36 Addr) (var37 Int) (var38 Addr) (var39 Addr) (var40 Addr) (var41 Addr) (var42 Addr) (var43 Int) (var44 Int) (var45 Addr) (var46 Int) (var47 Int) (var48 list) (var49 Heap) (var50 Heap) (var51 Addr) (var52 Addr) (var53 Addr) (var54 Int) (var55 Addr) (var56 Int) (var57 Heap)) (or (not (and (inv_main_7 var57 var56 var55 var54 var53 var52) (and (and (and (and (not (= var51 nullAddr)) (and (and (and (and (and (and (and (and (= var50 (newHeap (alloc var49 (O_list var48)))) (= var47 var46)) (= var51 var45)) (= var44 var43)) (= var42 var41)) (= var40 var39)) (= var38 var41)) (= var37 3)) (= var36 (newAddr (alloc var49 (O_list var48)))))) (and (and (and (and (and (and (and (= var35 (write var50 var36 (O_list (list var37 (|list::next| (getlist (read var50 var36))))))) (= var34 var47)) (= var33 var51)) (= var32 var44)) (= var31 var42)) (= var30 var40)) (= var29 var36)) (= var28 var37))) (and (and (and (and (and (and (and (= var27 (write var35 var29 (O_list (list (|list::key| (getlist (read var35 var29))) var33)))) (= var26 var34)) (= var25 var33)) (= var24 var32)) (= var23 var31)) (= var22 var30)) (= var21 var29)) (= var20 var28))) (and (and (and (= var19 nullAddr) (and (and (and (and (and (and (and (and (= var18 (newHeap (alloc var57 (O_list var17)))) (= var16 var56)) (= var19 var55)) (= var15 var54)) (= var14 var53)) (= var13 var52)) (= var12 var53)) (= var11 1)) (= var10 (newAddr (alloc var57 (O_list var17)))))) (and (and (and (and (and (and (and (= var9 (write var18 var10 (O_list (list var11 (|list::next| (getlist (read var18 var10))))))) (= var8 var16)) (= var7 var19)) (= var6 var15)) (= var5 var14)) (= var4 var13)) (= var3 var10)) (= var2 var11))) (and (and (and (and (and (and (and (= var49 (write var9 var3 (O_list (list (|list::key| (getlist (read var9 var3))) nullAddr)))) (= var46 var8)) (= var1 var7)) (= var43 var6)) (= var41 var5)) (= var39 var4)) (= var45 var3)) (= var0 var2)))))) (inv_main_43 var27 var26 var21 var24 var21 var22))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Int) (var7 Addr) (var8 Int) (var9 Heap) (var10 Addr) (var11 Int) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Int) (var16 Int) (var17 list) (var18 Heap) (var19 Addr) (var20 Int) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Int) (var25 Addr) (var26 Int) (var27 Heap) (var28 Int) (var29 Addr) (var30 Addr) (var31 Addr) (var32 Int) (var33 Addr) (var34 Int) (var35 Heap) (var36 Addr) (var37 Int) (var38 Addr) (var39 Addr) (var40 Addr) (var41 Addr) (var42 Addr) (var43 Int) (var44 Int) (var45 Addr) (var46 Int) (var47 Int) (var48 list) (var49 Heap) (var50 Heap) (var51 Addr) (var52 Addr) (var53 Addr) (var54 Int) (var55 Addr) (var56 Int) (var57 Heap)) (or (not (and (inv_main_7 var57 var56 var55 var54 var53 var52) (and (and (and (and (= var51 nullAddr) (and (and (and (and (and (and (and (and (= var50 (newHeap (alloc var49 (O_list var48)))) (= var47 var46)) (= var51 var45)) (= var44 var43)) (= var42 var41)) (= var40 var39)) (= var38 var41)) (= var37 3)) (= var36 (newAddr (alloc var49 (O_list var48)))))) (and (and (and (and (and (and (and (= var35 (write var50 var36 (O_list (list var37 (|list::next| (getlist (read var50 var36))))))) (= var34 var47)) (= var33 var51)) (= var32 var44)) (= var31 var42)) (= var30 var40)) (= var29 var36)) (= var28 var37))) (and (and (and (and (and (and (and (= var27 (write var35 var29 (O_list (list (|list::key| (getlist (read var35 var29))) nullAddr)))) (= var26 var34)) (= var25 var33)) (= var24 var32)) (= var23 var31)) (= var22 var30)) (= var21 var29)) (= var20 var28))) (and (and (and (not (= var19 nullAddr)) (and (and (and (and (and (and (and (and (= var18 (newHeap (alloc var57 (O_list var17)))) (= var16 var56)) (= var19 var55)) (= var15 var54)) (= var14 var53)) (= var13 var52)) (= var12 var53)) (= var11 1)) (= var10 (newAddr (alloc var57 (O_list var17)))))) (and (and (and (and (and (and (and (= var9 (write var18 var10 (O_list (list var11 (|list::next| (getlist (read var18 var10))))))) (= var8 var16)) (= var7 var19)) (= var6 var15)) (= var5 var14)) (= var4 var13)) (= var3 var10)) (= var2 var11))) (and (and (and (and (and (and (and (= var49 (write var9 var3 (O_list (list (|list::key| (getlist (read var9 var3))) var7)))) (= var46 var8)) (= var1 var7)) (= var43 var6)) (= var41 var5)) (= var39 var4)) (= var45 var3)) (= var0 var2)))))) (inv_main_43 var27 var26 var21 var24 var21 var22))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Int) (var7 Addr) (var8 Int) (var9 Heap) (var10 Addr) (var11 Int) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Int) (var16 Int) (var17 list) (var18 Heap) (var19 Addr) (var20 Int) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Int) (var25 Addr) (var26 Int) (var27 Heap) (var28 Int) (var29 Addr) (var30 Addr) (var31 Addr) (var32 Int) (var33 Addr) (var34 Int) (var35 Heap) (var36 Addr) (var37 Int) (var38 Addr) (var39 Addr) (var40 Addr) (var41 Addr) (var42 Addr) (var43 Int) (var44 Int) (var45 Addr) (var46 Int) (var47 Int) (var48 list) (var49 Heap) (var50 Heap) (var51 Addr) (var52 Addr) (var53 Addr) (var54 Int) (var55 Addr) (var56 Int) (var57 Heap)) (or (not (and (inv_main_7 var57 var56 var55 var54 var53 var52) (and (and (and (and (not (= var51 nullAddr)) (and (and (and (and (and (and (and (and (= var50 (newHeap (alloc var49 (O_list var48)))) (= var47 var46)) (= var51 var45)) (= var44 var43)) (= var42 var41)) (= var40 var39)) (= var38 var41)) (= var37 3)) (= var36 (newAddr (alloc var49 (O_list var48)))))) (and (and (and (and (and (and (and (= var35 (write var50 var36 (O_list (list var37 (|list::next| (getlist (read var50 var36))))))) (= var34 var47)) (= var33 var51)) (= var32 var44)) (= var31 var42)) (= var30 var40)) (= var29 var36)) (= var28 var37))) (and (and (and (and (and (and (and (= var27 (write var35 var29 (O_list (list (|list::key| (getlist (read var35 var29))) var33)))) (= var26 var34)) (= var25 var33)) (= var24 var32)) (= var23 var31)) (= var22 var30)) (= var21 var29)) (= var20 var28))) (and (and (and (not (= var19 nullAddr)) (and (and (and (and (and (and (and (and (= var18 (newHeap (alloc var57 (O_list var17)))) (= var16 var56)) (= var19 var55)) (= var15 var54)) (= var14 var53)) (= var13 var52)) (= var12 var53)) (= var11 1)) (= var10 (newAddr (alloc var57 (O_list var17)))))) (and (and (and (and (and (and (and (= var9 (write var18 var10 (O_list (list var11 (|list::next| (getlist (read var18 var10))))))) (= var8 var16)) (= var7 var19)) (= var6 var15)) (= var5 var14)) (= var4 var13)) (= var3 var10)) (= var2 var11))) (and (and (and (and (and (and (and (= var49 (write var9 var3 (O_list (list (|list::key| (getlist (read var9 var3))) var7)))) (= var46 var8)) (= var1 var7)) (= var43 var6)) (= var41 var5)) (= var39 var4)) (= var45 var3)) (= var0 var2)))))) (inv_main_43 var27 var26 var21 var24 var21 var22))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Addr) (var5 Int) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Int) (var10 Addr) (var11 Int) (var12 Heap)) (or (not (and (inv_main_43 var12 var11 var10 var9 var8 var7) (and (and (and (and (and (and (and (= var6 var12) (= var5 var11)) (= var4 var10)) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var0 (|list::next| (getlist (read var12 var8))))) (not (= var8 nullAddr))))) (inv_main_43 var6 var5 var4 var3 var0 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Int) (var5 Heap) (var6 Int) (var7 Addr) (var8 Addr) (var9 Int) (var10 Addr) (var11 Int) (var12 Heap) (var13 Int) (var14 Int) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Int) (var19 Addr) (var20 Int) (var21 Heap)) (or (not (and (inv_main_47 var21 var20 var19 var18 var17 var16 var15 var14) (and (and (and (= var13 0) (and (and (and (and (and (and (= var12 var21) (= var11 var20)) (= var10 var19)) (= var9 var18)) (= var8 var17)) (= var7 var15)) (= var6 (|list::key| (getlist (read var21 var15)))))) (and (and (and (and (and (and (= var5 var12) (= var4 var11)) (= var3 var10)) (= var2 var9)) (= var1 var8)) (= var0 var7)) (or (and (= var6 2) (= var13 1)) (and (not (= var6 2)) (= var13 0))))) (= var15 nullAddr)))) (inv_main14_7 var5 var4 var3 var2 var1 var0 var13))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Int) (var8 Addr) (var9 Int) (var10 Heap) (var11 Int) (var12 Addr) (var13 Addr) (var14 Int) (var15 Addr) (var16 Int) (var17 Heap) (var18 Int) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Int) (var24 Int) (var25 Addr) (var26 Addr) (var27 Int) (var28 Int) (var29 Heap) (var30 Heap) (var31 Int) (var32 Int) (var33 Addr) (var34 Addr) (var35 Addr) (var36 Int) (var37 Addr) (var38 Int) (var39 Heap)) (or (not (and (inv_main_47 var39 var38 var37 var36 var35 var34 var33 var32) (and (and (and (= var31 0) (and (and (and (and (and (and (= var30 var29) (= var28 var27)) (= var26 var25)) (= var24 var23)) (= var22 var21)) (= var20 var19)) (= var18 (|list::key| (getlist (read var29 var19)))))) (and (and (and (and (and (and (= var17 var30) (= var16 var28)) (= var15 var26)) (= var14 var24)) (= var13 var22)) (= var12 var20)) (or (and (= var18 2) (= var31 1)) (and (not (= var18 2)) (= var31 0))))) (and (and (= var11 0) (and (not (= var33 nullAddr)) (and (and (and (and (and (and (and (and (= var10 var39) (= var9 var38)) (= var8 var37)) (= var7 var36)) (= var6 var35)) (= var5 var34)) (= var4 var33)) (= var3 var32)) (= var2 (|list::key| (getlist (read var39 var33))))))) (and (and (and (and (and (and (and (and (= var29 var10) (= var27 var9)) (= var25 var8)) (= var23 var7)) (= var21 var6)) (= var1 var5)) (= var19 var4)) (= var0 var3)) (or (and (not (= var2 var3)) (= var11 1)) (and (= var2 var3) (= var11 0)))))))) (inv_main14_7 var17 var16 var15 var14 var13 var12 var31))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Int) (var11 Int) (var12 Addr) (var13 Addr) (var14 Int) (var15 Int) (var16 Heap) (var17 Heap) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Int) (var23 Addr) (var24 Int) (var25 Heap)) (or (not (and (inv_main780_17 var25 var24 var23 var22 var21 var20 var19 var18) (and (and (and (and (and (and (and (and (and (= var17 var16) (= var15 var14)) (= var13 var12)) (= var11 var10)) (= var9 var8)) (= var7 var6)) (= var5 var4)) (= var3 var2)) (= var1 (|list::next| (getlist (read var16 var2))))) (and (not (= var0 var4)) (and (and (and (and (and (and (and (and (= var16 var25) (= var14 var24)) (= var12 var23)) (= var10 var22)) (= var8 var21)) (= var6 var20)) (= var4 var19)) (= var2 var18)) (= var0 (|list::next| (getlist (read var25 var18))))))))) (inv_main780_17 var17 var15 var13 var11 var9 var7 var5 var1))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr) (var7 Int) (var8 Addr) (var9 Int) (var10 Heap) (var11 Int) (var12 Addr) (var13 Addr) (var14 Int) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Int) (var19 Addr) (var20 Int) (var21 Heap)) (or (not (and (inv_main_47 var21 var20 var19 var18 var17 var16 var15 var14) (and (not (= var13 var12)) (and (and (and (not (= var11 0)) (and (and (and (and (and (and (= var10 var21) (= var9 var20)) (= var8 var19)) (= var7 var18)) (= var6 var17)) (= var5 var15)) (= var4 (|list::key| (getlist (read var21 var15)))))) (and (and (and (and (and (and (= var3 var10) (= var2 var9)) (= var13 var8)) (= var1 var7)) (= var0 var6)) (= var12 var5)) (or (and (= var4 2) (= var11 1)) (and (not (= var4 2)) (= var11 0))))) (= var15 nullAddr))))) (inv_main780_17 var3 var2 var13 var1 var0 var12 var12 var13))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Int) (var8 Addr) (var9 Int) (var10 Heap) (var11 Int) (var12 Addr) (var13 Int) (var14 Int) (var15 Heap) (var16 Int) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Int) (var22 Int) (var23 Addr) (var24 Addr) (var25 Int) (var26 Int) (var27 Heap) (var28 Heap) (var29 Int) (var30 Addr) (var31 Addr) (var32 Int) (var33 Addr) (var34 Addr) (var35 Addr) (var36 Int) (var37 Addr) (var38 Int) (var39 Heap)) (or (not (and (inv_main_47 var39 var38 var37 var36 var35 var34 var33 var32) (and (not (= var31 var30)) (and (and (and (not (= var29 0)) (and (and (and (and (and (and (= var28 var27) (= var26 var25)) (= var24 var23)) (= var22 var21)) (= var20 var19)) (= var18 var17)) (= var16 (|list::key| (getlist (read var27 var17)))))) (and (and (and (and (and (and (= var15 var28) (= var14 var26)) (= var31 var24)) (= var13 var22)) (= var12 var20)) (= var30 var18)) (or (and (= var16 2) (= var29 1)) (and (not (= var16 2)) (= var29 0))))) (and (and (= var11 0) (and (not (= var33 nullAddr)) (and (and (and (and (and (and (and (and (= var10 var39) (= var9 var38)) (= var8 var37)) (= var7 var36)) (= var6 var35)) (= var5 var34)) (= var4 var33)) (= var3 var32)) (= var2 (|list::key| (getlist (read var39 var33))))))) (and (and (and (and (and (and (and (and (= var27 var10) (= var25 var9)) (= var23 var8)) (= var21 var7)) (= var19 var6)) (= var1 var5)) (= var17 var4)) (= var0 var3)) (or (and (not (= var2 var3)) (= var11 1)) (and (= var2 var3) (= var11 0))))))))) (inv_main780_17 var15 var14 var31 var13 var12 var30 var30 var31))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Int) (var6 Addr) (var7 Int) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Int) (var14 Addr) (var15 Int) (var16 Heap) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Addr) (var25 Addr) (var26 Int) (var27 Int) (var28 Addr) (var29 Addr) (var30 Int) (var31 Int) (var32 Heap) (var33 Heap) (var34 Addr) (var35 Addr) (var36 Addr) (var37 Addr) (var38 Int) (var39 Addr) (var40 Int) (var41 Heap)) (or (not (and (inv_main780_17 var41 var40 var39 var38 var37 var36 var35 var34) (and (and (and (and (and (and (and (and (and (and (and (= var33 var32) (= var31 var30)) (= var29 var28)) (= var27 var26)) (= var25 var24)) (= var23 var22)) (= var21 var20)) (= var19 var18)) (= var17 (|list::next| (getlist (read var32 var20))))) (and (and (and (and (and (and (and (= var16 (write var33 var19 (O_list (list (|list::key| (getlist (read var33 var19))) var17)))) (= var15 var31)) (= var14 var29)) (= var13 var27)) (= var12 var25)) (= var11 var23)) (= var10 var21)) (= var9 var19))) (and (and (and (and (and (and (and (= var8 (write var16 var10 defObj)) (= var7 var15)) (= var6 var14)) (= var5 var13)) (= var4 var12)) (= var3 var11)) (= var2 var10)) (= var1 var9))) (and (= var0 var20) (and (and (and (and (and (and (and (and (= var32 var41) (= var30 var40)) (= var28 var39)) (= var26 var38)) (= var24 var37)) (= var22 var36)) (= var20 var35)) (= var18 var34)) (= var0 (|list::next| (getlist (read var41 var34))))))))) (inv_main_60 var8 var7 var6 var5 var6 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Addr) (var5 Int) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Int) (var10 Addr) (var11 Int) (var12 Heap)) (or (not (and (inv_main_60 var12 var11 var10 var9 var8 var7) (and (and (and (and (and (and (and (= var6 var12) (= var5 var11)) (= var4 var10)) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var0 (|list::next| (getlist (read var12 var8))))) (not (= var8 nullAddr))))) (inv_main_60 var6 var5 var4 var3 var0 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Addr) (var5 Int) (var6 Heap) (var7 Int) (var8 Addr) (var9 Addr) (var10 Int) (var11 Addr) (var12 Addr) (var13 Int) (var14 Heap) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Int) (var20 Addr) (var21 Int) (var22 Heap) (var23 Addr) (var24 Addr) (var25 Addr) (var26 Addr) (var27 Int) (var28 Addr) (var29 Int) (var30 Heap) (var31 Addr) (var32 Addr) (var33 Addr) (var34 Addr) (var35 Addr) (var36 Addr) (var37 Addr) (var38 Addr) (var39 Addr) (var40 Int) (var41 Int) (var42 Addr) (var43 Addr) (var44 Int) (var45 Int) (var46 Heap) (var47 Heap) (var48 Int) (var49 Addr) (var50 Addr) (var51 Addr) (var52 Int) (var53 Addr) (var54 Int) (var55 Heap)) (or (not (and (inv_main_47 var55 var54 var53 var52 var51 var50 var49 var48) (and (and (and (and (and (and (and (and (and (and (and (and (= var47 var46) (= var45 var44)) (= var43 var42)) (= var41 var40)) (= var39 var38)) (= var37 var36)) (= var35 var34)) (= var33 var32)) (= var31 (|list::next| (getlist (read var46 var34))))) (and (and (and (and (and (and (and (= var30 (write var47 var33 (O_list (list (|list::key| (getlist (read var47 var33))) var31)))) (= var29 var45)) (= var28 var43)) (= var27 var41)) (= var26 var39)) (= var25 var37)) (= var24 var35)) (= var23 var33))) (and (and (and (and (and (and (and (= var22 (write var30 var24 defObj)) (= var21 var29)) (= var20 var28)) (= var19 var27)) (= var18 var26)) (= var17 var25)) (= var16 var24)) (= var15 var23))) (and (and (and (and (and (and (and (and (and (= var46 var14) (= var44 var13)) (= var12 var11)) (= var40 var10)) (= var38 var9)) (= var36 var8)) (= var34 var8)) (= var32 var11)) (= var42 (|list::next| (getlist (read var14 var8))))) (= var11 var8))) (and (and (and (not (= var7 0)) (and (and (and (and (and (and (= var6 var55) (= var5 var54)) (= var4 var53)) (= var3 var52)) (= var2 var51)) (= var1 var49)) (= var0 (|list::key| (getlist (read var55 var49)))))) (and (and (and (and (and (and (= var14 var6) (= var13 var5)) (= var11 var4)) (= var10 var3)) (= var9 var2)) (= var8 var1)) (or (and (= var0 2) (= var7 1)) (and (not (= var0 2)) (= var7 0))))) (= var49 nullAddr))))) (inv_main_60 var22 var21 var20 var19 var20 var17))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Int) (var8 Addr) (var9 Int) (var10 Heap) (var11 Int) (var12 Int) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Int) (var18 Int) (var19 Addr) (var20 Addr) (var21 Int) (var22 Int) (var23 Heap) (var24 Heap) (var25 Int) (var26 Addr) (var27 Addr) (var28 Int) (var29 Addr) (var30 Addr) (var31 Int) (var32 Heap) (var33 Addr) (var34 Addr) (var35 Addr) (var36 Addr) (var37 Int) (var38 Addr) (var39 Int) (var40 Heap) (var41 Addr) (var42 Addr) (var43 Addr) (var44 Addr) (var45 Int) (var46 Addr) (var47 Int) (var48 Heap) (var49 Addr) (var50 Addr) (var51 Addr) (var52 Addr) (var53 Addr) (var54 Addr) (var55 Addr) (var56 Addr) (var57 Addr) (var58 Int) (var59 Int) (var60 Addr) (var61 Addr) (var62 Int) (var63 Int) (var64 Heap) (var65 Heap) (var66 Int) (var67 Addr) (var68 Addr) (var69 Addr) (var70 Int) (var71 Addr) (var72 Int) (var73 Heap)) (or (not (and (inv_main_47 var73 var72 var71 var70 var69 var68 var67 var66) (and (and (and (and (and (and (and (and (and (and (and (and (= var65 var64) (= var63 var62)) (= var61 var60)) (= var59 var58)) (= var57 var56)) (= var55 var54)) (= var53 var52)) (= var51 var50)) (= var49 (|list::next| (getlist (read var64 var52))))) (and (and (and (and (and (and (and (= var48 (write var65 var51 (O_list (list (|list::key| (getlist (read var65 var51))) var49)))) (= var47 var63)) (= var46 var61)) (= var45 var59)) (= var44 var57)) (= var43 var55)) (= var42 var53)) (= var41 var51))) (and (and (and (and (and (and (and (= var40 (write var48 var42 defObj)) (= var39 var47)) (= var38 var46)) (= var37 var45)) (= var36 var44)) (= var35 var43)) (= var34 var42)) (= var33 var41))) (and (and (and (and (and (and (and (and (and (= var64 var32) (= var62 var31)) (= var30 var29)) (= var58 var28)) (= var56 var27)) (= var54 var26)) (= var52 var26)) (= var50 var29)) (= var60 (|list::next| (getlist (read var32 var26))))) (= var29 var26))) (and (and (and (not (= var25 0)) (and (and (and (and (and (and (= var24 var23) (= var22 var21)) (= var20 var19)) (= var18 var17)) (= var16 var15)) (= var14 var13)) (= var12 (|list::key| (getlist (read var23 var13)))))) (and (and (and (and (and (and (= var32 var24) (= var31 var22)) (= var29 var20)) (= var28 var18)) (= var27 var16)) (= var26 var14)) (or (and (= var12 2) (= var25 1)) (and (not (= var12 2)) (= var25 0))))) (and (and (= var11 0) (and (not (= var67 nullAddr)) (and (and (and (and (and (and (and (and (= var10 var73) (= var9 var72)) (= var8 var71)) (= var7 var70)) (= var6 var69)) (= var5 var68)) (= var4 var67)) (= var3 var66)) (= var2 (|list::key| (getlist (read var73 var67))))))) (and (and (and (and (and (and (and (and (= var23 var10) (= var21 var9)) (= var19 var8)) (= var17 var7)) (= var15 var6)) (= var1 var5)) (= var13 var4)) (= var0 var3)) (or (and (not (= var2 var3)) (= var11 1)) (and (= var2 var3) (= var11 0))))))))) (inv_main_60 var40 var39 var38 var37 var38 var35))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Addr) (var5 Int) (var6 Heap)) (not (inv_main14_7 var6 var5 var4 var3 var2 var1 var0))))
(check-sat)
