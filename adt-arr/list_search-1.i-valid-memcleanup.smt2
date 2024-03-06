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
(declare-fun inv_exit (Heap Addr) Bool)
(declare-fun inv_main556_3 (Heap Addr Addr Int Addr Addr) Bool)
(declare-fun inv_main565_12_0 (Heap Addr Addr) Bool)
(declare-fun inv_main_44 (Heap Addr Addr Int Addr Addr Addr Int) Bool)
(declare-fun inv_main_47 (Heap Addr Addr Int Addr Addr) Bool)
(declare-fun inv_main_7 (Heap Addr Addr Int Addr Addr) Bool)
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (and (= var5 emptyHeap) (= var4 nullAddr)) (= var3 nullAddr))) (inv_main556_3 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main_47 var5 var4 var3 var2 var1 var0) (= var3 nullAddr))) (inv_main565_12_0 var5 var4 var3))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Int) (var7 Addr) (var8 Heap) (var9 Addr) (var10 Int) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Int) (var15 Addr) (var16 Bool) (var17 Addr) (var18 list) (var19 Heap) (var20 Addr) (var21 Int) (var22 Addr) (var23 Addr) (var24 Addr) (var25 Int) (var26 Addr) (var27 Addr) (var28 Heap) (var29 Int) (var30 Addr) (var31 Addr) (var32 Addr) (var33 Int) (var34 Addr) (var35 Heap) (var36 Addr) (var37 Int) (var38 Addr) (var39 Addr) (var40 Addr) (var41 Addr) (var42 Addr) (var43 Int) (var44 Int) (var45 Addr) (var46 Addr) (var47 Addr) (var48 Bool) (var49 Addr) (var50 list) (var51 Heap) (var52 Heap) (var53 Addr) (var54 Addr) (var55 Addr) (var56 Int) (var57 Addr) (var58 Addr) (var59 Heap)) (or (not (and (inv_main556_3 var59 var58 var57 var56 var55 var54) (and (and (and (and (= var53 nullAddr) (and (and (and (and (and (and (and (and (= var52 (newHeap (alloc var51 (O_list var50)))) (or (and var48 (= var49 (newAddr (alloc var51 (O_list var50))))) (and (not var48) (= var49 var47)))) (= var46 var45)) (= var44 var43)) (= var42 var41)) (= var40 var39)) (= var38 var41)) (= var37 5)) (= var36 (newAddr (alloc var51 (O_list var50)))))) (and (and (and (and (and (and (and (= var35 (write var52 var36 (O_list (list var37 (|list::next| (getlist (read var52 var36))))))) (= var34 var49)) (= var53 var46)) (= var33 var44)) (= var32 var42)) (= var31 var40)) (= var30 var36)) (= var29 var37))) (and (and (and (and (and (and (and (= var28 (write var35 var30 (O_list (list (|list::key| (getlist (read var35 var30))) nullAddr)))) (= var27 var34)) (= var26 var53)) (= var25 var33)) (= var24 var32)) (= var23 var31)) (= var22 var30)) (= var21 var29))) (and (and (and (= var20 nullAddr) (and (and (and (and (and (and (and (and (= var19 (newHeap (alloc var59 (O_list var18)))) (or (and var16 (= var17 (newAddr (alloc var59 (O_list var18))))) (and (not var16) (= var17 var58)))) (= var15 var57)) (= var14 var56)) (= var13 var55)) (= var12 var54)) (= var11 var55)) (= var10 2)) (= var9 (newAddr (alloc var59 (O_list var18)))))) (and (and (and (and (and (and (and (= var8 (write var19 var9 (O_list (list var10 (|list::next| (getlist (read var19 var9))))))) (= var7 var17)) (= var20 var15)) (= var6 var14)) (= var5 var13)) (= var4 var12)) (= var3 var9)) (= var2 var10))) (and (and (and (and (and (and (and (= var51 (write var8 var3 (O_list (list (|list::key| (getlist (read var8 var3))) nullAddr)))) (= var47 var7)) (= var1 var20)) (= var43 var6)) (= var41 var5)) (= var39 var4)) (= var45 var3)) (= var0 var2)))))) (inv_main_7 var28 var27 var22 var25 var24 var23))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Int) (var7 Addr) (var8 Heap) (var9 Addr) (var10 Int) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Int) (var15 Addr) (var16 Bool) (var17 Addr) (var18 list) (var19 Heap) (var20 Addr) (var21 Int) (var22 Addr) (var23 Addr) (var24 Addr) (var25 Int) (var26 Addr) (var27 Addr) (var28 Heap) (var29 Int) (var30 Addr) (var31 Addr) (var32 Addr) (var33 Int) (var34 Addr) (var35 Addr) (var36 Heap) (var37 Int) (var38 Addr) (var39 Addr) (var40 Addr) (var41 Int) (var42 Addr) (var43 Heap) (var44 Addr) (var45 Int) (var46 Addr) (var47 Addr) (var48 Addr) (var49 Addr) (var50 Addr) (var51 Int) (var52 Int) (var53 Addr) (var54 Addr) (var55 Addr) (var56 Bool) (var57 Addr) (var58 list) (var59 Heap) (var60 Heap) (var61 Addr) (var62 Addr) (var63 Addr) (var64 Int) (var65 Addr) (var66 Addr) (var67 Heap)) (or (not (and (inv_main556_3 var67 var66 var65 var64 var63 var62) (and (and (and (and (and (not (= var61 nullAddr)) (and (and (and (and (and (and (and (and (= var60 (newHeap (alloc var59 (O_list var58)))) (or (and var56 (= var57 (newAddr (alloc var59 (O_list var58))))) (and (not var56) (= var57 var55)))) (= var54 var53)) (= var52 var51)) (= var50 var49)) (= var48 var47)) (= var46 var49)) (= var45 5)) (= var44 (newAddr (alloc var59 (O_list var58)))))) (and (and (and (and (and (and (and (= var43 (write var60 var44 (O_list (list var45 (|list::next| (getlist (read var60 var44))))))) (= var42 var57)) (= var61 var54)) (= var41 var52)) (= var40 var50)) (= var39 var48)) (= var38 var44)) (= var37 var45))) (and (and (and (and (and (and (and (= var36 (write var43 var38 (O_list (list var37 (|list::next| (getlist (read var43 var38))))))) (= var35 var42)) (= var34 var61)) (= var33 var41)) (= var32 var40)) (= var31 var39)) (= var30 var38)) (= var29 var37))) (and (and (and (and (and (and (and (= var28 (write var36 var30 (O_list (list (|list::key| (getlist (read var36 var30))) var34)))) (= var27 var35)) (= var26 var34)) (= var25 var33)) (= var24 var32)) (= var23 var31)) (= var22 var30)) (= var21 var29))) (and (and (and (= var20 nullAddr) (and (and (and (and (and (and (and (and (= var19 (newHeap (alloc var67 (O_list var18)))) (or (and var16 (= var17 (newAddr (alloc var67 (O_list var18))))) (and (not var16) (= var17 var66)))) (= var15 var65)) (= var14 var64)) (= var13 var63)) (= var12 var62)) (= var11 var63)) (= var10 2)) (= var9 (newAddr (alloc var67 (O_list var18)))))) (and (and (and (and (and (and (and (= var8 (write var19 var9 (O_list (list var10 (|list::next| (getlist (read var19 var9))))))) (= var7 var17)) (= var20 var15)) (= var6 var14)) (= var5 var13)) (= var4 var12)) (= var3 var9)) (= var2 var10))) (and (and (and (and (and (and (and (= var59 (write var8 var3 (O_list (list (|list::key| (getlist (read var8 var3))) nullAddr)))) (= var55 var7)) (= var1 var20)) (= var51 var6)) (= var49 var5)) (= var47 var4)) (= var53 var3)) (= var0 var2)))))) (inv_main_7 var28 var27 var22 var25 var24 var23))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Int) (var7 Addr) (var8 Addr) (var9 Heap) (var10 Int) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Int) (var15 Addr) (var16 Heap) (var17 Addr) (var18 Int) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Int) (var23 Addr) (var24 Bool) (var25 Addr) (var26 list) (var27 Heap) (var28 Addr) (var29 Int) (var30 Addr) (var31 Addr) (var32 Addr) (var33 Int) (var34 Addr) (var35 Addr) (var36 Heap) (var37 Int) (var38 Addr) (var39 Addr) (var40 Addr) (var41 Int) (var42 Addr) (var43 Heap) (var44 Addr) (var45 Int) (var46 Addr) (var47 Addr) (var48 Addr) (var49 Addr) (var50 Addr) (var51 Int) (var52 Int) (var53 Addr) (var54 Addr) (var55 Addr) (var56 Bool) (var57 Addr) (var58 list) (var59 Heap) (var60 Heap) (var61 Addr) (var62 Addr) (var63 Addr) (var64 Int) (var65 Addr) (var66 Addr) (var67 Heap)) (or (not (and (inv_main556_3 var67 var66 var65 var64 var63 var62) (and (and (and (and (= var61 nullAddr) (and (and (and (and (and (and (and (and (= var60 (newHeap (alloc var59 (O_list var58)))) (or (and var56 (= var57 (newAddr (alloc var59 (O_list var58))))) (and (not var56) (= var57 var55)))) (= var54 var53)) (= var52 var51)) (= var50 var49)) (= var48 var47)) (= var46 var49)) (= var45 5)) (= var44 (newAddr (alloc var59 (O_list var58)))))) (and (and (and (and (and (and (and (= var43 (write var60 var44 (O_list (list var45 (|list::next| (getlist (read var60 var44))))))) (= var42 var57)) (= var61 var54)) (= var41 var52)) (= var40 var50)) (= var39 var48)) (= var38 var44)) (= var37 var45))) (and (and (and (and (and (and (and (= var36 (write var43 var38 (O_list (list (|list::key| (getlist (read var43 var38))) nullAddr)))) (= var35 var42)) (= var34 var61)) (= var33 var41)) (= var32 var40)) (= var31 var39)) (= var30 var38)) (= var29 var37))) (and (and (and (and (not (= var28 nullAddr)) (and (and (and (and (and (and (and (and (= var27 (newHeap (alloc var67 (O_list var26)))) (or (and var24 (= var25 (newAddr (alloc var67 (O_list var26))))) (and (not var24) (= var25 var66)))) (= var23 var65)) (= var22 var64)) (= var21 var63)) (= var20 var62)) (= var19 var63)) (= var18 2)) (= var17 (newAddr (alloc var67 (O_list var26)))))) (and (and (and (and (and (and (and (= var16 (write var27 var17 (O_list (list var18 (|list::next| (getlist (read var27 var17))))))) (= var15 var25)) (= var28 var23)) (= var14 var22)) (= var13 var21)) (= var12 var20)) (= var11 var17)) (= var10 var18))) (and (and (and (and (and (and (and (= var9 (write var16 var11 (O_list (list var10 (|list::next| (getlist (read var16 var11))))))) (= var8 var15)) (= var7 var28)) (= var6 var14)) (= var5 var13)) (= var4 var12)) (= var3 var11)) (= var2 var10))) (and (and (and (and (and (and (and (= var59 (write var9 var3 (O_list (list (|list::key| (getlist (read var9 var3))) var7)))) (= var55 var8)) (= var1 var7)) (= var51 var6)) (= var49 var5)) (= var47 var4)) (= var53 var3)) (= var0 var2)))))) (inv_main_7 var36 var35 var30 var33 var32 var31))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Int) (var7 Addr) (var8 Addr) (var9 Heap) (var10 Int) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Int) (var15 Addr) (var16 Heap) (var17 Addr) (var18 Int) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Int) (var23 Addr) (var24 Bool) (var25 Addr) (var26 list) (var27 Heap) (var28 Addr) (var29 Int) (var30 Addr) (var31 Addr) (var32 Addr) (var33 Int) (var34 Addr) (var35 Addr) (var36 Heap) (var37 Int) (var38 Addr) (var39 Addr) (var40 Addr) (var41 Int) (var42 Addr) (var43 Addr) (var44 Heap) (var45 Int) (var46 Addr) (var47 Addr) (var48 Addr) (var49 Int) (var50 Addr) (var51 Heap) (var52 Addr) (var53 Int) (var54 Addr) (var55 Addr) (var56 Addr) (var57 Addr) (var58 Addr) (var59 Int) (var60 Int) (var61 Addr) (var62 Addr) (var63 Addr) (var64 Bool) (var65 Addr) (var66 list) (var67 Heap) (var68 Heap) (var69 Addr) (var70 Addr) (var71 Addr) (var72 Int) (var73 Addr) (var74 Addr) (var75 Heap)) (or (not (and (inv_main556_3 var75 var74 var73 var72 var71 var70) (and (and (and (and (and (not (= var69 nullAddr)) (and (and (and (and (and (and (and (and (= var68 (newHeap (alloc var67 (O_list var66)))) (or (and var64 (= var65 (newAddr (alloc var67 (O_list var66))))) (and (not var64) (= var65 var63)))) (= var62 var61)) (= var60 var59)) (= var58 var57)) (= var56 var55)) (= var54 var57)) (= var53 5)) (= var52 (newAddr (alloc var67 (O_list var66)))))) (and (and (and (and (and (and (and (= var51 (write var68 var52 (O_list (list var53 (|list::next| (getlist (read var68 var52))))))) (= var50 var65)) (= var69 var62)) (= var49 var60)) (= var48 var58)) (= var47 var56)) (= var46 var52)) (= var45 var53))) (and (and (and (and (and (and (and (= var44 (write var51 var46 (O_list (list var45 (|list::next| (getlist (read var51 var46))))))) (= var43 var50)) (= var42 var69)) (= var41 var49)) (= var40 var48)) (= var39 var47)) (= var38 var46)) (= var37 var45))) (and (and (and (and (and (and (and (= var36 (write var44 var38 (O_list (list (|list::key| (getlist (read var44 var38))) var42)))) (= var35 var43)) (= var34 var42)) (= var33 var41)) (= var32 var40)) (= var31 var39)) (= var30 var38)) (= var29 var37))) (and (and (and (and (not (= var28 nullAddr)) (and (and (and (and (and (and (and (and (= var27 (newHeap (alloc var75 (O_list var26)))) (or (and var24 (= var25 (newAddr (alloc var75 (O_list var26))))) (and (not var24) (= var25 var74)))) (= var23 var73)) (= var22 var72)) (= var21 var71)) (= var20 var70)) (= var19 var71)) (= var18 2)) (= var17 (newAddr (alloc var75 (O_list var26)))))) (and (and (and (and (and (and (and (= var16 (write var27 var17 (O_list (list var18 (|list::next| (getlist (read var27 var17))))))) (= var15 var25)) (= var28 var23)) (= var14 var22)) (= var13 var21)) (= var12 var20)) (= var11 var17)) (= var10 var18))) (and (and (and (and (and (and (and (= var9 (write var16 var11 (O_list (list var10 (|list::next| (getlist (read var16 var11))))))) (= var8 var15)) (= var7 var28)) (= var6 var14)) (= var5 var13)) (= var4 var12)) (= var3 var11)) (= var2 var10))) (and (and (and (and (and (and (and (= var67 (write var9 var3 (O_list (list (|list::key| (getlist (read var9 var3))) var7)))) (= var63 var8)) (= var1 var7)) (= var59 var6)) (= var57 var5)) (= var55 var4)) (= var61 var3)) (= var0 var2)))))) (inv_main_7 var36 var35 var30 var33 var32 var31))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Int) (var7 Addr) (var8 Addr) (var9 Int) (var10 Addr) (var11 Addr) (var12 Heap) (var13 Int) (var14 Int) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Int) (var19 Addr) (var20 Addr) (var21 Heap)) (or (not (and (inv_main_44 var21 var20 var19 var18 var17 var16 var15 var14) (and (and (and (= var13 0) (and (and (and (and (and (and (= var12 var21) (= var11 var20)) (= var10 var19)) (= var9 var18)) (= var8 var17)) (= var7 var15)) (= var6 (|list::key| (getlist (read var21 var15)))))) (and (and (and (and (and (and (= var5 var12) (= var4 var11)) (= var3 var10)) (= var2 var9)) (= var1 var8)) (= var0 var7)) (or (and (= var6 1) (= var13 1)) (and (not (= var6 1)) (= var13 0))))) (= var15 nullAddr)))) (inv_exit var5 var4))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Int) (var8 Addr) (var9 Addr) (var10 Heap) (var11 Int) (var12 Addr) (var13 Addr) (var14 Int) (var15 Addr) (var16 Addr) (var17 Heap) (var18 Int) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Int) (var24 Int) (var25 Addr) (var26 Addr) (var27 Addr) (var28 Addr) (var29 Heap) (var30 Heap) (var31 Int) (var32 Int) (var33 Addr) (var34 Addr) (var35 Addr) (var36 Int) (var37 Addr) (var38 Addr) (var39 Heap)) (or (not (and (inv_main_44 var39 var38 var37 var36 var35 var34 var33 var32) (and (and (and (= var31 0) (and (and (and (and (and (and (= var30 var29) (= var28 var27)) (= var26 var25)) (= var24 var23)) (= var22 var21)) (= var20 var19)) (= var18 (|list::key| (getlist (read var29 var19)))))) (and (and (and (and (and (and (= var17 var30) (= var16 var28)) (= var15 var26)) (= var14 var24)) (= var13 var22)) (= var12 var20)) (or (and (= var18 1) (= var31 1)) (and (not (= var18 1)) (= var31 0))))) (and (and (= var11 0) (and (not (= var33 nullAddr)) (and (and (and (and (and (and (and (and (= var10 var39) (= var9 var38)) (= var8 var37)) (= var7 var36)) (= var6 var35)) (= var5 var34)) (= var4 var33)) (= var3 var32)) (= var2 (|list::key| (getlist (read var39 var33))))))) (and (and (and (and (and (and (and (and (= var29 var10) (= var27 var9)) (= var25 var8)) (= var23 var7)) (= var21 var6)) (= var1 var5)) (= var19 var4)) (= var0 var3)) (or (and (not (= var2 var3)) (= var11 1)) (and (= var2 var3) (= var11 0)))))))) (inv_exit var17 var16))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Int) (var11 Addr) (var12 Addr) (var13 Heap) (var14 Addr) (var15 Addr) (var16 Int) (var17 Addr) (var18 Addr) (var19 Heap)) (or (not (and (inv_main_47 var19 var18 var17 var16 var15 var14) (and (and (and (and (and (and (and (and (= var13 var19) (= var12 var18)) (= var11 var17)) (= var10 var16)) (= var9 var15)) (= var8 var14)) (= var7 (|list::next| (getlist (read var19 var17))))) (and (and (and (and (and (and (= var6 (write var13 var11 defObj)) (or (and (= var12 var11) (= var5 nullAddr)) (and (not (= var12 var11)) (= var5 var12)))) (= var4 var11)) (= var3 var10)) (= var2 var9)) (= var1 var8)) (= var0 var7))) (not (= var17 nullAddr))))) (inv_main_47 var6 var5 var0 var3 var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Int) (var7 Addr) (var8 Addr) (var9 Int) (var10 Addr) (var11 Addr) (var12 Heap) (var13 Int) (var14 Int) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Int) (var19 Addr) (var20 Addr) (var21 Heap)) (or (not (and (inv_main_44 var21 var20 var19 var18 var17 var16 var15 var14) (and (and (and (not (= var13 0)) (and (and (and (and (and (and (= var12 var21) (= var11 var20)) (= var10 var19)) (= var9 var18)) (= var8 var17)) (= var7 var15)) (= var6 (|list::key| (getlist (read var21 var15)))))) (and (and (and (and (and (and (= var5 var12) (= var4 var11)) (= var3 var10)) (= var2 var9)) (= var1 var8)) (= var0 var7)) (or (and (= var6 1) (= var13 1)) (and (not (= var6 1)) (= var13 0))))) (= var15 nullAddr)))) (inv_main_47 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Int) (var8 Addr) (var9 Addr) (var10 Heap) (var11 Int) (var12 Addr) (var13 Addr) (var14 Int) (var15 Addr) (var16 Addr) (var17 Heap) (var18 Int) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Int) (var24 Int) (var25 Addr) (var26 Addr) (var27 Addr) (var28 Addr) (var29 Heap) (var30 Heap) (var31 Int) (var32 Int) (var33 Addr) (var34 Addr) (var35 Addr) (var36 Int) (var37 Addr) (var38 Addr) (var39 Heap)) (or (not (and (inv_main_44 var39 var38 var37 var36 var35 var34 var33 var32) (and (and (and (not (= var31 0)) (and (and (and (and (and (and (= var30 var29) (= var28 var27)) (= var26 var25)) (= var24 var23)) (= var22 var21)) (= var20 var19)) (= var18 (|list::key| (getlist (read var29 var19)))))) (and (and (and (and (and (and (= var17 var30) (= var16 var28)) (= var15 var26)) (= var14 var24)) (= var13 var22)) (= var12 var20)) (or (and (= var18 1) (= var31 1)) (and (not (= var18 1)) (= var31 0))))) (and (and (= var11 0) (and (not (= var33 nullAddr)) (and (and (and (and (and (and (and (and (= var10 var39) (= var9 var38)) (= var8 var37)) (= var7 var36)) (= var6 var35)) (= var5 var34)) (= var4 var33)) (= var3 var32)) (= var2 (|list::key| (getlist (read var39 var33))))))) (and (and (and (and (and (and (and (and (= var29 var10) (= var27 var9)) (= var25 var8)) (= var23 var7)) (= var21 var6)) (= var1 var5)) (= var19 var4)) (= var0 var3)) (or (and (not (= var2 var3)) (= var11 1)) (and (= var2 var3) (= var11 0)))))))) (inv_main_47 var17 var16 var15 var14 var13 var12))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Int) (var6 Addr) (var7 Addr) (var8 Heap) (var9 Int) (var10 Addr) (var11 Int) (var12 Int) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Int) (var20 Int) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Addr) (var25 Heap) (var26 Heap) (var27 Int) (var28 Addr) (var29 Addr) (var30 Addr) (var31 Int) (var32 Addr) (var33 Addr) (var34 Heap)) (or (not (and (inv_main_44 var34 var33 var32 var31 var30 var29 var28 var27) (and (and (and (and (and (and (and (and (and (= var26 var25) (= var24 var23)) (= var22 var21)) (= var20 var19)) (= var18 var17)) (= var16 var15)) (= var14 var13)) (= var12 var11)) (= var10 (|list::next| (getlist (read var25 var13))))) (and (and (not (= var9 0)) (and (not (= var28 nullAddr)) (and (and (and (and (and (and (and (and (= var8 var34) (= var7 var33)) (= var6 var32)) (= var5 var31)) (= var4 var30)) (= var3 var29)) (= var2 var28)) (= var1 var27)) (= var0 (|list::key| (getlist (read var34 var28))))))) (and (and (and (and (and (and (and (and (= var25 var8) (= var23 var7)) (= var21 var6)) (= var19 var5)) (= var17 var4)) (= var15 var3)) (= var13 var2)) (= var11 var1)) (or (and (not (= var0 var1)) (= var9 1)) (and (= var0 var1) (= var9 0)))))))) (inv_main_44 var26 var24 var22 var20 var18 var16 var10 var12))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Int) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Int) (var8 Addr) (var9 Heap) (var10 Addr) (var11 Int) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Int) (var16 Addr) (var17 Bool) (var18 Addr) (var19 list) (var20 Heap) (var21 Addr) (var22 Int) (var23 Addr) (var24 Addr) (var25 Addr) (var26 Int) (var27 Addr) (var28 Addr) (var29 Heap) (var30 Int) (var31 Addr) (var32 Addr) (var33 Addr) (var34 Int) (var35 Addr) (var36 Heap) (var37 Addr) (var38 Int) (var39 Addr) (var40 Addr) (var41 Addr) (var42 Addr) (var43 Addr) (var44 Int) (var45 Int) (var46 Addr) (var47 Addr) (var48 Addr) (var49 Bool) (var50 Addr) (var51 list) (var52 Heap) (var53 Heap) (var54 Addr) (var55 Addr) (var56 Addr) (var57 Int) (var58 Addr) (var59 Addr) (var60 Heap)) (or (not (and (inv_main_7 var60 var59 var58 var57 var56 var55) (and (and (and (and (and (= var54 nullAddr) (and (and (and (and (and (and (and (and (= var53 (newHeap (alloc var52 (O_list var51)))) (or (and var49 (= var50 (newAddr (alloc var52 (O_list var51))))) (and (not var49) (= var50 var48)))) (= var47 var46)) (= var45 var44)) (= var43 var42)) (= var41 var40)) (= var39 var42)) (= var38 3)) (= var37 (newAddr (alloc var52 (O_list var51)))))) (and (and (and (and (and (and (and (= var36 (write var53 var37 (O_list (list var38 (|list::next| (getlist (read var53 var37))))))) (= var35 var50)) (= var54 var47)) (= var34 var45)) (= var33 var43)) (= var32 var41)) (= var31 var37)) (= var30 var38))) (and (and (and (and (and (and (and (= var29 (write var36 var31 (O_list (list (|list::key| (getlist (read var36 var31))) nullAddr)))) (= var28 var35)) (= var27 var54)) (= var26 var34)) (= var25 var33)) (= var24 var32)) (= var23 var31)) (= var22 var30))) (and (and (and (= var21 nullAddr) (and (and (and (and (and (and (and (and (= var20 (newHeap (alloc var60 (O_list var19)))) (or (and var17 (= var18 (newAddr (alloc var60 (O_list var19))))) (and (not var17) (= var18 var59)))) (= var16 var58)) (= var15 var57)) (= var14 var56)) (= var13 var55)) (= var12 var56)) (= var11 1)) (= var10 (newAddr (alloc var60 (O_list var19)))))) (and (and (and (and (and (and (and (= var9 (write var20 var10 (O_list (list var11 (|list::next| (getlist (read var20 var10))))))) (= var8 var18)) (= var21 var16)) (= var7 var15)) (= var6 var14)) (= var5 var13)) (= var4 var10)) (= var3 var11))) (and (and (and (and (and (and (and (= var52 (write var9 var4 (O_list (list (|list::key| (getlist (read var9 var4))) nullAddr)))) (= var48 var8)) (= var2 var21)) (= var44 var7)) (= var42 var6)) (= var40 var5)) (= var46 var4)) (= var1 var3)))) (= var0 2)))) (inv_main_44 var29 var28 var23 var26 var25 var24 var23 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Int) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Int) (var8 Addr) (var9 Heap) (var10 Addr) (var11 Int) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Int) (var16 Addr) (var17 Bool) (var18 Addr) (var19 list) (var20 Heap) (var21 Addr) (var22 Int) (var23 Addr) (var24 Addr) (var25 Addr) (var26 Int) (var27 Addr) (var28 Addr) (var29 Heap) (var30 Int) (var31 Addr) (var32 Addr) (var33 Addr) (var34 Int) (var35 Addr) (var36 Addr) (var37 Heap) (var38 Int) (var39 Addr) (var40 Addr) (var41 Addr) (var42 Int) (var43 Addr) (var44 Heap) (var45 Addr) (var46 Int) (var47 Addr) (var48 Addr) (var49 Addr) (var50 Addr) (var51 Addr) (var52 Int) (var53 Int) (var54 Addr) (var55 Addr) (var56 Addr) (var57 Bool) (var58 Addr) (var59 list) (var60 Heap) (var61 Heap) (var62 Addr) (var63 Addr) (var64 Addr) (var65 Int) (var66 Addr) (var67 Addr) (var68 Heap)) (or (not (and (inv_main_7 var68 var67 var66 var65 var64 var63) (and (and (and (and (and (and (not (= var62 nullAddr)) (and (and (and (and (and (and (and (and (= var61 (newHeap (alloc var60 (O_list var59)))) (or (and var57 (= var58 (newAddr (alloc var60 (O_list var59))))) (and (not var57) (= var58 var56)))) (= var55 var54)) (= var53 var52)) (= var51 var50)) (= var49 var48)) (= var47 var50)) (= var46 3)) (= var45 (newAddr (alloc var60 (O_list var59)))))) (and (and (and (and (and (and (and (= var44 (write var61 var45 (O_list (list var46 (|list::next| (getlist (read var61 var45))))))) (= var43 var58)) (= var62 var55)) (= var42 var53)) (= var41 var51)) (= var40 var49)) (= var39 var45)) (= var38 var46))) (and (and (and (and (and (and (and (= var37 (write var44 var39 (O_list (list var38 (|list::next| (getlist (read var44 var39))))))) (= var36 var43)) (= var35 var62)) (= var34 var42)) (= var33 var41)) (= var32 var40)) (= var31 var39)) (= var30 var38))) (and (and (and (and (and (and (and (= var29 (write var37 var31 (O_list (list (|list::key| (getlist (read var37 var31))) var35)))) (= var28 var36)) (= var27 var35)) (= var26 var34)) (= var25 var33)) (= var24 var32)) (= var23 var31)) (= var22 var30))) (and (and (and (= var21 nullAddr) (and (and (and (and (and (and (and (and (= var20 (newHeap (alloc var68 (O_list var19)))) (or (and var17 (= var18 (newAddr (alloc var68 (O_list var19))))) (and (not var17) (= var18 var67)))) (= var16 var66)) (= var15 var65)) (= var14 var64)) (= var13 var63)) (= var12 var64)) (= var11 1)) (= var10 (newAddr (alloc var68 (O_list var19)))))) (and (and (and (and (and (and (and (= var9 (write var20 var10 (O_list (list var11 (|list::next| (getlist (read var20 var10))))))) (= var8 var18)) (= var21 var16)) (= var7 var15)) (= var6 var14)) (= var5 var13)) (= var4 var10)) (= var3 var11))) (and (and (and (and (and (and (and (= var60 (write var9 var4 (O_list (list (|list::key| (getlist (read var9 var4))) nullAddr)))) (= var56 var8)) (= var2 var21)) (= var52 var7)) (= var50 var6)) (= var48 var5)) (= var54 var4)) (= var1 var3)))) (= var0 2)))) (inv_main_44 var29 var28 var23 var26 var25 var24 var23 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Int) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Int) (var8 Addr) (var9 Addr) (var10 Heap) (var11 Int) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Int) (var16 Addr) (var17 Heap) (var18 Addr) (var19 Int) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Int) (var24 Addr) (var25 Bool) (var26 Addr) (var27 list) (var28 Heap) (var29 Addr) (var30 Int) (var31 Addr) (var32 Addr) (var33 Addr) (var34 Int) (var35 Addr) (var36 Addr) (var37 Heap) (var38 Int) (var39 Addr) (var40 Addr) (var41 Addr) (var42 Int) (var43 Addr) (var44 Heap) (var45 Addr) (var46 Int) (var47 Addr) (var48 Addr) (var49 Addr) (var50 Addr) (var51 Addr) (var52 Int) (var53 Int) (var54 Addr) (var55 Addr) (var56 Addr) (var57 Bool) (var58 Addr) (var59 list) (var60 Heap) (var61 Heap) (var62 Addr) (var63 Addr) (var64 Addr) (var65 Int) (var66 Addr) (var67 Addr) (var68 Heap)) (or (not (and (inv_main_7 var68 var67 var66 var65 var64 var63) (and (and (and (and (and (= var62 nullAddr) (and (and (and (and (and (and (and (and (= var61 (newHeap (alloc var60 (O_list var59)))) (or (and var57 (= var58 (newAddr (alloc var60 (O_list var59))))) (and (not var57) (= var58 var56)))) (= var55 var54)) (= var53 var52)) (= var51 var50)) (= var49 var48)) (= var47 var50)) (= var46 3)) (= var45 (newAddr (alloc var60 (O_list var59)))))) (and (and (and (and (and (and (and (= var44 (write var61 var45 (O_list (list var46 (|list::next| (getlist (read var61 var45))))))) (= var43 var58)) (= var62 var55)) (= var42 var53)) (= var41 var51)) (= var40 var49)) (= var39 var45)) (= var38 var46))) (and (and (and (and (and (and (and (= var37 (write var44 var39 (O_list (list (|list::key| (getlist (read var44 var39))) nullAddr)))) (= var36 var43)) (= var35 var62)) (= var34 var42)) (= var33 var41)) (= var32 var40)) (= var31 var39)) (= var30 var38))) (and (and (and (and (not (= var29 nullAddr)) (and (and (and (and (and (and (and (and (= var28 (newHeap (alloc var68 (O_list var27)))) (or (and var25 (= var26 (newAddr (alloc var68 (O_list var27))))) (and (not var25) (= var26 var67)))) (= var24 var66)) (= var23 var65)) (= var22 var64)) (= var21 var63)) (= var20 var64)) (= var19 1)) (= var18 (newAddr (alloc var68 (O_list var27)))))) (and (and (and (and (and (and (and (= var17 (write var28 var18 (O_list (list var19 (|list::next| (getlist (read var28 var18))))))) (= var16 var26)) (= var29 var24)) (= var15 var23)) (= var14 var22)) (= var13 var21)) (= var12 var18)) (= var11 var19))) (and (and (and (and (and (and (and (= var10 (write var17 var12 (O_list (list var11 (|list::next| (getlist (read var17 var12))))))) (= var9 var16)) (= var8 var29)) (= var7 var15)) (= var6 var14)) (= var5 var13)) (= var4 var12)) (= var3 var11))) (and (and (and (and (and (and (and (= var60 (write var10 var4 (O_list (list (|list::key| (getlist (read var10 var4))) var8)))) (= var56 var9)) (= var2 var8)) (= var52 var7)) (= var50 var6)) (= var48 var5)) (= var54 var4)) (= var1 var3)))) (= var0 2)))) (inv_main_44 var37 var36 var31 var34 var33 var32 var31 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Int) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Int) (var8 Addr) (var9 Addr) (var10 Heap) (var11 Int) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Int) (var16 Addr) (var17 Heap) (var18 Addr) (var19 Int) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Int) (var24 Addr) (var25 Bool) (var26 Addr) (var27 list) (var28 Heap) (var29 Addr) (var30 Int) (var31 Addr) (var32 Addr) (var33 Addr) (var34 Int) (var35 Addr) (var36 Addr) (var37 Heap) (var38 Int) (var39 Addr) (var40 Addr) (var41 Addr) (var42 Int) (var43 Addr) (var44 Addr) (var45 Heap) (var46 Int) (var47 Addr) (var48 Addr) (var49 Addr) (var50 Int) (var51 Addr) (var52 Heap) (var53 Addr) (var54 Int) (var55 Addr) (var56 Addr) (var57 Addr) (var58 Addr) (var59 Addr) (var60 Int) (var61 Int) (var62 Addr) (var63 Addr) (var64 Addr) (var65 Bool) (var66 Addr) (var67 list) (var68 Heap) (var69 Heap) (var70 Addr) (var71 Addr) (var72 Addr) (var73 Int) (var74 Addr) (var75 Addr) (var76 Heap)) (or (not (and (inv_main_7 var76 var75 var74 var73 var72 var71) (and (and (and (and (and (and (not (= var70 nullAddr)) (and (and (and (and (and (and (and (and (= var69 (newHeap (alloc var68 (O_list var67)))) (or (and var65 (= var66 (newAddr (alloc var68 (O_list var67))))) (and (not var65) (= var66 var64)))) (= var63 var62)) (= var61 var60)) (= var59 var58)) (= var57 var56)) (= var55 var58)) (= var54 3)) (= var53 (newAddr (alloc var68 (O_list var67)))))) (and (and (and (and (and (and (and (= var52 (write var69 var53 (O_list (list var54 (|list::next| (getlist (read var69 var53))))))) (= var51 var66)) (= var70 var63)) (= var50 var61)) (= var49 var59)) (= var48 var57)) (= var47 var53)) (= var46 var54))) (and (and (and (and (and (and (and (= var45 (write var52 var47 (O_list (list var46 (|list::next| (getlist (read var52 var47))))))) (= var44 var51)) (= var43 var70)) (= var42 var50)) (= var41 var49)) (= var40 var48)) (= var39 var47)) (= var38 var46))) (and (and (and (and (and (and (and (= var37 (write var45 var39 (O_list (list (|list::key| (getlist (read var45 var39))) var43)))) (= var36 var44)) (= var35 var43)) (= var34 var42)) (= var33 var41)) (= var32 var40)) (= var31 var39)) (= var30 var38))) (and (and (and (and (not (= var29 nullAddr)) (and (and (and (and (and (and (and (and (= var28 (newHeap (alloc var76 (O_list var27)))) (or (and var25 (= var26 (newAddr (alloc var76 (O_list var27))))) (and (not var25) (= var26 var75)))) (= var24 var74)) (= var23 var73)) (= var22 var72)) (= var21 var71)) (= var20 var72)) (= var19 1)) (= var18 (newAddr (alloc var76 (O_list var27)))))) (and (and (and (and (and (and (and (= var17 (write var28 var18 (O_list (list var19 (|list::next| (getlist (read var28 var18))))))) (= var16 var26)) (= var29 var24)) (= var15 var23)) (= var14 var22)) (= var13 var21)) (= var12 var18)) (= var11 var19))) (and (and (and (and (and (and (and (= var10 (write var17 var12 (O_list (list var11 (|list::next| (getlist (read var17 var12))))))) (= var9 var16)) (= var8 var29)) (= var7 var15)) (= var6 var14)) (= var5 var13)) (= var4 var12)) (= var3 var11))) (and (and (and (and (and (and (and (= var68 (write var10 var4 (O_list (list (|list::key| (getlist (read var10 var4))) var8)))) (= var64 var9)) (= var2 var8)) (= var60 var7)) (= var58 var6)) (= var56 var5)) (= var62 var4)) (= var1 var3)))) (= var0 2)))) (inv_main_44 var37 var36 var31 var34 var33 var32 var31 var0))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_exit var1 var0) (not (= var0 nullAddr))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main565_12_0 var2 var1 var0) (not (= var1 nullAddr))))))
(check-sat)