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

(declare-datatypes ((HeapObject 0) (TSLL 0))
                   (((O_Int (getInt Int)) (O_UInt (getUInt Int)) (O_Addr (getAddr Addr)) (O_AddrRange (getAddrRange AddrRange)) (O_TSLL (getTSLL TSLL)) (defObj))
                   ((TSLL (|TSLL::next| Addr) (|TSLL::data| Int)))))
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
(declare-fun inv_main1001_2 (Heap Addr Addr Addr Int) Bool)
(declare-fun inv_main1075_9 (Heap Addr Int) Bool)
(declare-fun inv_main996_2 (Heap Addr) Bool)
(declare-fun inv_main_15 (Heap Addr Addr Addr Int) Bool)
(declare-fun inv_main_16 (Heap Addr Addr Addr Int) Bool)
(declare-fun inv_main_33 (Heap Addr Addr Addr Int Addr) Bool)
(declare-fun inv_main_34 (Heap Addr Addr Addr Int Addr) Bool)
(declare-fun inv_main_52 (Heap Addr Addr Addr Int Addr) Bool)
(assert (forall ((var0 Addr) (var1 Heap)) (or (not (and (= var1 emptyHeap) (= var0 nullAddr))) (inv_main996_2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main_33 var5 var4 var3 var2 var1 var0) (= var2 nullAddr))) (inv_main_34 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Int) (var7 Addr) (var8 Int) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Heap) (var13 Int) (var14 Addr) (var15 Int) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Heap)) (or (not (and (inv_main_33 var19 var18 var17 var16 var15 var14) (and (and (= var13 0) (and (not (= var16 nullAddr)) (and (and (and (and (and (and (= var12 var19) (= var11 var18)) (= var10 var17)) (= var9 var16)) (= var8 var15)) (= var7 var14)) (= var6 (|TSLL::data| (getTSLL (read var19 var16))))))) (and (and (and (and (and (and (= var5 var12) (= var4 var11)) (= var3 var10)) (= var2 var9)) (= var1 var8)) (= var0 var7)) (or (and (not (= var6 1)) (= var13 1)) (and (= var6 1) (= var13 0))))))) (inv_main_34 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Int) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Int) (var12 Int) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Heap) (var20 Heap) (var21 Addr) (var22 Int) (var23 Addr) (var24 Addr) (var25 Addr) (var26 Heap)) (or (not (and (inv_main_34 var26 var25 var24 var23 var22 var21) (and (and (and (and (and (and (and (= var20 var19) (= var18 var17)) (= var16 var15)) (= var14 var13)) (= var12 var11)) (= var10 var9)) (= var8 (|TSLL::next| (getTSLL (read var19 var13))))) (and (= var11 1) (and (and (= var7 1) (and (and (and (and (and (and (= var19 var6) (= var17 var5)) (= var15 var4)) (= var13 var3)) (= var11 var2)) (= var9 var1)) (= var7 (|TSLL::data| (getTSLL (read var6 var3)))))) (and (and (and (and (and (and (and (= var6 var26) (= var5 var25)) (= var4 var24)) (= var3 var23)) (= var0 var22)) (= var1 var21)) (= var2 (|TSLL::data| (getTSLL (read var26 var23))))) (not (= var23 nullAddr)))))))) (inv_main_34 var20 var18 var16 var8 var12 var10))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main1001_2 var6 var5 var4 var3 var2) (and (and (not (= nullAddr var4)) (and (= var1 0) (not (= var2 0)))) (= var0 0)))) (inv_main_15 var6 var5 var4 var4 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Int) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap) (var11 Addr) (var12 Int) (var13 Int) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Heap) (var18 Int) (var19 Addr) (var20 Int) (var21 Int) (var22 Addr) (var23 Addr) (var24 Addr) (var25 Addr) (var26 Addr) (var27 Addr) (var28 Heap) (var29 Heap) (var30 Int) (var31 Addr) (var32 Addr) (var33 Addr) (var34 Heap)) (or (not (and (inv_main_15 var34 var33 var32 var31 var30) (and (and (and (and (and (and (= var29 var28) (= var27 var26)) (= var25 var24)) (= var23 var22)) (= var21 var20)) (= var19 (|TSLL::next| (getTSLL (read var28 var22))))) (and (and (= var18 0) (and (and (and (and (and (= var28 var17) (= var26 var16)) (= var24 var15)) (= var22 var14)) (= var20 var13)) (= var18 (|TSLL::data| (getTSLL (read var17 var14)))))) (and (and (not (= var12 0)) (and (and (not (= var11 nullAddr)) (and (and (and (and (and (= var10 var34) (= var9 var33)) (= var8 var32)) (= var7 var31)) (= var6 var30)) (= var11 (|TSLL::next| (getTSLL (read var34 var31)))))) (and (and (and (and (and (= var5 var10) (= var4 var9)) (= var3 var8)) (= var2 var7)) (= var1 var6)) (= var0 (|TSLL::data| (getTSLL (read var10 (|TSLL::next| (getTSLL (read var10 var7)))))))))) (and (and (and (and (and (= var17 var5) (= var16 var4)) (= var15 var3)) (= var14 var2)) (= var13 var1)) (or (and (= var0 0) (= var12 1)) (and (not (= var0 0)) (= var12 0))))))))) (inv_main_15 var29 var27 var25 var19 var21))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Int) (var8 Addr) (var9 Int) (var10 Int) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Heap) (var15 Addr) (var16 Addr) (var17 Int) (var18 Int) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Addr) (var25 Heap) (var26 Heap) (var27 Int) (var28 Addr) (var29 Int) (var30 Addr) (var31 Addr) (var32 Addr) (var33 Heap)) (or (not (and (inv_main_33 var33 var32 var31 var30 var29 var28) (and (and (not (= var27 0)) (and (and (and (and (and (and (= var26 var25) (= var24 var23)) (= var22 var21)) (= var20 var19)) (= var18 var17)) (= var16 var15)) (= var27 (|TSLL::data| (getTSLL (read var25 var19)))))) (and (and (and (and (and (and (and (= var25 var14) (= var23 var13)) (= var21 var12)) (= var19 var11)) (= var10 var9)) (= var15 var8)) (= var17 (|TSLL::data| (getTSLL (read var14 var11))))) (and (and (not (= var7 0)) (and (not (= var30 nullAddr)) (and (and (and (and (and (and (= var6 var33) (= var5 var32)) (= var4 var31)) (= var3 var30)) (= var2 var29)) (= var1 var28)) (= var0 (|TSLL::data| (getTSLL (read var33 var30))))))) (and (and (and (and (and (and (= var14 var6) (= var13 var5)) (= var12 var4)) (= var11 var3)) (= var9 var2)) (= var8 var1)) (or (and (not (= var0 1)) (= var7 1)) (and (= var0 1) (= var7 0))))))))) (inv_exit var26 var24))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Int) (var8 Addr) (var9 Int) (var10 Int) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Heap) (var15 Addr) (var16 Addr) (var17 Int) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Heap) (var25 Heap) (var26 Int) (var27 Int) (var28 Addr) (var29 Int) (var30 Addr) (var31 Addr) (var32 Addr) (var33 Heap)) (or (not (and (inv_main_33 var33 var32 var31 var30 var29 var28) (and (not (= var27 0)) (and (and (= var26 0) (and (and (and (and (and (and (= var25 var24) (= var23 var22)) (= var21 var20)) (= var19 var18)) (= var27 var17)) (= var16 var15)) (= var26 (|TSLL::data| (getTSLL (read var24 var18)))))) (and (and (and (and (and (and (and (= var24 var14) (= var22 var13)) (= var20 var12)) (= var18 var11)) (= var10 var9)) (= var15 var8)) (= var17 (|TSLL::data| (getTSLL (read var14 var11))))) (and (and (not (= var7 0)) (and (not (= var30 nullAddr)) (and (and (and (and (and (and (= var6 var33) (= var5 var32)) (= var4 var31)) (= var3 var30)) (= var2 var29)) (= var1 var28)) (= var0 (|TSLL::data| (getTSLL (read var33 var30))))))) (and (and (and (and (and (and (= var14 var6) (= var13 var5)) (= var12 var4)) (= var11 var3)) (= var9 var2)) (= var8 var1)) (or (and (not (= var0 1)) (= var7 1)) (and (= var0 1) (= var7 0)))))))))) (inv_exit var25 var23))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Heap) (var12 Heap) (var13 Int) (var14 Addr) (var15 Int) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Heap)) (or (not (and (inv_main_34 var19 var18 var17 var16 var15 var14) (and (and (not (= var13 1)) (and (and (and (and (and (and (= var12 var11) (= var10 var9)) (= var8 var7)) (= var6 var5)) (= var4 var3)) (= var2 var1)) (= var13 (|TSLL::data| (getTSLL (read var11 var5)))))) (and (and (and (and (and (and (and (= var11 var19) (= var9 var18)) (= var7 var17)) (= var5 var16)) (= var0 var15)) (= var1 var14)) (= var3 (|TSLL::data| (getTSLL (read var19 var16))))) (not (= var16 nullAddr)))))) (inv_exit var12 var10))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap) (var11 Heap) (var12 Int) (var13 Int) (var14 Addr) (var15 Int) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Heap)) (or (not (and (inv_main_34 var19 var18 var17 var16 var15 var14) (and (not (= var13 1)) (and (and (= var12 1) (and (and (and (and (and (and (= var11 var10) (= var9 var8)) (= var7 var6)) (= var5 var4)) (= var13 var3)) (= var2 var1)) (= var12 (|TSLL::data| (getTSLL (read var10 var4)))))) (and (and (and (and (and (and (and (= var10 var19) (= var8 var18)) (= var6 var17)) (= var4 var16)) (= var0 var15)) (= var1 var14)) (= var3 (|TSLL::data| (getTSLL (read var19 var16))))) (not (= var16 nullAddr))))))) (inv_exit var11 var9))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main1001_2 var5 var4 var3 var2 var1) (and (= nullAddr var3) (and (= var0 0) (not (= var1 0)))))) (inv_exit var5 var4))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Int) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap) (var11 Addr) (var12 Int) (var13 Int) (var14 Int) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Heap) (var22 Heap) (var23 Int) (var24 Int) (var25 Addr) (var26 Addr) (var27 Addr) (var28 Heap)) (or (not (and (inv_main_15 var28 var27 var26 var25 var24) (and (and (not (= var23 0)) (and (and (and (and (and (= var22 var21) (= var20 var19)) (= var18 var17)) (= var16 var15)) (= var14 var13)) (= var23 (|TSLL::data| (getTSLL (read var21 var15)))))) (and (and (not (= var12 0)) (and (and (not (= var11 nullAddr)) (and (and (and (and (and (= var10 var28) (= var9 var27)) (= var8 var26)) (= var7 var25)) (= var6 var24)) (= var11 (|TSLL::next| (getTSLL (read var28 var25)))))) (and (and (and (and (and (= var5 var10) (= var4 var9)) (= var3 var8)) (= var2 var7)) (= var1 var6)) (= var0 (|TSLL::data| (getTSLL (read var10 (|TSLL::next| (getTSLL (read var10 var7)))))))))) (and (and (and (and (and (= var21 var5) (= var19 var4)) (= var17 var3)) (= var15 var2)) (= var13 var1)) (or (and (= var0 0) (= var12 1)) (and (not (= var0 0)) (= var12 0)))))))) (inv_exit var22 var20))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Int) (var9 Int) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Heap) (var17 Heap) (var18 Int) (var19 Int) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Heap)) (or (not (and (inv_main_16 var23 var22 var21 var20 var19) (and (and (not (= var18 1)) (and (and (and (and (and (= var17 var16) (= var15 var14)) (= var13 var12)) (= var11 var10)) (= var9 var8)) (= var18 (|TSLL::data| (getTSLL (read var16 var10)))))) (and (and (and (and (and (and (= var16 var7) (= var14 var6)) (= var12 var5)) (= var4 var3)) (= var8 var2)) (= var10 (|TSLL::next| (getTSLL (read var7 var3))))) (and (not (= var1 0)) (and (not (= var0 nullAddr)) (and (and (and (and (and (= var7 var23) (= var6 var22)) (= var5 var21)) (= var3 var20)) (= var2 var19)) (= var0 (|TSLL::next| (getTSLL (read var23 var20))))))))))) (inv_exit var17 var15))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Int) (var8 Addr) (var9 Int) (var10 Int) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Heap) (var15 Addr) (var16 Int) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Heap) (var21 Int) (var22 Addr) (var23 Addr) (var24 Addr) (var25 Int) (var26 Int) (var27 Addr) (var28 Addr) (var29 Addr) (var30 Addr) (var31 Addr) (var32 Addr) (var33 Heap) (var34 Heap) (var35 Addr) (var36 Int) (var37 Addr) (var38 Addr) (var39 Addr) (var40 Heap)) (or (not (and (inv_main_33 var40 var39 var38 var37 var36 var35) (and (and (and (and (and (and (and (= var34 var33) (= var32 var31)) (= var30 var29)) (= var28 var27)) (= var26 var25)) (= var24 var23)) (= var22 (|TSLL::next| (getTSLL (read var33 var27))))) (and (= var25 0) (and (and (= var21 0) (and (and (and (and (and (and (= var33 var20) (= var31 var19)) (= var29 var18)) (= var27 var17)) (= var25 var16)) (= var23 var15)) (= var21 (|TSLL::data| (getTSLL (read var20 var17)))))) (and (and (and (and (and (and (and (= var20 var14) (= var19 var13)) (= var18 var12)) (= var17 var11)) (= var10 var9)) (= var15 var8)) (= var16 (|TSLL::data| (getTSLL (read var14 var11))))) (and (and (not (= var7 0)) (and (not (= var37 nullAddr)) (and (and (and (and (and (and (= var6 var40) (= var5 var39)) (= var4 var38)) (= var3 var37)) (= var2 var36)) (= var1 var35)) (= var0 (|TSLL::data| (getTSLL (read var40 var37))))))) (and (and (and (and (and (and (= var14 var6) (= var13 var5)) (= var12 var4)) (= var11 var3)) (= var9 var2)) (= var8 var1)) (or (and (not (= var0 1)) (= var7 1)) (and (= var0 1) (= var7 0))))))))))) (inv_main_33 var34 var32 var30 var22 var26 var24))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Int) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Heap) (var14 Addr) (var15 Int) (var16 Int) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Bool) (var23 Addr) (var24 TSLL) (var25 Heap) (var26 Heap) (var27 Addr) (var28 Addr) (var29 Int) (var30 Int) (var31 Addr) (var32 Addr) (var33 Addr) (var34 Addr) (var35 Addr) (var36 Addr) (var37 Heap) (var38 Heap) (var39 Addr) (var40 Int) (var41 Addr) (var42 Addr) (var43 Addr) (var44 Heap)) (or (not (and (inv_main_16 var44 var43 var42 var41 var40) (and (and (and (and (and (and (= var39 nullAddr) (and (and (and (and (and (and (= var38 var37) (= var36 var35)) (= var34 var33)) (= var32 var31)) (= var30 var29)) (= var28 var27)) (= var39 (|TSLL::next| (getTSLL (read var37 var31)))))) (and (and (and (and (and (and (= var26 (newHeap (alloc var25 (O_TSLL var24)))) (or (and var22 (= var23 (newAddr (alloc var25 (O_TSLL var24))))) (and (not var22) (= var23 var21)))) (= var20 var19)) (= var18 var17)) (= var16 var15)) (= var14 (newAddr (alloc var25 (O_TSLL var24))))) (and (and (and (and (and (= var13 (write var26 var14 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var26 var14))) 1)))) (= var12 var23)) (= var11 var20)) (= var10 var18)) (= var9 var16)) (= var8 var14)))) (and (and (and (and (and (= var37 (write var13 var8 (O_TSLL (TSLL nullAddr (|TSLL::data| (getTSLL (read var13 var8))))))) (= var35 var12)) (= var33 var11)) (= var31 var10)) (= var29 var9)) (= var27 var8))) (and (and (and (and (and (= var7 (write var38 var32 (O_TSLL (TSLL var28 (|TSLL::data| (getTSLL (read var38 var32))))))) (= var6 var36)) (= var5 var34)) (= var4 var32)) (= var3 var30)) (= var2 var28))) (and (= var1 nullAddr) (and (and (and (and (and (= var25 var44) (= var21 var43)) (= var19 var42)) (= var17 var41)) (= var15 var40)) (= var1 (|TSLL::next| (getTSLL (read var44 var41))))))) (= var0 0)))) (inv_main_33 var7 var6 var5 var5 var0 var2))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Int) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Heap) (var14 Addr) (var15 Int) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Heap) (var20 Addr) (var21 Int) (var22 Int) (var23 Addr) (var24 Addr) (var25 Addr) (var26 Addr) (var27 Addr) (var28 Bool) (var29 Addr) (var30 TSLL) (var31 Heap) (var32 Heap) (var33 Addr) (var34 Int) (var35 Addr) (var36 Addr) (var37 Addr) (var38 Heap) (var39 Addr) (var40 Addr) (var41 Addr) (var42 Addr) (var43 Int) (var44 Int) (var45 Addr) (var46 Addr) (var47 Addr) (var48 Addr) (var49 Addr) (var50 Addr) (var51 Heap) (var52 Heap) (var53 Int) (var54 Addr) (var55 Addr) (var56 Addr) (var57 Heap)) (or (not (and (inv_main_16 var57 var56 var55 var54 var53) (and (and (and (and (and (and (and (and (and (and (and (= var52 var51) (= var50 var49)) (= var48 var47)) (= var46 var45)) (= var44 var43)) (= var42 var41)) (= var40 (|TSLL::next| (getTSLL (read var51 var45))))) (and (and (and (not (= var39 nullAddr)) (and (and (and (and (and (and (= var51 var38) (= var49 var37)) (= var47 var36)) (= var45 var35)) (= var43 var34)) (= var41 var33)) (= var39 (|TSLL::next| (getTSLL (read var38 var35)))))) (and (and (and (and (and (and (= var32 (newHeap (alloc var31 (O_TSLL var30)))) (or (and var28 (= var29 (newAddr (alloc var31 (O_TSLL var30))))) (and (not var28) (= var29 var27)))) (= var26 var25)) (= var24 var23)) (= var22 var21)) (= var20 (newAddr (alloc var31 (O_TSLL var30))))) (and (and (and (and (and (= var19 (write var32 var20 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var32 var20))) 1)))) (= var18 var29)) (= var17 var26)) (= var16 var24)) (= var15 var22)) (= var14 var20)))) (and (and (and (and (and (= var38 (write var19 var14 (O_TSLL (TSLL nullAddr (|TSLL::data| (getTSLL (read var19 var14))))))) (= var37 var18)) (= var36 var17)) (= var35 var16)) (= var34 var15)) (= var33 var14)))) (and (and (and (and (and (= var13 (write var52 var42 (O_TSLL (TSLL var40 (|TSLL::data| (getTSLL (read var52 var42))))))) (= var12 var50)) (= var11 var48)) (= var10 var46)) (= var9 var44)) (= var8 var42))) (and (and (and (and (and (= var7 (write var13 var10 (O_TSLL (TSLL var8 (|TSLL::data| (getTSLL (read var13 var10))))))) (= var6 var12)) (= var5 var11)) (= var4 var10)) (= var3 var9)) (= var2 var8))) (and (= var1 nullAddr) (and (and (and (and (and (= var31 var57) (= var27 var56)) (= var25 var55)) (= var23 var54)) (= var21 var53)) (= var1 (|TSLL::next| (getTSLL (read var57 var54))))))) (= var0 0)))) (inv_main_33 var7 var6 var5 var5 var0 var2))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Addr) (var4 Int) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap) (var9 Addr) (var10 Int) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Heap) (var15 Addr) (var16 Int) (var17 Int) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Bool) (var24 Addr) (var25 TSLL) (var26 Heap) (var27 Heap) (var28 Addr) (var29 Addr) (var30 Int) (var31 Int) (var32 Addr) (var33 Addr) (var34 Addr) (var35 Addr) (var36 Addr) (var37 Addr) (var38 Heap) (var39 Heap) (var40 Addr) (var41 Int) (var42 Addr) (var43 Addr) (var44 Addr) (var45 Heap)) (or (not (and (inv_main_16 var45 var44 var43 var42 var41) (and (and (and (and (and (and (= var40 nullAddr) (and (and (and (and (and (and (= var39 var38) (= var37 var36)) (= var35 var34)) (= var33 var32)) (= var31 var30)) (= var29 var28)) (= var40 (|TSLL::next| (getTSLL (read var38 var32)))))) (and (and (and (and (and (and (= var27 (newHeap (alloc var26 (O_TSLL var25)))) (or (and var23 (= var24 (newAddr (alloc var26 (O_TSLL var25))))) (and (not var23) (= var24 var22)))) (= var21 var20)) (= var19 var18)) (= var17 var16)) (= var15 (newAddr (alloc var26 (O_TSLL var25))))) (and (and (and (and (and (= var14 (write var27 var15 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var27 var15))) 1)))) (= var13 var24)) (= var12 var21)) (= var11 var19)) (= var10 var17)) (= var9 var15)))) (and (and (and (and (and (= var38 (write var14 var9 (O_TSLL (TSLL nullAddr (|TSLL::data| (getTSLL (read var14 var9))))))) (= var36 var13)) (= var34 var12)) (= var32 var11)) (= var30 var10)) (= var28 var9))) (and (and (and (and (and (= var8 (write var39 var33 (O_TSLL (TSLL var29 (|TSLL::data| (getTSLL (read var39 var33))))))) (= var7 var37)) (= var6 var35)) (= var5 var33)) (= var4 var31)) (= var3 var29))) (and (= var2 0) (and (not (= var1 nullAddr)) (and (and (and (and (and (= var26 var45) (= var22 var44)) (= var20 var43)) (= var18 var42)) (= var16 var41)) (= var1 (|TSLL::next| (getTSLL (read var45 var42)))))))) (= var0 0)))) (inv_main_33 var8 var7 var6 var6 var0 var3))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Addr) (var4 Int) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap) (var9 Addr) (var10 Int) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Heap) (var15 Addr) (var16 Int) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Heap) (var21 Addr) (var22 Int) (var23 Int) (var24 Addr) (var25 Addr) (var26 Addr) (var27 Addr) (var28 Addr) (var29 Bool) (var30 Addr) (var31 TSLL) (var32 Heap) (var33 Heap) (var34 Addr) (var35 Int) (var36 Addr) (var37 Addr) (var38 Addr) (var39 Heap) (var40 Addr) (var41 Addr) (var42 Addr) (var43 Addr) (var44 Int) (var45 Int) (var46 Addr) (var47 Addr) (var48 Addr) (var49 Addr) (var50 Addr) (var51 Addr) (var52 Heap) (var53 Heap) (var54 Int) (var55 Addr) (var56 Addr) (var57 Addr) (var58 Heap)) (or (not (and (inv_main_16 var58 var57 var56 var55 var54) (and (and (and (and (and (and (and (and (and (and (and (= var53 var52) (= var51 var50)) (= var49 var48)) (= var47 var46)) (= var45 var44)) (= var43 var42)) (= var41 (|TSLL::next| (getTSLL (read var52 var46))))) (and (and (and (not (= var40 nullAddr)) (and (and (and (and (and (and (= var52 var39) (= var50 var38)) (= var48 var37)) (= var46 var36)) (= var44 var35)) (= var42 var34)) (= var40 (|TSLL::next| (getTSLL (read var39 var36)))))) (and (and (and (and (and (and (= var33 (newHeap (alloc var32 (O_TSLL var31)))) (or (and var29 (= var30 (newAddr (alloc var32 (O_TSLL var31))))) (and (not var29) (= var30 var28)))) (= var27 var26)) (= var25 var24)) (= var23 var22)) (= var21 (newAddr (alloc var32 (O_TSLL var31))))) (and (and (and (and (and (= var20 (write var33 var21 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var33 var21))) 1)))) (= var19 var30)) (= var18 var27)) (= var17 var25)) (= var16 var23)) (= var15 var21)))) (and (and (and (and (and (= var39 (write var20 var15 (O_TSLL (TSLL nullAddr (|TSLL::data| (getTSLL (read var20 var15))))))) (= var38 var19)) (= var37 var18)) (= var36 var17)) (= var35 var16)) (= var34 var15)))) (and (and (and (and (and (= var14 (write var53 var43 (O_TSLL (TSLL var41 (|TSLL::data| (getTSLL (read var53 var43))))))) (= var13 var51)) (= var12 var49)) (= var11 var47)) (= var10 var45)) (= var9 var43))) (and (and (and (and (and (= var8 (write var14 var11 (O_TSLL (TSLL var9 (|TSLL::data| (getTSLL (read var14 var11))))))) (= var7 var13)) (= var6 var12)) (= var5 var11)) (= var4 var10)) (= var3 var9))) (and (= var2 0) (and (not (= var1 nullAddr)) (and (and (and (and (and (= var32 var58) (= var28 var57)) (= var26 var56)) (= var24 var55)) (= var22 var54)) (= var1 (|TSLL::next| (getTSLL (read var58 var55)))))))) (= var0 0)))) (inv_main_33 var8 var7 var6 var6 var0 var3))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main_52 var6 var5 var4 var3 var2 var1) (and (= var3 nullAddr) (= var0 0)))) (inv_main1075_9 var6 var5 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Int) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main_15 var10 var9 var8 var7 var6) (and (= var5 nullAddr) (and (and (and (and (and (= var4 var10) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var0 var6)) (= var5 (|TSLL::next| (getTSLL (read var10 var7)))))))) (inv_main_16 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Int) (var6 Int) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap) (var11 Int) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Heap) (var16 Addr) (var17 Int) (var18 Int) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Heap)) (or (not (and (inv_main_15 var22 var21 var20 var19 var18) (and (and (= var17 0) (and (and (not (= var16 nullAddr)) (and (and (and (and (and (= var15 var22) (= var14 var21)) (= var13 var20)) (= var12 var19)) (= var11 var18)) (= var16 (|TSLL::next| (getTSLL (read var22 var19)))))) (and (and (and (and (and (= var10 var15) (= var9 var14)) (= var8 var13)) (= var7 var12)) (= var6 var11)) (= var5 (|TSLL::data| (getTSLL (read var15 (|TSLL::next| (getTSLL (read var15 var12)))))))))) (and (and (and (and (and (= var4 var10) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var0 var6)) (or (and (= var5 0) (= var17 1)) (and (not (= var5 0)) (= var17 0))))))) (inv_main_16 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Int) (var9 Int) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Heap) (var17 Heap) (var18 Int) (var19 Int) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Heap)) (or (not (and (inv_main_16 var23 var22 var21 var20 var19) (and (and (= var18 1) (and (and (and (and (and (= var17 var16) (= var15 var14)) (= var13 var12)) (= var11 var10)) (= var9 var8)) (= var18 (|TSLL::data| (getTSLL (read var16 var10)))))) (and (and (and (and (and (and (= var16 var7) (= var14 var6)) (= var12 var5)) (= var4 var3)) (= var8 var2)) (= var10 (|TSLL::next| (getTSLL (read var7 var3))))) (and (not (= var1 0)) (and (not (= var0 nullAddr)) (and (and (and (and (and (= var7 var23) (= var6 var22)) (= var5 var21)) (= var3 var20)) (= var2 var19)) (= var0 (|TSLL::next| (getTSLL (read var23 var20))))))))))) (inv_main_16 var17 var15 var13 var11 var9))))
(assert (forall ((var0 Int) (var1 Heap) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Int) (var8 Addr) (var9 Int) (var10 Addr) (var11 Addr) (var12 Bool) (var13 Addr) (var14 TSLL) (var15 Heap) (var16 Addr) (var17 Int) (var18 Int) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Addr) (var25 Heap) (var26 Heap) (var27 Int) (var28 Int) (var29 Addr) (var30 Addr) (var31 Addr) (var32 Heap)) (or (not (and (inv_main1001_2 var32 var31 var30 var29 var28) (and (and (and (not (= var27 0)) (and (and (and (and (and (and (and (and (= var26 var25) (= var24 var23)) (= var22 var21)) (= var20 var19)) (= var18 var17)) (= var16 (|TSLL::next| (getTSLL (read var25 var19))))) (and (and (and (and (and (and (= var15 (newHeap (alloc var32 (O_TSLL var14)))) (or (and var12 (= var13 (newAddr (alloc var32 (O_TSLL var14))))) (and (not var12) (= var13 var31)))) (= var11 var30)) (= var10 var29)) (= var9 var28)) (= var8 (newAddr (alloc var32 (O_TSLL var14))))) (or (not (= var7 0)) (= var28 0)))) (and (and (and (and (= var25 (write var15 var10 (O_TSLL (TSLL var8 (|TSLL::data| (getTSLL (read var15 var10))))))) (= var23 var13)) (= var21 var11)) (= var19 var10)) (= var17 var9))) (and (and (and (and (= var6 (write var26 var16 (O_TSLL (TSLL nullAddr (|TSLL::data| (getTSLL (read var26 var16))))))) (= var5 var24)) (= var4 var22)) (= var3 var16)) (= var2 var18)))) (= var1 (write var6 var3 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var6 var3))) 1))))) (= var0 1)))) (inv_main1001_2 var1 var5 var4 var3 var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Int) (var6 Addr) (var7 Int) (var8 Addr) (var9 Addr) (var10 Bool) (var11 Addr) (var12 TSLL) (var13 Heap) (var14 Addr) (var15 Int) (var16 Int) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Heap) (var24 Heap) (var25 Int) (var26 Int) (var27 Int) (var28 Addr) (var29 Addr) (var30 Addr) (var31 Heap)) (or (not (and (inv_main1001_2 var31 var30 var29 var28 var27) (and (and (not (= var26 0)) (and (= var25 0) (and (and (and (and (and (and (and (and (= var24 var23) (= var22 var21)) (= var20 var19)) (= var18 var17)) (= var16 var15)) (= var14 (|TSLL::next| (getTSLL (read var23 var17))))) (and (and (and (and (and (and (= var13 (newHeap (alloc var31 (O_TSLL var12)))) (or (and var10 (= var11 (newAddr (alloc var31 (O_TSLL var12))))) (and (not var10) (= var11 var30)))) (= var9 var29)) (= var8 var28)) (= var7 var27)) (= var6 (newAddr (alloc var31 (O_TSLL var12))))) (or (not (= var5 0)) (= var27 0)))) (and (and (and (and (= var23 (write var13 var8 (O_TSLL (TSLL var6 (|TSLL::data| (getTSLL (read var13 var8))))))) (= var21 var11)) (= var19 var9)) (= var17 var8)) (= var15 var7))) (and (and (and (and (= var4 (write var24 var14 (O_TSLL (TSLL nullAddr (|TSLL::data| (getTSLL (read var24 var14))))))) (= var3 var22)) (= var2 var20)) (= var1 var14)) (= var26 var16))))) (= var0 (write var4 var1 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var4 var1))) 1))))))) (inv_main1001_2 var0 var3 var2 var1 var26))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Int) (var6 Addr) (var7 Int) (var8 Addr) (var9 Addr) (var10 Bool) (var11 Addr) (var12 TSLL) (var13 Heap) (var14 Addr) (var15 Int) (var16 Int) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Heap) (var24 Heap) (var25 Int) (var26 Int) (var27 Int) (var28 Addr) (var29 Addr) (var30 Addr) (var31 Heap)) (or (not (and (inv_main1001_2 var31 var30 var29 var28 var27) (and (and (= var26 0) (and (= var25 0) (and (and (and (and (and (and (and (and (= var24 var23) (= var22 var21)) (= var20 var19)) (= var18 var17)) (= var16 var15)) (= var14 (|TSLL::next| (getTSLL (read var23 var17))))) (and (and (and (and (and (and (= var13 (newHeap (alloc var31 (O_TSLL var12)))) (or (and var10 (= var11 (newAddr (alloc var31 (O_TSLL var12))))) (and (not var10) (= var11 var30)))) (= var9 var29)) (= var8 var28)) (= var7 var27)) (= var6 (newAddr (alloc var31 (O_TSLL var12))))) (or (not (= var5 0)) (= var27 0)))) (and (and (and (and (= var23 (write var13 var8 (O_TSLL (TSLL var6 (|TSLL::data| (getTSLL (read var13 var8))))))) (= var21 var11)) (= var19 var9)) (= var17 var8)) (= var15 var7))) (and (and (and (and (= var4 (write var24 var14 (O_TSLL (TSLL nullAddr (|TSLL::data| (getTSLL (read var24 var14))))))) (= var3 var22)) (= var2 var20)) (= var1 var14)) (= var26 var16))))) (= var0 (write var4 var1 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var4 var1))) 0))))))) (inv_main1001_2 var0 var3 var2 var1 var26))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Bool) (var9 Addr) (var10 TSLL) (var11 Heap) (var12 Addr) (var13 Heap)) (or (not (and (inv_main996_2 var13 var12) (and (and (and (and (and (= var11 (newHeap (alloc var13 (O_TSLL var10)))) (or (and var8 (= var9 (newAddr (alloc var13 (O_TSLL var10))))) (and (not var8) (= var9 var12)))) (= var7 (newAddr (alloc var13 (O_TSLL var10))))) (and (and (= var6 (write var11 var7 (O_TSLL (TSLL nullAddr (|TSLL::data| (getTSLL (read var11 var7))))))) (= var5 var9)) (= var4 var7))) (and (and (= var3 (write var6 var4 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var6 var4))) 0)))) (= var2 var5)) (= var1 var4))) (= var0 0)))) (inv_main1001_2 var3 var2 var1 var1 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main_34 var5 var4 var3 var2 var1 var0) (= var2 nullAddr))) (inv_main_52 var5 var4 var3 var3 var1 var0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Int) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap) (var9 Addr) (var10 Int) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Heap)) (or (not (and (inv_main_52 var14 var13 var12 var11 var10 var9) (and (and (and (and (and (and (and (and (and (= var8 var14) (= var7 var13)) (= var6 var11)) (= var5 var11)) (= var4 var10)) (= var3 var9)) (= var2 (|TSLL::next| (getTSLL (read var14 var11))))) (not (= var11 nullAddr))) (= var1 (write var8 var6 defObj))) (or (and (= var7 var6) (= var0 nullAddr)) (and (not (= var7 var6)) (= var0 var7)))))) (inv_main_52 var1 var0 var6 var2 var4 var3))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_exit var1 var0) (not (= var0 nullAddr))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap)) (not (and (inv_main1075_9 var2 var1 var0) (not (= var1 nullAddr))))))
(check-sat)
