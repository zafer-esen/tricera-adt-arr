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

(declare-datatypes ((HeapObject 0) (TSLL 0))
                   (((O_Int (getInt Int)) (O_UInt (getUInt Int)) (O_Addr (getAddr Addr)) (O_AddrRange (getAddrRange AddrRange)) (O_TSLL (getTSLL TSLL)) (defObj))
                   ((TSLL (|TSLL::next| Addr) (|TSLL::prev| Addr) (|TSLL::data| Int)))))
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
(declare-fun inv_main1002_2 (Heap Addr Addr Addr Int) Bool)
(declare-fun inv_main1048_9 (Heap Addr Int) Bool)
(declare-fun inv_main997_2 (Heap Addr) Bool)
(declare-fun inv_main_17 (Heap Addr Addr Addr Int) Bool)
(declare-fun inv_main_27 (Heap Addr Addr Addr Int) Bool)
(declare-fun inv_main_9 (Heap Addr Addr Addr Int) Bool)
(assert (forall ((var0 Addr) (var1 Heap)) (or (not (and (= var1 emptyHeap) (= var0 nullAddr))) (inv_main997_2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Int) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main_9 var9 var8 var7 var6 var5) (and (= nullAddr var4) (and (and (and (and (= var3 (write var9 var6 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var9 var6))) (|TSLL::prev| (getTSLL (read var9 var6))) var5)))) (= var2 var8)) (= var1 var7)) (= var4 var6)) (= var0 var5))))) (inv_exit var3 var2))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap) (var10 Heap) (var11 Int) (var12 Int) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Heap)) (or (not (and (inv_main_17 var16 var15 var14 var13 var12) (and (and (= var11 0) (and (and (and (and (and (= var10 var9) (= var8 var7)) (= var6 var5)) (= var4 var3)) (= var2 var1)) (= var11 (|TSLL::data| (getTSLL (read var9 (|TSLL::next| (getTSLL (read var9 var3))))))))) (and (not (= var0 0)) (and (and (and (and (and (= var9 var16) (= var7 var15)) (= var5 var14)) (= var3 var13)) (= var1 var12)) (= var0 (|TSLL::data| (getTSLL (read var16 var13))))))))) (inv_exit var10 var8))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Int) (var7 Int) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Heap) (var12 Int) (var13 Int) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Heap) (var21 Heap) (var22 Int) (var23 Int) (var24 Int) (var25 Addr) (var26 Addr) (var27 Addr) (var28 Heap)) (or (not (and (inv_main_17 var28 var27 var26 var25 var24) (and (and (= var23 0) (and (and (and (not (= var22 0)) (and (and (and (and (and (= var21 var20) (= var19 var18)) (= var17 var16)) (= var15 var14)) (= var13 var12)) (= var22 (|TSLL::data| (getTSLL (read var20 (|TSLL::next| (getTSLL (read var20 var14))))))))) (and (and (and (and (and (= var11 var21) (= var10 var19)) (= var9 var17)) (= var8 var15)) (= var7 var13)) (= var6 (|TSLL::data| (getTSLL (read var21 var15)))))) (and (and (and (and (and (= var5 var11) (= var4 var10)) (= var3 var9)) (= var2 var8)) (= var1 var7)) (or (and (<= 0 (+ (+ var6 (* (- 1) (|TSLL::data| (getTSLL (read var11 (|TSLL::next| (getTSLL (read var11 var8)))))))) (- 1))) (= var23 1)) (and (not (<= 0 (+ (+ var6 (* (- 1) (|TSLL::data| (getTSLL (read var11 (|TSLL::next| (getTSLL (read var11 var8)))))))) (- 1)))) (= var23 0)))))) (and (not (= var0 0)) (and (and (and (and (and (= var20 var28) (= var18 var27)) (= var16 var26)) (= var14 var25)) (= var12 var24)) (= var0 (|TSLL::data| (getTSLL (read var28 var25))))))))) (inv_exit var5 var4))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap) (var10 Heap) (var11 Addr) (var12 Int) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Heap)) (or (not (and (inv_main1002_2 var16 var15 var14 var13 var12) (and (and (= nullAddr var11) (and (and (and (and (and (and (= var10 var9) (= var8 var7)) (= var6 var5)) (= var4 var3)) (= var2 var1)) (= var11 (|TSLL::next| (getTSLL (read var9 var5))))) (and (and (and (and (= var9 (write var16 var13 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var16 var13))) (|TSLL::prev| (getTSLL (read var16 var13))) var12)))) (= var7 var15)) (= var5 var14)) (= var3 var13)) (= var1 var12)))) (= var0 0)))) (inv_exit var10 var8))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Int) (var6 Addr) (var7 Int) (var8 Addr) (var9 Addr) (var10 Bool) (var11 Addr) (var12 TSLL) (var13 Heap) (var14 Addr) (var15 Int) (var16 Int) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Heap) (var24 Heap) (var25 Int) (var26 Addr) (var27 Addr) (var28 Int) (var29 Addr) (var30 Heap) (var31 Int) (var32 Int) (var33 Addr) (var34 Addr) (var35 Addr) (var36 Addr) (var37 Addr) (var38 Addr) (var39 Heap) (var40 Heap) (var41 Addr) (var42 Int) (var43 Addr) (var44 Addr) (var45 Addr) (var46 Heap)) (or (not (and (inv_main1002_2 var46 var45 var44 var43 var42) (and (and (= nullAddr var41) (and (and (and (and (and (and (= var40 var39) (= var38 var37)) (= var36 var35)) (= var34 var33)) (= var32 var31)) (= var41 (|TSLL::next| (getTSLL (read var39 var35))))) (and (and (and (and (= var39 (write var30 var29 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var30 var29))) (|TSLL::prev| (getTSLL (read var30 var29))) var28)))) (= var37 var27)) (= var35 var26)) (= var33 var29)) (= var31 var28)))) (and (not (= var28 2)) (and (not (= var28 1)) (and (not (= var25 0)) (and (and (and (and (and (and (and (and (= var24 var23) (= var22 var21)) (= var20 var19)) (= var18 var17)) (= var16 var15)) (= var14 (|TSLL::next| (getTSLL (read var23 var17))))) (and (and (and (and (and (and (and (= var13 (newHeap (alloc var46 (O_TSLL var12)))) (or (and var10 (= var11 (newAddr (alloc var46 (O_TSLL var12))))) (and (not var10) (= var11 var45)))) (= var9 var44)) (= var8 var43)) (= var7 var42)) (= var6 (newAddr (alloc var46 (O_TSLL var12))))) (not (= var5 0))) (and (and (and (and (= var4 (write var13 var8 (O_TSLL (TSLL var6 (|TSLL::prev| (getTSLL (read var13 var8))) (|TSLL::data| (getTSLL (read var13 var8))))))) (= var3 var11)) (= var2 var9)) (= var1 var8)) (= var0 var7)))) (and (and (and (and (= var23 (write var4 (|TSLL::next| (getTSLL (read var4 var1))) (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var4 (|TSLL::next| (getTSLL (read var4 var1)))))) var1 (|TSLL::data| (getTSLL (read var4 (|TSLL::next| (getTSLL (read var4 var1)))))))))) (= var21 var3)) (= var19 var2)) (= var17 var1)) (= var15 var0))) (and (and (and (and (= var30 (write var24 var14 (O_TSLL (TSLL var20 (|TSLL::prev| (getTSLL (read var24 var14))) (|TSLL::data| (getTSLL (read var24 var14))))))) (= var27 var22)) (= var26 var20)) (= var29 var14)) (= var28 var16))))))))) (inv_exit var40 var38))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Int) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main_9 var9 var8 var7 var6 var5) (and (not (= nullAddr var4)) (and (and (and (and (= var3 (write var9 var6 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var9 var6))) (|TSLL::prev| (getTSLL (read var9 var6))) var5)))) (= var2 var8)) (= var1 var7)) (= var4 var6)) (= var0 var5))))) (inv_main1002_2 var3 var2 var1 var4 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Bool) (var9 Addr) (var10 TSLL) (var11 Heap) (var12 Addr) (var13 Heap)) (or (not (and (inv_main997_2 var13 var12) (and (and (and (and (and (= var11 (newHeap (alloc var13 (O_TSLL var10)))) (or (and var8 (= var9 (newAddr (alloc var13 (O_TSLL var10))))) (and (not var8) (= var9 var12)))) (= var7 (newAddr (alloc var13 (O_TSLL var10))))) (and (and (= var6 (write var11 var7 (O_TSLL (TSLL var7 (|TSLL::prev| (getTSLL (read var11 var7))) (|TSLL::data| (getTSLL (read var11 var7))))))) (= var5 var9)) (= var4 var7))) (and (and (= var3 (write var6 var4 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var6 var4))) (|TSLL::prev| (getTSLL (read var6 var4))) 0)))) (= var2 var5)) (= var1 var4))) (= var0 1)))) (inv_main1002_2 var3 var2 var1 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap) (var11 Heap) (var12 Int) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Heap)) (or (not (and (inv_main_17 var16 var15 var14 var13 var12) (and (and (and (and (and (and (= var11 var10) (= var9 var8)) (= var7 var6)) (= var5 var4)) (= var3 var2)) (= var1 (|TSLL::next| (getTSLL (read var10 var6))))) (and (= var0 0) (and (and (and (and (and (= var10 var16) (= var8 var15)) (= var6 var14)) (= var4 var13)) (= var2 var12)) (= var0 (|TSLL::data| (getTSLL (read var16 var13))))))))) (inv_main_27 var11 var9 var7 var1 var3))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Int) (var4 Addr) (var5 Int) (var6 Int) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Heap) (var13 Heap) (var14 Int) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Heap)) (or (not (and (inv_main_27 var18 var17 var16 var15 var14) (and (and (and (and (and (and (and (and (= var13 var12) (= var11 var10)) (= var9 var8)) (= var7 var8)) (= var6 var5)) (= var4 (|TSLL::next| (getTSLL (read var12 var8))))) (and (not (= var3 0)) (and (and (and (and (and (= var12 var18) (= var10 var17)) (= var2 var16)) (= var8 var15)) (= var5 var14)) (= var3 (|TSLL::data| (getTSLL (read var18 var15))))))) (= var1 (write var13 var9 defObj))) (or (and (= var11 var9) (= var0 nullAddr)) (and (not (= var11 var9)) (= var0 var11)))))) (inv_main_27 var1 var0 var9 var4 var6))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Int) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap) (var10 Int) (var11 Addr) (var12 Int) (var13 Addr) (var14 Addr) (var15 Bool) (var16 Addr) (var17 TSLL) (var18 Heap) (var19 Addr) (var20 Int) (var21 Int) (var22 Addr) (var23 Addr) (var24 Addr) (var25 Addr) (var26 Addr) (var27 Addr) (var28 Heap) (var29 Heap) (var30 Int) (var31 Int) (var32 Addr) (var33 Addr) (var34 Addr) (var35 Heap)) (or (not (and (inv_main1002_2 var35 var34 var33 var32 var31) (and (= var30 0) (and (and (and (and (and (and (and (and (= var29 var28) (= var27 var26)) (= var25 var24)) (= var23 var22)) (= var21 var20)) (= var19 (|TSLL::next| (getTSLL (read var28 var22))))) (and (and (and (and (and (and (and (= var18 (newHeap (alloc var35 (O_TSLL var17)))) (or (and var15 (= var16 (newAddr (alloc var35 (O_TSLL var17))))) (and (not var15) (= var16 var34)))) (= var14 var33)) (= var13 var32)) (= var12 var31)) (= var11 (newAddr (alloc var35 (O_TSLL var17))))) (not (= var10 0))) (and (and (and (and (= var9 (write var18 var13 (O_TSLL (TSLL var11 (|TSLL::prev| (getTSLL (read var18 var13))) (|TSLL::data| (getTSLL (read var18 var13))))))) (= var8 var16)) (= var7 var14)) (= var6 var13)) (= var5 var12)))) (and (and (and (and (= var28 (write var9 (|TSLL::next| (getTSLL (read var9 var6))) (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var9 (|TSLL::next| (getTSLL (read var9 var6)))))) var6 (|TSLL::data| (getTSLL (read var9 (|TSLL::next| (getTSLL (read var9 var6)))))))))) (= var26 var8)) (= var24 var7)) (= var22 var6)) (= var20 var5))) (and (and (and (and (= var4 (write var29 var19 (O_TSLL (TSLL var25 (|TSLL::prev| (getTSLL (read var29 var19))) (|TSLL::data| (getTSLL (read var29 var19))))))) (= var3 var27)) (= var2 var25)) (= var1 var19)) (= var0 var21)))))) (inv_main_9 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Int) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap) (var10 Int) (var11 Addr) (var12 Int) (var13 Addr) (var14 Addr) (var15 Bool) (var16 Addr) (var17 TSLL) (var18 Heap) (var19 Addr) (var20 Int) (var21 Int) (var22 Addr) (var23 Addr) (var24 Addr) (var25 Addr) (var26 Addr) (var27 Addr) (var28 Heap) (var29 Heap) (var30 Int) (var31 Int) (var32 Int) (var33 Addr) (var34 Addr) (var35 Addr) (var36 Heap)) (or (not (and (inv_main1002_2 var36 var35 var34 var33 var32) (and (and (= var31 1) (and (not (= var30 0)) (and (and (and (and (and (and (and (and (= var29 var28) (= var27 var26)) (= var25 var24)) (= var23 var22)) (= var21 var20)) (= var19 (|TSLL::next| (getTSLL (read var28 var22))))) (and (and (and (and (and (and (and (= var18 (newHeap (alloc var36 (O_TSLL var17)))) (or (and var15 (= var16 (newAddr (alloc var36 (O_TSLL var17))))) (and (not var15) (= var16 var35)))) (= var14 var34)) (= var13 var33)) (= var12 var32)) (= var11 (newAddr (alloc var36 (O_TSLL var17))))) (not (= var10 0))) (and (and (and (and (= var9 (write var18 var13 (O_TSLL (TSLL var11 (|TSLL::prev| (getTSLL (read var18 var13))) (|TSLL::data| (getTSLL (read var18 var13))))))) (= var8 var16)) (= var7 var14)) (= var6 var13)) (= var5 var12)))) (and (and (and (and (= var28 (write var9 (|TSLL::next| (getTSLL (read var9 var6))) (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var9 (|TSLL::next| (getTSLL (read var9 var6)))))) var6 (|TSLL::data| (getTSLL (read var9 (|TSLL::next| (getTSLL (read var9 var6)))))))))) (= var26 var8)) (= var24 var7)) (= var22 var6)) (= var20 var5))) (and (and (and (and (= var4 (write var29 var19 (O_TSLL (TSLL var25 (|TSLL::prev| (getTSLL (read var29 var19))) (|TSLL::data| (getTSLL (read var29 var19))))))) (= var3 var27)) (= var2 var25)) (= var1 var19)) (= var31 var21))))) (= var0 2)))) (inv_main_9 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Int) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap) (var10 Int) (var11 Addr) (var12 Int) (var13 Addr) (var14 Addr) (var15 Bool) (var16 Addr) (var17 TSLL) (var18 Heap) (var19 Addr) (var20 Int) (var21 Int) (var22 Addr) (var23 Addr) (var24 Addr) (var25 Addr) (var26 Addr) (var27 Addr) (var28 Heap) (var29 Heap) (var30 Int) (var31 Int) (var32 Int) (var33 Addr) (var34 Addr) (var35 Addr) (var36 Heap)) (or (not (and (inv_main1002_2 var36 var35 var34 var33 var32) (and (and (= var31 2) (and (not (= var31 1)) (and (not (= var30 0)) (and (and (and (and (and (and (and (and (= var29 var28) (= var27 var26)) (= var25 var24)) (= var23 var22)) (= var21 var20)) (= var19 (|TSLL::next| (getTSLL (read var28 var22))))) (and (and (and (and (and (and (and (= var18 (newHeap (alloc var36 (O_TSLL var17)))) (or (and var15 (= var16 (newAddr (alloc var36 (O_TSLL var17))))) (and (not var15) (= var16 var35)))) (= var14 var34)) (= var13 var33)) (= var12 var32)) (= var11 (newAddr (alloc var36 (O_TSLL var17))))) (not (= var10 0))) (and (and (and (and (= var9 (write var18 var13 (O_TSLL (TSLL var11 (|TSLL::prev| (getTSLL (read var18 var13))) (|TSLL::data| (getTSLL (read var18 var13))))))) (= var8 var16)) (= var7 var14)) (= var6 var13)) (= var5 var12)))) (and (and (and (and (= var28 (write var9 (|TSLL::next| (getTSLL (read var9 var6))) (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var9 (|TSLL::next| (getTSLL (read var9 var6)))))) var6 (|TSLL::data| (getTSLL (read var9 (|TSLL::next| (getTSLL (read var9 var6)))))))))) (= var26 var8)) (= var24 var7)) (= var22 var6)) (= var20 var5))) (and (and (and (and (= var4 (write var29 var19 (O_TSLL (TSLL var25 (|TSLL::prev| (getTSLL (read var29 var19))) (|TSLL::data| (getTSLL (read var29 var19))))))) (= var3 var27)) (= var2 var25)) (= var1 var19)) (= var31 var21)))))) (= var0 3)))) (inv_main_9 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Int) (var8 Int) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Heap) (var16 Heap) (var17 Int) (var18 Int) (var19 Addr) (var20 Int) (var21 Int) (var22 Addr) (var23 Addr) (var24 Addr) (var25 Addr) (var26 Addr) (var27 Addr) (var28 Heap) (var29 Heap) (var30 Int) (var31 Addr) (var32 Addr) (var33 Addr) (var34 Heap)) (or (not (and (inv_main_17 var34 var33 var32 var31 var30) (and (and (and (and (and (and (= var29 var28) (= var27 var26)) (= var25 var24)) (= var23 var22)) (= var21 var20)) (= var19 (|TSLL::next| (getTSLL (read var28 var22))))) (and (and (not (= var18 0)) (and (and (and (not (= var17 0)) (and (and (and (and (and (= var16 var15) (= var14 var13)) (= var12 var11)) (= var10 var9)) (= var8 var7)) (= var17 (|TSLL::data| (getTSLL (read var15 (|TSLL::next| (getTSLL (read var15 var9))))))))) (and (and (and (and (and (= var6 var16) (= var5 var14)) (= var4 var12)) (= var3 var10)) (= var2 var8)) (= var1 (|TSLL::data| (getTSLL (read var16 var10)))))) (and (and (and (and (and (= var28 var6) (= var26 var5)) (= var24 var4)) (= var22 var3)) (= var20 var2)) (or (and (<= 0 (+ (+ var1 (* (- 1) (|TSLL::data| (getTSLL (read var6 (|TSLL::next| (getTSLL (read var6 var3)))))))) (- 1))) (= var18 1)) (and (not (<= 0 (+ (+ var1 (* (- 1) (|TSLL::data| (getTSLL (read var6 (|TSLL::next| (getTSLL (read var6 var3)))))))) (- 1)))) (= var18 0)))))) (and (not (= var0 0)) (and (and (and (and (and (= var15 var34) (= var13 var33)) (= var11 var32)) (= var9 var31)) (= var7 var30)) (= var0 (|TSLL::data| (getTSLL (read var34 var31)))))))))) (inv_main_17 var29 var27 var25 var19 var21))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap) (var10 Heap) (var11 Addr) (var12 Int) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Heap)) (or (not (and (inv_main1002_2 var16 var15 var14 var13 var12) (and (and (not (= nullAddr var11)) (and (and (and (and (and (and (= var10 var9) (= var8 var7)) (= var6 var5)) (= var4 var3)) (= var2 var1)) (= var11 (|TSLL::next| (getTSLL (read var9 var5))))) (and (and (and (and (= var9 (write var16 var13 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var16 var13))) (|TSLL::prev| (getTSLL (read var16 var13))) var12)))) (= var7 var15)) (= var5 var14)) (= var3 var13)) (= var1 var12)))) (= var0 0)))) (inv_main_17 var10 var8 var6 var11 var2))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Int) (var6 Addr) (var7 Int) (var8 Addr) (var9 Addr) (var10 Bool) (var11 Addr) (var12 TSLL) (var13 Heap) (var14 Addr) (var15 Int) (var16 Int) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Heap) (var24 Heap) (var25 Int) (var26 Addr) (var27 Addr) (var28 Int) (var29 Addr) (var30 Heap) (var31 Int) (var32 Int) (var33 Addr) (var34 Addr) (var35 Addr) (var36 Addr) (var37 Addr) (var38 Addr) (var39 Heap) (var40 Heap) (var41 Addr) (var42 Int) (var43 Addr) (var44 Addr) (var45 Addr) (var46 Heap)) (or (not (and (inv_main1002_2 var46 var45 var44 var43 var42) (and (and (not (= nullAddr var41)) (and (and (and (and (and (and (= var40 var39) (= var38 var37)) (= var36 var35)) (= var34 var33)) (= var32 var31)) (= var41 (|TSLL::next| (getTSLL (read var39 var35))))) (and (and (and (and (= var39 (write var30 var29 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var30 var29))) (|TSLL::prev| (getTSLL (read var30 var29))) var28)))) (= var37 var27)) (= var35 var26)) (= var33 var29)) (= var31 var28)))) (and (not (= var28 2)) (and (not (= var28 1)) (and (not (= var25 0)) (and (and (and (and (and (and (and (and (= var24 var23) (= var22 var21)) (= var20 var19)) (= var18 var17)) (= var16 var15)) (= var14 (|TSLL::next| (getTSLL (read var23 var17))))) (and (and (and (and (and (and (and (= var13 (newHeap (alloc var46 (O_TSLL var12)))) (or (and var10 (= var11 (newAddr (alloc var46 (O_TSLL var12))))) (and (not var10) (= var11 var45)))) (= var9 var44)) (= var8 var43)) (= var7 var42)) (= var6 (newAddr (alloc var46 (O_TSLL var12))))) (not (= var5 0))) (and (and (and (and (= var4 (write var13 var8 (O_TSLL (TSLL var6 (|TSLL::prev| (getTSLL (read var13 var8))) (|TSLL::data| (getTSLL (read var13 var8))))))) (= var3 var11)) (= var2 var9)) (= var1 var8)) (= var0 var7)))) (and (and (and (and (= var23 (write var4 (|TSLL::next| (getTSLL (read var4 var1))) (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var4 (|TSLL::next| (getTSLL (read var4 var1)))))) var1 (|TSLL::data| (getTSLL (read var4 (|TSLL::next| (getTSLL (read var4 var1)))))))))) (= var21 var3)) (= var19 var2)) (= var17 var1)) (= var15 var0))) (and (and (and (and (= var30 (write var24 var14 (O_TSLL (TSLL var20 (|TSLL::prev| (getTSLL (read var24 var14))) (|TSLL::data| (getTSLL (read var24 var14))))))) (= var27 var22)) (= var26 var20)) (= var29 var14)) (= var28 var16))))))))) (inv_main_17 var40 var38 var36 var41 var32))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Int) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap) (var11 Int) (var12 Int) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Heap)) (or (not (and (inv_main_27 var16 var15 var14 var13 var12) (and (and (and (= var11 0) (and (and (and (and (and (= var10 var16) (= var9 var15)) (= var8 var14)) (= var7 var13)) (= var6 var12)) (= var11 (|TSLL::data| (getTSLL (read var16 var13)))))) (and (and (and (and (= var5 (write var10 var7 defObj)) (or (and (= var9 var7) (= var4 nullAddr)) (and (not (= var9 var7)) (= var4 var9)))) (= var3 var8)) (= var2 var7)) (= var1 var6))) (= var0 0)))) (inv_main1048_9 var5 var4 var0))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_exit var1 var0) (not (= var0 nullAddr))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap)) (not (and (inv_main1048_9 var2 var1 var0) (not (= var1 nullAddr))))))
(check-sat)
