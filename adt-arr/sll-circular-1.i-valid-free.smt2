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
(declare-fun inv_main1001_2 (Heap Addr Addr Int) Bool)
(declare-fun inv_main996_2 (Heap) Bool)
(declare-fun inv_main_16 (Heap Addr Addr Int) Bool)
(declare-fun inv_main_27 (Heap Addr Addr Int) Bool)
(declare-fun inv_main_30 (Heap Addr Addr Int) Bool)
(assert (forall ((var0 Heap)) (or (not (= var0 emptyHeap)) (inv_main996_2 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Int) (var6 Addr) (var7 Int) (var8 Int) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Heap) (var13 Heap) (var14 Int) (var15 Addr) (var16 Addr) (var17 Heap)) (or (not (and (inv_main_30 var17 var16 var15 var14) (and (and (and (and (and (and (= var13 var12) (= var11 var10)) (= var9 var10)) (= var8 var7)) (= var6 (|TSLL::next| (getTSLL (read var12 var10))))) (and (not (= var5 0)) (and (and (and (and (= var12 var4) (= var3 var2)) (= var10 var1)) (= var7 var0)) (= var5 (|TSLL::data| (getTSLL (read var4 var1))))))) (and (and (and (= var4 (write var17 var16 defObj)) (= var2 var16)) (= var1 var15)) (= var0 var14))))) (inv_main_30 var13 var11 var6 var8))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Int) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap) (var11 Int) (var12 Addr) (var13 Int) (var14 Int) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Heap) (var19 Heap) (var20 Int) (var21 Addr) (var22 Addr) (var23 Heap)) (or (not (and (inv_main_16 var23 var22 var21 var20) (and (and (and (and (and (and (= var19 var18) (= var17 var16)) (= var15 var16)) (= var14 var13)) (= var12 (|TSLL::next| (getTSLL (read var18 var16))))) (and (not (= var11 0)) (and (and (and (and (= var18 var10) (= var9 var8)) (= var16 var7)) (= var13 var6)) (= var11 (|TSLL::data| (getTSLL (read var10 var7))))))) (and (and (and (and (and (= var10 var5) (= var8 var4)) (= var3 var2)) (= var6 var1)) (= var7 (|TSLL::next| (getTSLL (read var5 var4))))) (and (= var0 0) (and (and (and (and (= var5 var23) (= var4 var22)) (= var2 var21)) (= var1 var20)) (= var0 (|TSLL::data| (getTSLL (read var23 var21)))))))))) (inv_main_30 var19 var17 var12 var14))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Heap) (var8 Int) (var9 Int) (var10 Addr) (var11 Addr) (var12 Heap)) (or (not (and (inv_main_30 var12 var11 var10 var9) (and (and (= var8 0) (and (and (and (and (= var7 var6) (= var5 var4)) (= var3 var2)) (= var1 var0)) (= var8 (|TSLL::data| (getTSLL (read var6 var2)))))) (and (and (and (= var6 (write var12 var11 defObj)) (= var4 var11)) (= var2 var10)) (= var0 var9))))) (inv_main_27 var7 var5 var3 var1))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Int) (var7 Int) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Heap) (var13 Heap) (var14 Int) (var15 Int) (var16 Addr) (var17 Addr) (var18 Heap)) (or (not (and (inv_main_16 var18 var17 var16 var15) (and (and (= var14 0) (and (and (and (and (= var13 var12) (= var11 var10)) (= var9 var8)) (= var7 var6)) (= var14 (|TSLL::data| (getTSLL (read var12 var8)))))) (and (and (and (and (and (= var12 var5) (= var10 var4)) (= var3 var2)) (= var6 var1)) (= var8 (|TSLL::next| (getTSLL (read var5 var4))))) (and (= var0 0) (and (and (and (and (= var5 var18) (= var4 var17)) (= var2 var16)) (= var1 var15)) (= var0 (|TSLL::data| (getTSLL (read var18 var16)))))))))) (inv_main_27 var13 var11 var9 var7))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Int) (var6 Addr) (var7 Int) (var8 Int) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Heap) (var14 Heap) (var15 Int) (var16 Addr) (var17 Addr) (var18 Heap)) (or (not (and (inv_main_16 var18 var17 var16 var15) (and (and (and (and (and (= var14 var13) (= var12 var11)) (= var10 var9)) (= var8 var7)) (= var6 (|TSLL::next| (getTSLL (read var13 var9))))) (and (and (= var5 0) (and (and (and (and (= var13 var4) (= var11 var3)) (= var9 var2)) (= var7 var1)) (= var5 (|TSLL::data| (getTSLL (read var4 (|TSLL::next| (getTSLL (read var4 var2))))))))) (and (not (= var0 0)) (and (and (and (and (= var4 var18) (= var3 var17)) (= var2 var16)) (= var1 var15)) (= var0 (|TSLL::data| (getTSLL (read var18 var16)))))))))) (inv_main_16 var14 var12 var6 var8))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Int) (var7 Int) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Heap) (var13 Heap) (var14 Int) (var15 Int) (var16 Addr) (var17 Int) (var18 Int) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Heap) (var24 Heap) (var25 Int) (var26 Addr) (var27 Addr) (var28 Heap)) (or (not (and (inv_main_16 var28 var27 var26 var25) (and (and (and (and (and (= var24 var23) (= var22 var21)) (= var20 var19)) (= var18 var17)) (= var16 (|TSLL::next| (getTSLL (read var23 var19))))) (and (and (not (= var15 0)) (and (and (and (not (= var14 0)) (and (and (and (and (= var13 var12) (= var11 var10)) (= var9 var8)) (= var7 var6)) (= var14 (|TSLL::data| (getTSLL (read var12 (|TSLL::next| (getTSLL (read var12 var8))))))))) (and (and (and (and (= var5 var13) (= var4 var11)) (= var3 var9)) (= var2 var7)) (= var1 (|TSLL::data| (getTSLL (read var13 var9)))))) (and (and (and (and (= var23 var5) (= var21 var4)) (= var19 var3)) (= var17 var2)) (or (and (<= 0 (+ (|TSLL::data| (getTSLL (read var5 (|TSLL::next| (getTSLL (read var5 var3)))))) (* (- 1) var1))) (= var15 1)) (and (not (<= 0 (+ (|TSLL::data| (getTSLL (read var5 (|TSLL::next| (getTSLL (read var5 var3)))))) (* (- 1) var1)))) (= var15 0)))))) (and (not (= var0 0)) (and (and (and (and (= var12 var28) (= var10 var27)) (= var8 var26)) (= var6 var25)) (= var0 (|TSLL::data| (getTSLL (read var28 var26)))))))))) (inv_main_16 var24 var22 var16 var18))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Heap) (var9 Addr) (var10 Int) (var11 Addr) (var12 Addr) (var13 Heap)) (or (not (and (inv_main1001_2 var13 var12 var11 var10) (and (and (not (= nullAddr var9)) (and (and (and (and (and (= var8 var7) (= var6 var5)) (= var4 var3)) (= var2 var1)) (= var9 (|TSLL::next| (getTSLL (read var7 var5))))) (and (and (and (= var7 (write var13 var11 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var13 var11))) var10)))) (= var5 var12)) (= var3 var11)) (= var1 var10)))) (= var0 0)))) (inv_main_16 var8 var6 var9 var2))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 TSLL) (var6 Heap) (var7 Addr) (var8 Int) (var9 Int) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Heap) (var15 Heap) (var16 Int) (var17 Addr) (var18 Int) (var19 Addr) (var20 Heap) (var21 Int) (var22 Int) (var23 Addr) (var24 Addr) (var25 Addr) (var26 Addr) (var27 Heap) (var28 Heap) (var29 Addr) (var30 Int) (var31 Addr) (var32 Addr) (var33 Heap)) (or (not (and (inv_main1001_2 var33 var32 var31 var30) (and (and (not (= nullAddr var29)) (and (and (and (and (and (= var28 var27) (= var26 var25)) (= var24 var23)) (= var22 var21)) (= var29 (|TSLL::next| (getTSLL (read var27 var25))))) (and (and (and (= var27 (write var20 var19 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var20 var19))) var18)))) (= var25 var17)) (= var23 var19)) (= var21 var18)))) (and (not (= var18 2)) (and (not (= var18 1)) (and (not (= var16 0)) (and (and (and (and (and (and (and (= var15 var14) (= var13 var12)) (= var11 var10)) (= var9 var8)) (= var7 (|TSLL::next| (getTSLL (read var14 var10))))) (and (and (and (and (and (= var6 (newHeap (alloc var33 (O_TSLL var5)))) (= var4 var32)) (= var3 var31)) (= var2 var30)) (= var1 (newAddr (alloc var33 (O_TSLL var5))))) (not (= var0 0)))) (and (and (and (= var14 (write var6 var3 (O_TSLL (TSLL var1 (|TSLL::data| (getTSLL (read var6 var3))))))) (= var12 var4)) (= var10 var3)) (= var8 var2))) (and (and (and (= var20 (write var15 var7 (O_TSLL (TSLL var13 (|TSLL::data| (getTSLL (read var15 var7))))))) (= var17 var13)) (= var19 var7)) (= var18 var9))))))))) (inv_main_16 var28 var26 var29 var22))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Heap) (var5 Addr) (var6 TSLL) (var7 Heap) (var8 Heap)) (or (not (and (inv_main996_2 var8) (and (and (and (and (= var7 (newHeap (alloc var8 (O_TSLL var6)))) (= var5 (newAddr (alloc var8 (O_TSLL var6))))) (and (= var4 (write var7 var5 (O_TSLL (TSLL var5 (|TSLL::data| (getTSLL (read var7 var5))))))) (= var3 var5))) (and (= var2 (write var4 var3 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var4 var3))) 0)))) (= var1 var3))) (= var0 1)))) (inv_main1001_2 var2 var1 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 TSLL) (var6 Heap) (var7 Addr) (var8 Int) (var9 Int) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Heap) (var15 Heap) (var16 Int) (var17 Int) (var18 Addr) (var19 Addr) (var20 Int) (var21 Addr) (var22 Heap) (var23 Heap) (var24 Addr) (var25 Int) (var26 Addr) (var27 Addr) (var28 Heap)) (or (not (and (inv_main1001_2 var28 var27 var26 var25) (and (and (not (= nullAddr var24)) (and (and (and (= var23 (write var22 var21 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var22 var21))) var20)))) (= var19 var18)) (= var24 var21)) (= var17 var20))) (and (= var16 0) (and (and (and (and (and (and (and (= var15 var14) (= var13 var12)) (= var11 var10)) (= var9 var8)) (= var7 (|TSLL::next| (getTSLL (read var14 var10))))) (and (and (and (and (and (= var6 (newHeap (alloc var28 (O_TSLL var5)))) (= var4 var27)) (= var3 var26)) (= var2 var25)) (= var1 (newAddr (alloc var28 (O_TSLL var5))))) (not (= var0 0)))) (and (and (and (= var14 (write var6 var3 (O_TSLL (TSLL var1 (|TSLL::data| (getTSLL (read var6 var3))))))) (= var12 var4)) (= var10 var3)) (= var8 var2))) (and (and (and (= var22 (write var15 var7 (O_TSLL (TSLL var13 (|TSLL::data| (getTSLL (read var15 var7))))))) (= var18 var13)) (= var21 var7)) (= var20 var9))))))) (inv_main1001_2 var23 var19 var24 var17))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 TSLL) (var6 Heap) (var7 Addr) (var8 Int) (var9 Int) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Heap) (var15 Heap) (var16 Int) (var17 Int) (var18 Int) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Heap) (var23 Heap) (var24 Addr) (var25 Int) (var26 Addr) (var27 Addr) (var28 Heap)) (or (not (and (inv_main1001_2 var28 var27 var26 var25) (and (and (not (= nullAddr var24)) (and (and (and (= var23 (write var22 var21 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var22 var21))) 2)))) (= var20 var19)) (= var24 var21)) (= var18 2))) (and (= var17 1) (and (not (= var16 0)) (and (and (and (and (and (and (and (= var15 var14) (= var13 var12)) (= var11 var10)) (= var9 var8)) (= var7 (|TSLL::next| (getTSLL (read var14 var10))))) (and (and (and (and (and (= var6 (newHeap (alloc var28 (O_TSLL var5)))) (= var4 var27)) (= var3 var26)) (= var2 var25)) (= var1 (newAddr (alloc var28 (O_TSLL var5))))) (not (= var0 0)))) (and (and (and (= var14 (write var6 var3 (O_TSLL (TSLL var1 (|TSLL::data| (getTSLL (read var6 var3))))))) (= var12 var4)) (= var10 var3)) (= var8 var2))) (and (and (and (= var22 (write var15 var7 (O_TSLL (TSLL var13 (|TSLL::data| (getTSLL (read var15 var7))))))) (= var19 var13)) (= var21 var7)) (= var17 var9)))))))) (inv_main1001_2 var23 var20 var24 var18))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 TSLL) (var6 Heap) (var7 Addr) (var8 Int) (var9 Int) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Heap) (var15 Heap) (var16 Int) (var17 Int) (var18 Int) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Heap) (var23 Heap) (var24 Addr) (var25 Int) (var26 Addr) (var27 Addr) (var28 Heap)) (or (not (and (inv_main1001_2 var28 var27 var26 var25) (and (and (not (= nullAddr var24)) (and (and (and (= var23 (write var22 var21 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var22 var21))) 3)))) (= var20 var19)) (= var24 var21)) (= var18 3))) (and (= var17 2) (and (not (= var17 1)) (and (not (= var16 0)) (and (and (and (and (and (and (and (= var15 var14) (= var13 var12)) (= var11 var10)) (= var9 var8)) (= var7 (|TSLL::next| (getTSLL (read var14 var10))))) (and (and (and (and (and (= var6 (newHeap (alloc var28 (O_TSLL var5)))) (= var4 var27)) (= var3 var26)) (= var2 var25)) (= var1 (newAddr (alloc var28 (O_TSLL var5))))) (not (= var0 0)))) (and (and (and (= var14 (write var6 var3 (O_TSLL (TSLL var1 (|TSLL::data| (getTSLL (read var6 var3))))))) (= var12 var4)) (= var10 var3)) (= var8 var2))) (and (and (and (= var22 (write var15 var7 (O_TSLL (TSLL var13 (|TSLL::data| (getTSLL (read var15 var7))))))) (= var19 var13)) (= var21 var7)) (= var17 var9))))))))) (inv_main1001_2 var23 var20 var24 var18))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_30 var3 var2 var1 var0) (and (not (= var2 nullAddr)) (= (read var3 var2) defObj))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_27 var3 var2 var1 var0) (and (not (= var1 nullAddr)) (= (read var3 var1) defObj))))))
(check-sat)
