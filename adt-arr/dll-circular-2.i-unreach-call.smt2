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
(declare-fun inv_main1003_2 (Heap Addr Addr Int) Bool)
(declare-fun inv_main1026_12 (Heap Addr Addr Int) Bool)
(declare-fun inv_main1031_11 (Heap Addr Addr Int) Bool)
(declare-fun inv_main1035_12 (Heap Addr Addr Int) Bool)
(declare-fun inv_main997_2 (Heap) Bool)
(declare-fun inv_main_10 (Heap Addr Addr Int) Bool)
(declare-fun inv_main_18 (Heap Addr Addr Int) Bool)
(declare-fun inv_main_28 (Heap Addr Addr Int) Bool)
(assert (forall ((var0 Heap)) (or (not (= var0 emptyHeap)) (inv_main997_2 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Heap) (var9 Addr) (var10 Int) (var11 Addr) (var12 Addr) (var13 Heap)) (or (not (and (inv_main1003_2 var13 var12 var11 var10) (and (and (= nullAddr var9) (and (and (and (and (and (= var8 var7) (= var6 var5)) (= var4 var3)) (= var2 var1)) (= var9 (|TSLL::next| (getTSLL (read var7 var5))))) (and (and (and (= var7 (write var13 var11 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var13 var11))) (|TSLL::prev| (getTSLL (read var13 var11))) var10)))) (= var5 var12)) (= var3 var11)) (= var1 var10)))) (= var0 0)))) (inv_main1031_11 var8 var6 var9 var2))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Addr) (var6 Int) (var7 Addr) (var8 Addr) (var9 TSLL) (var10 Heap) (var11 Addr) (var12 Int) (var13 Int) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Heap) (var19 Heap) (var20 Int) (var21 Addr) (var22 Int) (var23 Addr) (var24 Heap) (var25 Int) (var26 Int) (var27 Addr) (var28 Addr) (var29 Addr) (var30 Addr) (var31 Heap) (var32 Heap) (var33 Addr) (var34 Int) (var35 Addr) (var36 Addr) (var37 Heap)) (or (not (and (inv_main1003_2 var37 var36 var35 var34) (and (and (= nullAddr var33) (and (and (and (and (and (= var32 var31) (= var30 var29)) (= var28 var27)) (= var26 var25)) (= var33 (|TSLL::next| (getTSLL (read var31 var29))))) (and (and (and (= var31 (write var24 var23 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var24 var23))) (|TSLL::prev| (getTSLL (read var24 var23))) var22)))) (= var29 var21)) (= var27 var23)) (= var25 var22)))) (and (not (= var22 2)) (and (not (= var22 1)) (and (not (= var20 0)) (and (and (and (and (and (and (and (= var19 var18) (= var17 var16)) (= var15 var14)) (= var13 var12)) (= var11 (|TSLL::next| (getTSLL (read var18 var14))))) (and (and (and (and (and (and (= var10 (newHeap (alloc var37 (O_TSLL var9)))) (= var8 var36)) (= var7 var35)) (= var6 var34)) (= var5 (newAddr (alloc var37 (O_TSLL var9))))) (not (= var4 0))) (and (and (and (= var3 (write var10 var7 (O_TSLL (TSLL var5 (|TSLL::prev| (getTSLL (read var10 var7))) (|TSLL::data| (getTSLL (read var10 var7))))))) (= var2 var8)) (= var1 var7)) (= var0 var6)))) (and (and (and (= var18 (write var3 (|TSLL::next| (getTSLL (read var3 var1))) (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var3 (|TSLL::next| (getTSLL (read var3 var1)))))) var1 (|TSLL::data| (getTSLL (read var3 (|TSLL::next| (getTSLL (read var3 var1)))))))))) (= var16 var2)) (= var14 var1)) (= var12 var0))) (and (and (and (= var24 (write var19 var11 (O_TSLL (TSLL var17 (|TSLL::prev| (getTSLL (read var19 var11))) (|TSLL::data| (getTSLL (read var19 var11))))))) (= var21 var17)) (= var23 var11)) (= var22 var13))))))))) (inv_main1031_11 var32 var30 var33 var26))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Int) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main_10 var7 var6 var5 var4) (and (= nullAddr var3) (and (and (and (= var2 (write var7 var5 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var7 var5))) (|TSLL::prev| (getTSLL (read var7 var5))) var4)))) (= var1 var6)) (= var3 var5)) (= var0 var4))))) (inv_main1026_12 var2 var1 var3 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Int) (var6 Addr) (var7 Int) (var8 Int) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Heap) (var14 Heap) (var15 Int) (var16 Addr) (var17 Addr) (var18 Heap)) (or (not (and (inv_main_18 var18 var17 var16 var15) (and (and (and (and (and (= var14 var13) (= var12 var11)) (= var10 var9)) (= var8 var7)) (= var6 (|TSLL::next| (getTSLL (read var13 var9))))) (and (and (= var5 0) (and (and (and (and (= var13 var4) (= var11 var3)) (= var9 var2)) (= var7 var1)) (= var5 (|TSLL::data| (getTSLL (read var4 (|TSLL::next| (getTSLL (read var4 var2))))))))) (and (not (= var0 0)) (and (and (and (and (= var4 var18) (= var3 var17)) (= var2 var16)) (= var1 var15)) (= var0 (|TSLL::data| (getTSLL (read var18 var16)))))))))) (inv_main_18 var14 var12 var6 var8))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Int) (var7 Int) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Heap) (var13 Heap) (var14 Int) (var15 Int) (var16 Addr) (var17 Int) (var18 Int) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Heap) (var24 Heap) (var25 Int) (var26 Addr) (var27 Addr) (var28 Heap)) (or (not (and (inv_main_18 var28 var27 var26 var25) (and (and (and (and (and (= var24 var23) (= var22 var21)) (= var20 var19)) (= var18 var17)) (= var16 (|TSLL::next| (getTSLL (read var23 var19))))) (and (and (not (= var15 0)) (and (and (and (not (= var14 0)) (and (and (and (and (= var13 var12) (= var11 var10)) (= var9 var8)) (= var7 var6)) (= var14 (|TSLL::data| (getTSLL (read var12 (|TSLL::next| (getTSLL (read var12 var8))))))))) (and (and (and (and (= var5 var13) (= var4 var11)) (= var3 var9)) (= var2 var7)) (= var1 (|TSLL::data| (getTSLL (read var13 var9)))))) (and (and (and (and (= var23 var5) (= var21 var4)) (= var19 var3)) (= var17 var2)) (or (and (<= 0 (+ (|TSLL::data| (getTSLL (read var5 (|TSLL::next| (getTSLL (read var5 var3)))))) (* (- 1) var1))) (= var15 1)) (and (not (<= 0 (+ (|TSLL::data| (getTSLL (read var5 (|TSLL::next| (getTSLL (read var5 var3)))))) (* (- 1) var1)))) (= var15 0)))))) (and (not (= var0 0)) (and (and (and (and (= var12 var28) (= var10 var27)) (= var8 var26)) (= var6 var25)) (= var0 (|TSLL::data| (getTSLL (read var28 var26)))))))))) (inv_main_18 var24 var22 var16 var18))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Heap) (var9 Addr) (var10 Int) (var11 Addr) (var12 Addr) (var13 Heap)) (or (not (and (inv_main1003_2 var13 var12 var11 var10) (and (and (not (= nullAddr var9)) (and (and (and (and (and (= var8 var7) (= var6 var5)) (= var4 var3)) (= var2 var1)) (= var9 (|TSLL::next| (getTSLL (read var7 var5))))) (and (and (and (= var7 (write var13 var11 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var13 var11))) (|TSLL::prev| (getTSLL (read var13 var11))) var10)))) (= var5 var12)) (= var3 var11)) (= var1 var10)))) (= var0 0)))) (inv_main_18 var8 var6 var9 var2))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Addr) (var6 Int) (var7 Addr) (var8 Addr) (var9 TSLL) (var10 Heap) (var11 Addr) (var12 Int) (var13 Int) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Heap) (var19 Heap) (var20 Int) (var21 Addr) (var22 Int) (var23 Addr) (var24 Heap) (var25 Int) (var26 Int) (var27 Addr) (var28 Addr) (var29 Addr) (var30 Addr) (var31 Heap) (var32 Heap) (var33 Addr) (var34 Int) (var35 Addr) (var36 Addr) (var37 Heap)) (or (not (and (inv_main1003_2 var37 var36 var35 var34) (and (and (not (= nullAddr var33)) (and (and (and (and (and (= var32 var31) (= var30 var29)) (= var28 var27)) (= var26 var25)) (= var33 (|TSLL::next| (getTSLL (read var31 var29))))) (and (and (and (= var31 (write var24 var23 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var24 var23))) (|TSLL::prev| (getTSLL (read var24 var23))) var22)))) (= var29 var21)) (= var27 var23)) (= var25 var22)))) (and (not (= var22 2)) (and (not (= var22 1)) (and (not (= var20 0)) (and (and (and (and (and (and (and (= var19 var18) (= var17 var16)) (= var15 var14)) (= var13 var12)) (= var11 (|TSLL::next| (getTSLL (read var18 var14))))) (and (and (and (and (and (and (= var10 (newHeap (alloc var37 (O_TSLL var9)))) (= var8 var36)) (= var7 var35)) (= var6 var34)) (= var5 (newAddr (alloc var37 (O_TSLL var9))))) (not (= var4 0))) (and (and (and (= var3 (write var10 var7 (O_TSLL (TSLL var5 (|TSLL::prev| (getTSLL (read var10 var7))) (|TSLL::data| (getTSLL (read var10 var7))))))) (= var2 var8)) (= var1 var7)) (= var0 var6)))) (and (and (and (= var18 (write var3 (|TSLL::next| (getTSLL (read var3 var1))) (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var3 (|TSLL::next| (getTSLL (read var3 var1)))))) var1 (|TSLL::data| (getTSLL (read var3 (|TSLL::next| (getTSLL (read var3 var1)))))))))) (= var16 var2)) (= var14 var1)) (= var12 var0))) (and (and (and (= var24 (write var19 var11 (O_TSLL (TSLL var17 (|TSLL::prev| (getTSLL (read var19 var11))) (|TSLL::data| (getTSLL (read var19 var11))))))) (= var21 var17)) (= var23 var11)) (= var22 var13))))))))) (inv_main_18 var32 var30 var33 var26))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap) (var9 Heap) (var10 Int) (var11 Addr) (var12 Addr) (var13 Heap)) (or (not (and (inv_main_18 var13 var12 var11 var10) (and (and (and (and (and (= var9 var8) (= var7 var6)) (= var5 var4)) (= var3 var2)) (= var1 (|TSLL::next| (getTSLL (read var8 var6))))) (and (= var0 0) (and (and (and (and (= var8 var13) (= var6 var12)) (= var4 var11)) (= var2 var10)) (= var0 (|TSLL::data| (getTSLL (read var13 var11))))))))) (inv_main_28 var9 var7 var1 var3))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Int) (var3 Addr) (var4 Int) (var5 Int) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap) (var10 Heap) (var11 Int) (var12 Addr) (var13 Addr) (var14 Heap)) (or (not (and (inv_main_28 var14 var13 var12 var11) (and (and (and (and (and (and (= var10 var9) (= var8 var7)) (= var6 var7)) (= var5 var4)) (= var3 (|TSLL::next| (getTSLL (read var9 var7))))) (and (not (= var2 0)) (and (and (and (and (= var9 var14) (= var1 var13)) (= var7 var12)) (= var4 var11)) (= var2 (|TSLL::data| (getTSLL (read var14 var12))))))) (= var0 (write var10 var8 defObj))))) (inv_main_28 var0 var8 var3 var5))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Int) (var9 Addr) (var10 Int) (var11 Addr) (var12 Addr) (var13 TSLL) (var14 Heap) (var15 Addr) (var16 Int) (var17 Int) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Heap) (var23 Heap) (var24 Int) (var25 Int) (var26 Addr) (var27 Addr) (var28 Heap)) (or (not (and (inv_main1003_2 var28 var27 var26 var25) (and (= var24 0) (and (and (and (and (and (and (and (= var23 var22) (= var21 var20)) (= var19 var18)) (= var17 var16)) (= var15 (|TSLL::next| (getTSLL (read var22 var18))))) (and (and (and (and (and (and (= var14 (newHeap (alloc var28 (O_TSLL var13)))) (= var12 var27)) (= var11 var26)) (= var10 var25)) (= var9 (newAddr (alloc var28 (O_TSLL var13))))) (not (= var8 0))) (and (and (and (= var7 (write var14 var11 (O_TSLL (TSLL var9 (|TSLL::prev| (getTSLL (read var14 var11))) (|TSLL::data| (getTSLL (read var14 var11))))))) (= var6 var12)) (= var5 var11)) (= var4 var10)))) (and (and (and (= var22 (write var7 (|TSLL::next| (getTSLL (read var7 var5))) (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var7 (|TSLL::next| (getTSLL (read var7 var5)))))) var5 (|TSLL::data| (getTSLL (read var7 (|TSLL::next| (getTSLL (read var7 var5)))))))))) (= var20 var6)) (= var18 var5)) (= var16 var4))) (and (and (and (= var3 (write var23 var15 (O_TSLL (TSLL var21 (|TSLL::prev| (getTSLL (read var23 var15))) (|TSLL::data| (getTSLL (read var23 var15))))))) (= var2 var21)) (= var1 var15)) (= var0 var17)))))) (inv_main_10 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Int) (var9 Addr) (var10 Int) (var11 Addr) (var12 Addr) (var13 TSLL) (var14 Heap) (var15 Addr) (var16 Int) (var17 Int) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Heap) (var23 Heap) (var24 Int) (var25 Int) (var26 Int) (var27 Addr) (var28 Addr) (var29 Heap)) (or (not (and (inv_main1003_2 var29 var28 var27 var26) (and (and (= var25 1) (and (not (= var24 0)) (and (and (and (and (and (and (and (= var23 var22) (= var21 var20)) (= var19 var18)) (= var17 var16)) (= var15 (|TSLL::next| (getTSLL (read var22 var18))))) (and (and (and (and (and (and (= var14 (newHeap (alloc var29 (O_TSLL var13)))) (= var12 var28)) (= var11 var27)) (= var10 var26)) (= var9 (newAddr (alloc var29 (O_TSLL var13))))) (not (= var8 0))) (and (and (and (= var7 (write var14 var11 (O_TSLL (TSLL var9 (|TSLL::prev| (getTSLL (read var14 var11))) (|TSLL::data| (getTSLL (read var14 var11))))))) (= var6 var12)) (= var5 var11)) (= var4 var10)))) (and (and (and (= var22 (write var7 (|TSLL::next| (getTSLL (read var7 var5))) (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var7 (|TSLL::next| (getTSLL (read var7 var5)))))) var5 (|TSLL::data| (getTSLL (read var7 (|TSLL::next| (getTSLL (read var7 var5)))))))))) (= var20 var6)) (= var18 var5)) (= var16 var4))) (and (and (and (= var3 (write var23 var15 (O_TSLL (TSLL var21 (|TSLL::prev| (getTSLL (read var23 var15))) (|TSLL::data| (getTSLL (read var23 var15))))))) (= var2 var21)) (= var1 var15)) (= var25 var17))))) (= var0 2)))) (inv_main_10 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Int) (var9 Addr) (var10 Int) (var11 Addr) (var12 Addr) (var13 TSLL) (var14 Heap) (var15 Addr) (var16 Int) (var17 Int) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Heap) (var23 Heap) (var24 Int) (var25 Int) (var26 Int) (var27 Addr) (var28 Addr) (var29 Heap)) (or (not (and (inv_main1003_2 var29 var28 var27 var26) (and (and (= var25 2) (and (not (= var25 1)) (and (not (= var24 0)) (and (and (and (and (and (and (and (= var23 var22) (= var21 var20)) (= var19 var18)) (= var17 var16)) (= var15 (|TSLL::next| (getTSLL (read var22 var18))))) (and (and (and (and (and (and (= var14 (newHeap (alloc var29 (O_TSLL var13)))) (= var12 var28)) (= var11 var27)) (= var10 var26)) (= var9 (newAddr (alloc var29 (O_TSLL var13))))) (not (= var8 0))) (and (and (and (= var7 (write var14 var11 (O_TSLL (TSLL var9 (|TSLL::prev| (getTSLL (read var14 var11))) (|TSLL::data| (getTSLL (read var14 var11))))))) (= var6 var12)) (= var5 var11)) (= var4 var10)))) (and (and (and (= var22 (write var7 (|TSLL::next| (getTSLL (read var7 var5))) (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var7 (|TSLL::next| (getTSLL (read var7 var5)))))) var5 (|TSLL::data| (getTSLL (read var7 (|TSLL::next| (getTSLL (read var7 var5)))))))))) (= var20 var6)) (= var18 var5)) (= var16 var4))) (and (and (and (= var3 (write var23 var15 (O_TSLL (TSLL var21 (|TSLL::prev| (getTSLL (read var23 var15))) (|TSLL::data| (getTSLL (read var23 var15))))))) (= var2 var21)) (= var1 var15)) (= var25 var17)))))) (= var0 3)))) (inv_main_10 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Int) (var6 Int) (var7 Addr) (var8 Addr) (var9 Heap) (var10 Int) (var11 Int) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Heap) (var17 Heap) (var18 Int) (var19 Int) (var20 Int) (var21 Addr) (var22 Addr) (var23 Heap)) (or (not (and (inv_main_18 var23 var22 var21 var20) (and (and (= var19 0) (and (and (and (not (= var18 0)) (and (and (and (and (= var17 var16) (= var15 var14)) (= var13 var12)) (= var11 var10)) (= var18 (|TSLL::data| (getTSLL (read var16 (|TSLL::next| (getTSLL (read var16 var12))))))))) (and (and (and (and (= var9 var17) (= var8 var15)) (= var7 var13)) (= var6 var11)) (= var5 (|TSLL::data| (getTSLL (read var17 var13)))))) (and (and (and (and (= var4 var9) (= var3 var8)) (= var2 var7)) (= var1 var6)) (or (and (<= 0 (+ (|TSLL::data| (getTSLL (read var9 (|TSLL::next| (getTSLL (read var9 var7)))))) (* (- 1) var5))) (= var19 1)) (and (not (<= 0 (+ (|TSLL::data| (getTSLL (read var9 (|TSLL::next| (getTSLL (read var9 var7)))))) (* (- 1) var5)))) (= var19 0)))))) (and (not (= var0 0)) (and (and (and (and (= var16 var23) (= var14 var22)) (= var12 var21)) (= var10 var20)) (= var0 (|TSLL::data| (getTSLL (read var23 var21))))))))) (inv_main1035_12 var4 var3 var2 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Int) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main_10 var7 var6 var5 var4) (and (not (= nullAddr var3)) (and (and (and (= var2 (write var7 var5 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var7 var5))) (|TSLL::prev| (getTSLL (read var7 var5))) var4)))) (= var1 var6)) (= var3 var5)) (= var0 var4))))) (inv_main1003_2 var2 var1 var3 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Heap) (var7 Addr) (var8 TSLL) (var9 Heap) (var10 Heap)) (or (not (and (inv_main997_2 var10) (and (and (and (and (and (= var9 (newHeap (alloc var10 (O_TSLL var8)))) (= var7 (newAddr (alloc var10 (O_TSLL var8))))) (and (= var6 (write var9 var7 (O_TSLL (TSLL var7 (|TSLL::prev| (getTSLL (read var9 var7))) (|TSLL::data| (getTSLL (read var9 var7))))))) (= var5 var7))) (and (= var4 (write var6 var5 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var6 var5))) nullAddr (|TSLL::data| (getTSLL (read var6 var5))))))) (= var3 var5))) (and (= var2 (write var4 var3 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var4 var3))) (|TSLL::prev| (getTSLL (read var4 var3))) 0)))) (= var1 var3))) (= var0 1)))) (inv_main1003_2 var2 var1 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (inv_main1026_12 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (inv_main1031_11 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (inv_main1035_12 var3 var2 var1 var0))))
(check-sat)
