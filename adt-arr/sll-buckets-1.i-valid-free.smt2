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

(declare-datatypes ((HeapObject 0) (TSLL 0) (TBCK 0))
                   (((O_Int (getInt Int)) (O_UInt (getUInt Int)) (O_Addr (getAddr Addr)) (O_AddrRange (getAddrRange AddrRange)) (O_TSLL (getTSLL TSLL)) (O_TBCK (getTBCK TBCK)) (defObj))
                   ((TSLL (|TSLL::next| Addr) (|TSLL::data| Int)))
                   ((TBCK (|TBCK::next| Addr) (|TBCK::list| Addr) (|TBCK::data| Int)))))
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
(declare-fun inv_main1004_2 (Heap) Bool)
(declare-fun inv_main1020_2 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main_20 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main_28 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main_35 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main_40 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main_47 (Heap Addr Addr Addr Addr) Bool)
(assert (forall ((var0 Heap)) (or (not (= var0 emptyHeap)) (inv_main1004_2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap) (var9 Addr) (var10 Heap) (var11 Int) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Heap)) (or (not (and (inv_main_35 var16 var15 var14 var13 var12) (and (and (= var11 (|TBCK::data| (getTBCK (read var10 var9)))) (and (and (and (and (and (= var10 var8) (= var7 var6)) (= var9 var5)) (= var4 var3)) (= var2 var1)) (= var11 (|TSLL::data| (getTSLL (read var8 var1)))))) (and (and (and (and (and (and (= var8 var16) (= var6 var15)) (= var5 var14)) (= var0 var13)) (= var1 var13)) (= var3 (|TSLL::next| (getTSLL (read var16 var13))))) (not (= var13 nullAddr)))))) (inv_main_40 var10 var7 var9 var4 var2))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap) (var11 Heap) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Heap)) (or (not (and (inv_main_20 var17 var16 var15 var14 var13) (and (and (and (= var12 nullAddr) (and (and (and (and (and (= var11 var10) (= var9 var8)) (= var7 var6)) (= var5 var4)) (= var3 var2)) (= var12 (|TBCK::list| (getTBCK (read var10 var6)))))) (and (not (= var6 nullAddr)) (and (= var1 (|TSLL::data| (getTSLL (read var10 var4)))) (and (and (and (and (and (= var10 var17) (= var8 var16)) (= var6 var15)) (= var4 var14)) (= var2 var13)) (= var1 (|TBCK::data| (getTBCK (read var17 var15)))))))) (= var0 (write var11 var7 (O_TBCK (TBCK (|TBCK::next| (getTBCK (read var11 var7))) var5 (|TBCK::data| (getTBCK (read var11 var7)))))))))) (inv_main1020_2 var0 var9 var7 var5 var3))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Heap)) (or (not (and (inv_main_28 var11 var10 var9 var8 var7) (and (and (= var6 nullAddr) (and (and (and (and (and (= var5 var11) (= var4 var10)) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var6 (|TSLL::next| (getTSLL (read var11 var7)))))) (= var0 (write var5 var1 (O_TSLL (TSLL var2 (|TSLL::data| (getTSLL (read var5 var1)))))))))) (inv_main1020_2 var0 var4 var3 var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 TBCK) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 TBCK) (var10 Heap) (var11 Heap) (var12 Addr) (var13 Addr) (var14 Heap) (var15 Addr) (var16 Addr) (var17 Heap) (var18 Addr) (var19 Addr) (var20 Heap) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Heap) (var25 Heap) (var26 Addr) (var27 Addr) (var28 Addr) (var29 Addr) (var30 Addr) (var31 TBCK) (var32 Heap) (var33 Heap) (var34 Addr) (var35 Addr) (var36 Addr) (var37 Addr) (var38 Addr) (var39 Heap) (var40 Heap) (var41 Addr) (var42 Addr) (var43 Addr) (var44 Addr) (var45 Addr) (var46 Heap) (var47 Heap) (var48 Heap)) (or (not (and (inv_main1004_2 var48) (and (and (and (and (and (and (and (and (= var47 var46) (= var45 var44)) (= var43 var42)) (= var41 nullAddr)) (and (and (and (and (and (and (and (= var40 var39) (= var38 var37)) (= var36 var35)) (= var34 (|TBCK::next| (getTBCK (read var39 var35))))) (and (and (and (and (and (= var33 (newHeap (alloc var32 (O_TBCK var31)))) (= var30 var29)) (= var28 var27)) (= var26 (newAddr (alloc var32 (O_TBCK var31))))) (and (and (and (= var25 var24) (= var23 var22)) (= var21 (|TBCK::next| (getTBCK (read var24 var22))))) (and (and (= var20 (write var25 var21 (O_TBCK (TBCK (|TBCK::next| (getTBCK (read var25 var21))) (|TBCK::list| (getTBCK (read var25 var21))) 1)))) (= var19 var23)) (= var18 var21)))) (and (and (= var32 (write var20 var18 (O_TBCK (TBCK (|TBCK::next| (getTBCK (read var20 var18))) nullAddr (|TBCK::data| (getTBCK (read var20 var18))))))) (= var29 var19)) (= var27 var18)))) (and (and (= var39 (write var33 var28 (O_TBCK (TBCK var26 (|TBCK::list| (getTBCK (read var33 var28))) (|TBCK::data| (getTBCK (read var33 var28))))))) (= var37 var30)) (= var35 var28))) (and (and (= var17 (write var40 var34 (O_TBCK (TBCK (|TBCK::next| (getTBCK (read var40 var34))) (|TBCK::list| (getTBCK (read var40 var34))) 2)))) (= var16 var38)) (= var15 var34))) (and (and (= var14 (write var17 var15 (O_TBCK (TBCK (|TBCK::next| (getTBCK (read var17 var15))) nullAddr (|TBCK::data| (getTBCK (read var17 var15))))))) (= var13 var16)) (= var12 var15)))) (and (and (= var46 (write var14 var12 (O_TBCK (TBCK nullAddr (|TBCK::list| (getTBCK (read var14 var12))) (|TBCK::data| (getTBCK (read var14 var12))))))) (= var44 var13)) (= var42 var12))) (and (and (and (and (= var11 (newHeap (alloc var10 (O_TBCK var9)))) (= var8 var7)) (= var6 (newAddr (alloc var10 (O_TBCK var9))))) (and (and (= var5 (newHeap (alloc var48 (O_TBCK var4)))) (= var3 (newAddr (alloc var48 (O_TBCK var4))))) (and (= var2 (write var5 var3 (O_TBCK (TBCK (|TBCK::next| (getTBCK (read var5 var3))) (|TBCK::list| (getTBCK (read var5 var3))) 0)))) (= var1 var3)))) (and (= var10 (write var2 var1 (O_TBCK (TBCK (|TBCK::next| (getTBCK (read var2 var1))) nullAddr (|TBCK::data| (getTBCK (read var2 var1))))))) (= var7 var1)))) (and (= var24 (write var11 var8 (O_TBCK (TBCK var6 (|TBCK::list| (getTBCK (read var11 var8))) (|TBCK::data| (getTBCK (read var11 var8))))))) (= var22 var8))) (= var0 nullAddr)))) (inv_main1020_2 var47 var45 var43 var41 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Heap) (var17 Heap) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Heap)) (or (not (and (inv_main_20 var22 var21 var20 var19 var18) (and (and (and (and (and (and (= var17 var16) (= var15 var14)) (= var13 var12)) (= var11 var10)) (= var9 var8)) (= var7 (|TBCK::list| (getTBCK (read var16 var12))))) (and (and (not (= var6 nullAddr)) (and (and (and (and (and (= var16 var5) (= var14 var4)) (= var12 var3)) (= var10 var2)) (= var8 var1)) (= var6 (|TBCK::list| (getTBCK (read var5 var3)))))) (and (not (= var3 nullAddr)) (and (= var0 (|TSLL::data| (getTSLL (read var5 var2)))) (and (and (and (and (and (= var5 var22) (= var4 var21)) (= var3 var20)) (= var2 var19)) (= var1 var18)) (= var0 (|TBCK::data| (getTBCK (read var22 var20))))))))))) (inv_main_28 var17 var15 var13 var11 var7))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap) (var11 Heap) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Heap)) (or (not (and (inv_main_28 var16 var15 var14 var13 var12) (and (and (and (and (and (and (= var11 var10) (= var9 var8)) (= var7 var6)) (= var5 var4)) (= var3 var2)) (= var1 (|TSLL::next| (getTSLL (read var10 var2))))) (and (not (= var0 nullAddr)) (and (and (and (and (and (= var10 var16) (= var8 var15)) (= var6 var14)) (= var4 var13)) (= var2 var12)) (= var0 (|TSLL::next| (getTSLL (read var16 var12))))))))) (inv_main_28 var11 var9 var7 var5 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap) (var11 Heap) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Heap)) (or (not (and (inv_main_20 var16 var15 var14 var13 var12) (and (and (and (and (and (and (= var11 var10) (= var9 var8)) (= var7 var6)) (= var5 var4)) (= var3 var2)) (= var1 (|TBCK::next| (getTBCK (read var10 var6))))) (and (not (= var0 (|TSLL::data| (getTSLL (read var10 var4))))) (and (and (and (and (and (= var10 var16) (= var8 var15)) (= var6 var14)) (= var4 var13)) (= var2 var12)) (= var0 (|TBCK::data| (getTBCK (read var16 var14))))))))) (inv_main_20 var11 var9 var1 var5 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Int) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 TSLL) (var15 Heap) (var16 Int) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Heap)) (or (not (and (inv_main1020_2 var23 var22 var21 var20 var19) (and (and (and (not (= var18 nullAddr)) (not (= var17 nullAddr))) (and (not (= var16 0)) (and (and (and (and (and (and (and (= var15 (newHeap (alloc var23 (O_TSLL var14)))) (= var13 var22)) (= var12 var21)) (= var11 var20)) (= var10 var19)) (= var9 (newAddr (alloc var23 (O_TSLL var14))))) (not (= var8 0))) (and (and (and (and (= var7 (write var15 var9 (O_TSLL (TSLL nullAddr (|TSLL::data| (getTSLL (read var15 var9))))))) (= var6 var13)) (= var5 var12)) (= var4 var9)) (= var3 var10))))) (and (and (and (and (= var2 (write var7 var4 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var7 var4))) 0)))) (= var17 var6)) (= var1 var5)) (= var18 var4)) (= var0 var3))))) (inv_main_20 var2 var17 var17 var18 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Int) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 TSLL) (var15 Heap) (var16 Int) (var17 Int) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Heap)) (or (not (and (inv_main1020_2 var24 var23 var22 var21 var20) (and (and (and (not (= var19 nullAddr)) (not (= var18 nullAddr))) (and (not (= var17 0)) (and (= var16 0) (and (and (and (and (and (and (and (= var15 (newHeap (alloc var24 (O_TSLL var14)))) (= var13 var23)) (= var12 var22)) (= var11 var21)) (= var10 var20)) (= var9 (newAddr (alloc var24 (O_TSLL var14))))) (not (= var8 0))) (and (and (and (and (= var7 (write var15 var9 (O_TSLL (TSLL nullAddr (|TSLL::data| (getTSLL (read var15 var9))))))) (= var6 var13)) (= var5 var12)) (= var4 var9)) (= var3 var10)))))) (and (and (and (and (= var2 (write var7 var4 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var7 var4))) 1)))) (= var18 var6)) (= var1 var5)) (= var19 var4)) (= var0 var3))))) (inv_main_20 var2 var18 var18 var19 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Int) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 TSLL) (var15 Heap) (var16 Int) (var17 Int) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Heap)) (or (not (and (inv_main1020_2 var24 var23 var22 var21 var20) (and (and (and (not (= var19 nullAddr)) (not (= var18 nullAddr))) (and (= var17 0) (and (= var16 0) (and (and (and (and (and (and (and (= var15 (newHeap (alloc var24 (O_TSLL var14)))) (= var13 var23)) (= var12 var22)) (= var11 var21)) (= var10 var20)) (= var9 (newAddr (alloc var24 (O_TSLL var14))))) (not (= var8 0))) (and (and (and (and (= var7 (write var15 var9 (O_TSLL (TSLL nullAddr (|TSLL::data| (getTSLL (read var15 var9))))))) (= var6 var13)) (= var5 var12)) (= var4 var9)) (= var3 var10)))))) (and (and (and (and (= var2 (write var7 var4 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var7 var4))) 2)))) (= var18 var6)) (= var1 var5)) (= var19 var4)) (= var0 var3))))) (inv_main_20 var2 var18 var18 var19 var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main_40 var5 var4 var3 var2 var1) (= var0 (write var5 var1 defObj)))) (inv_main_35 var0 var4 var3 var2 var1))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Heap)) (or (not (and (inv_main1020_2 var12 var11 var10 var9 var8) (and (and (and (and (and (and (and (and (= var7 var12) (= var6 var11)) (= var5 var11)) (= var4 var9)) (= var3 var8)) (= var2 (|TBCK::list| (getTBCK (read var12 var11))))) (not (= var11 nullAddr))) (= var1 0)) (= var0 (write var7 var5 (O_TBCK (TBCK (|TBCK::next| (getTBCK (read var7 var5))) nullAddr (|TBCK::data| (getTBCK (read var7 var5)))))))))) (inv_main_35 var0 var6 var5 var2 var3))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Heap) (var16 Heap) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Heap)) (or (not (and (inv_main_47 var21 var20 var19 var18 var17) (and (and (and (and (and (and (and (and (and (= var16 var15) (= var14 var13)) (= var12 var11)) (= var10 var9)) (= var8 var7)) (= var6 (|TBCK::list| (getTBCK (read var15 var11))))) (not (= var11 nullAddr))) (and (and (and (and (= var5 (write var21 var20 defObj)) (= var4 var20)) (= var3 var19)) (= var2 var18)) (= var1 var17))) (and (and (and (and (= var15 var5) (= var13 nullAddr)) (= var11 var3)) (= var9 var2)) (= var7 var1))) (= var0 (write var16 var12 (O_TBCK (TBCK (|TBCK::next| (getTBCK (read var16 var12))) nullAddr (|TBCK::data| (getTBCK (read var16 var12)))))))))) (inv_main_35 var0 var14 var12 var6 var8))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main_35 var10 var9 var8 var7 var6) (and (and (and (and (and (and (= var5 var10) (= var4 var8)) (= var3 var8)) (= var2 var7)) (= var1 var6)) (= var0 (|TBCK::next| (getTBCK (read var10 var8))))) (and (= var7 nullAddr) (= var7 nullAddr))))) (inv_main_47 var5 var4 var0 var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main_40 var4 var3 var2 var1 var0) (and (not (= var0 nullAddr)) (= (read var4 var0) defObj))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main_47 var4 var3 var2 var1 var0) (and (not (= var3 nullAddr)) (= (read var4 var3) defObj))))))
(check-sat)
