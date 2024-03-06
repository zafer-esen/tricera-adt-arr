(set-logic HORN)
(set-info :source |
    Benchmark: C_VC
    Output by Princess (http://www.philipp.ruemmer.org/princess.shtml)
|)
(set-info :status unsat)
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
(declare-fun inv_main1002_2 (Heap Addr Addr Int) Bool)
(declare-fun inv_main1027_12 (Heap Addr Addr Int) Bool)
(declare-fun inv_main1028_12 (Heap Addr Addr Int) Bool)
(declare-fun inv_main1031_11 (Heap Addr Addr Int) Bool)
(declare-fun inv_main1034_12 (Heap Addr Addr Int) Bool)
(declare-fun inv_main1035_12 (Heap Addr Addr Int) Bool)
(declare-fun inv_main1039_12 (Heap Addr Addr Int) Bool)
(declare-fun inv_main1040_12 (Heap Addr Addr Int) Bool)
(declare-fun inv_main1041_12 (Heap Addr Addr Int) Bool)
(declare-fun inv_main1045_12 (Heap Addr Addr Int) Bool)
(declare-fun inv_main1046_12 (Heap Addr Addr Int) Bool)
(declare-fun inv_main1047_12 (Heap Addr Addr Int) Bool)
(declare-fun inv_main1048_12 (Heap Addr Addr Int) Bool)
(declare-fun inv_main1049_12 (Heap Addr Addr Int) Bool)
(declare-fun inv_main1055_12 (Heap Addr Addr Int) Bool)
(declare-fun inv_main997_2 (Heap) Bool)
(declare-fun inv_main_10 (Heap Addr Addr Int) Bool)
(declare-fun inv_main_23 (Heap Addr Addr Int) Bool)
(declare-fun inv_main_30 (Heap Addr Addr Int) Bool)
(declare-fun inv_main_56 (Heap Addr Addr Int) Bool)
(declare-fun inv_main_57 (Heap Addr Addr Int) Bool)
(assert (forall ((var0 Heap)) (or (not (= var0 emptyHeap)) (inv_main997_2 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Int) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main_23 var8 var7 var6 var5) (and (and (= var4 nullAddr) (and (and (and (and (= var3 var8) (= var2 var7)) (= var1 var6)) (= var0 var5)) (= var4 (|TSLL::next| (getTSLL (read var8 var7)))))) (and (not (= var7 nullAddr)) (= var5 2))))) (inv_main1040_12 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main_23 var3 var2 var1 var0) (not (= var0 2)))) (inv_main_30 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Heap) (var9 Addr) (var10 Int) (var11 Addr) (var12 Addr) (var13 Heap)) (or (not (and (inv_main_23 var13 var12 var11 var10) (and (and (not (= var9 nullAddr)) (and (and (and (and (= var8 var7) (= var6 var5)) (= var4 var3)) (= var2 var1)) (= var9 (|TSLL::next| (getTSLL (read var7 (|TSLL::next| (getTSLL (read var7 var5))))))))) (and (and (not (= var0 nullAddr)) (and (and (and (and (= var7 var13) (= var5 var12)) (= var3 var11)) (= var1 var10)) (= var0 (|TSLL::next| (getTSLL (read var13 var12)))))) (and (not (= var12 nullAddr)) (= var10 2)))))) (inv_main_30 var8 var6 var4 var2))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main_23 var3 var2 var1 var0) (and (= var2 nullAddr) (= var0 2)))) (inv_main1039_12 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Int) (var6 Int) (var7 Addr) (var8 Addr) (var9 Heap) (var10 Int) (var11 Int) (var12 Addr) (var13 Addr) (var14 Heap)) (or (not (and (inv_main_56 var14 var13 var12 var11) (and (and (and (= var10 0) (and (not (= var11 0)) (and (and (and (and (= var9 var14) (= var8 var13)) (= var7 var12)) (= var6 var11)) (= var5 (|TSLL::data| (getTSLL (read var14 var12))))))) (and (and (and (and (= var4 var9) (= var3 var8)) (= var2 var7)) (= var1 var6)) (or (and (<= 0 (+ var5 (- 1))) (= var10 1)) (and (not (<= 0 (+ var5 (- 1)))) (= var10 0))))) (and (not (= var0 0)) (not (= var12 nullAddr)))))) (inv_main1055_12 var4 var3 var2 var1))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Heap) (var9 Addr) (var10 Int) (var11 Addr) (var12 Addr) (var13 Heap)) (or (not (and (inv_main_23 var13 var12 var11 var10) (and (and (= var9 nullAddr) (and (and (and (and (= var8 var7) (= var6 var5)) (= var4 var3)) (= var2 var1)) (= var9 (|TSLL::next| (getTSLL (read var7 (|TSLL::next| (getTSLL (read var7 var5))))))))) (and (and (not (= var0 nullAddr)) (and (and (and (and (= var7 var13) (= var5 var12)) (= var3 var11)) (= var1 var10)) (= var0 (|TSLL::next| (getTSLL (read var13 var12)))))) (and (not (= var12 nullAddr)) (= var10 2)))))) (inv_main1041_12 var8 var6 var4 var2))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Int) (var7 Addr) (var8 Addr) (var9 Heap) (var10 Addr) (var11 Int) (var12 Int) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Heap) (var18 Heap) (var19 Int) (var20 Int) (var21 Addr) (var22 Addr) (var23 Heap)) (or (not (and (inv_main_30 var23 var22 var21 var20) (and (and (= var19 3) (and (and (and (and (= var18 var17) (= var16 var15)) (= var14 var13)) (= var12 var11)) (= var19 (|TSLL::data| (getTSLL (read var17 (|TSLL::next| (getTSLL (read var17 (|TSLL::next| (getTSLL (read var17 (|TSLL::next| (getTSLL (read var17 var15))))))))))))))) (and (and (not (= var10 nullAddr)) (and (and (and (and (= var17 var9) (= var15 var8)) (= var13 var7)) (= var11 var6)) (= var10 (|TSLL::next| (getTSLL (read var9 (|TSLL::next| (getTSLL (read var9 (|TSLL::next| (getTSLL (read var9 var8)))))))))))) (and (and (not (= var5 nullAddr)) (and (and (and (and (= var9 var4) (= var8 var3)) (= var7 var2)) (= var6 var1)) (= var5 (|TSLL::next| (getTSLL (read var4 (|TSLL::next| (getTSLL (read var4 var3))))))))) (and (and (not (= var0 nullAddr)) (and (and (and (and (= var4 var23) (= var3 var22)) (= var2 var21)) (= var1 var20)) (= var0 (|TSLL::next| (getTSLL (read var23 var22)))))) (and (not (= var22 nullAddr)) (= var20 3)))))))) (inv_main1049_12 var18 var16 var14 var12))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main1002_2 var4 var3 var2 var1) (and (= var3 nullAddr) (and (= var1 1) (and (not (= var3 nullAddr)) (= var0 0)))))) (inv_main1034_12 var4 var3 var2 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main_10 var3 var2 var1 var0) (= var2 nullAddr))) (inv_main1027_12 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Int) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main_56 var9 var8 var7 var6) (and (and (and (and (and (= var5 var9) (= var4 var8)) (= var3 var7)) (= var2 var6)) (= var1 (|TSLL::next| (getTSLL (read var9 var7))))) (and (= var6 0) (and (not (= var0 0)) (not (= var7 nullAddr))))))) (inv_main_56 var5 var4 var1 var2))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Int) (var7 Addr) (var8 Int) (var9 Int) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Heap) (var15 Heap) (var16 Int) (var17 Addr) (var18 Addr) (var19 Heap)) (or (not (and (inv_main_56 var19 var18 var17 var16) (and (and (and (and (and (= var15 var14) (= var13 var12)) (= var11 var10)) (= var9 var8)) (= var7 (|TSLL::next| (getTSLL (read var14 var10))))) (and (and (and (not (= var6 0)) (and (not (= var16 0)) (and (and (and (and (= var5 var19) (= var4 var18)) (= var3 var17)) (= var2 var16)) (= var1 (|TSLL::data| (getTSLL (read var19 var17))))))) (and (and (and (and (= var14 var5) (= var12 var4)) (= var10 var3)) (= var8 var2)) (or (and (<= 0 (+ var1 (- 1))) (= var6 1)) (and (not (<= 0 (+ var1 (- 1)))) (= var6 0))))) (and (not (= var0 0)) (not (= var17 nullAddr))))))) (inv_main_56 var15 var13 var7 var9))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Int) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main_30 var8 var7 var6 var5) (and (and (and (and (and (= var4 var8) (= var3 var7)) (= var2 var6)) (= var1 var5)) (= var0 (|TSLL::next| (getTSLL (read var8 var7))))) (not (= var5 3))))) (inv_main_56 var4 var3 var0 var1))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Int) (var7 Addr) (var8 Addr) (var9 Heap) (var10 Addr) (var11 Int) (var12 Addr) (var13 Addr) (var14 Heap) (var15 Int) (var16 Addr) (var17 Int) (var18 Int) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Heap) (var24 Heap) (var25 Int) (var26 Addr) (var27 Addr) (var28 Heap)) (or (not (and (inv_main_30 var28 var27 var26 var25) (and (and (and (and (and (= var24 var23) (= var22 var21)) (= var20 var19)) (= var18 var17)) (= var16 (|TSLL::next| (getTSLL (read var23 var21))))) (and (and (not (= var15 3)) (and (and (and (and (= var23 var14) (= var21 var13)) (= var19 var12)) (= var17 var11)) (= var15 (|TSLL::data| (getTSLL (read var14 (|TSLL::next| (getTSLL (read var14 (|TSLL::next| (getTSLL (read var14 (|TSLL::next| (getTSLL (read var14 var13))))))))))))))) (and (and (not (= var10 nullAddr)) (and (and (and (and (= var14 var9) (= var13 var8)) (= var12 var7)) (= var11 var6)) (= var10 (|TSLL::next| (getTSLL (read var9 (|TSLL::next| (getTSLL (read var9 (|TSLL::next| (getTSLL (read var9 var8)))))))))))) (and (and (not (= var5 nullAddr)) (and (and (and (and (= var9 var4) (= var8 var3)) (= var7 var2)) (= var6 var1)) (= var5 (|TSLL::next| (getTSLL (read var4 (|TSLL::next| (getTSLL (read var4 var3))))))))) (and (and (not (= var0 nullAddr)) (and (and (and (and (= var4 var28) (= var3 var27)) (= var2 var26)) (= var1 var25)) (= var0 (|TSLL::next| (getTSLL (read var28 var27)))))) (and (not (= var27 nullAddr)) (= var25 3))))))))) (inv_main_56 var24 var22 var16 var18))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main1002_2 var4 var3 var2 var1) (and (not (= var1 1)) (and (not (= var3 nullAddr)) (= var0 0))))) (inv_main_23 var4 var3 var2 var1))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Int) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main1002_2 var9 var8 var7 var6) (and (and (not (= var5 nullAddr)) (and (and (and (and (= var4 var9) (= var3 var8)) (= var2 var7)) (= var1 var6)) (= var5 (|TSLL::next| (getTSLL (read var9 var8)))))) (and (not (= var8 nullAddr)) (and (= var6 1) (and (not (= var8 nullAddr)) (= var0 0))))))) (inv_main_23 var4 var3 var2 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Int) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main_30 var8 var7 var6 var5) (and (and (= var4 nullAddr) (and (and (and (and (= var3 var8) (= var2 var7)) (= var1 var6)) (= var0 var5)) (= var4 (|TSLL::next| (getTSLL (read var8 var7)))))) (and (not (= var7 nullAddr)) (= var5 3))))) (inv_main1046_12 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main_30 var3 var2 var1 var0) (and (= var2 nullAddr) (= var0 3)))) (inv_main1045_12 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main_10 var3 var2 var1 var0) (and (= var1 nullAddr) (not (= var2 nullAddr))))) (inv_main1028_12 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main_56 var3 var2 var1 var0) (= var1 nullAddr))) (inv_main_57 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main_56 var4 var3 var2 var1) (and (= var0 0) (not (= var2 nullAddr))))) (inv_main_57 var4 var3 var2 var1))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Int) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main_57 var9 var8 var7 var6) (and (and (and (and (and (and (= var5 var9) (= var4 var8)) (= var3 var8)) (= var2 var6)) (= var1 (|TSLL::next| (getTSLL (read var9 var8))))) (not (= var8 nullAddr))) (= var0 (write var5 var3 defObj))))) (inv_main_57 var0 var1 var3 var2))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Heap) (var9 Addr) (var10 Int) (var11 Addr) (var12 Addr) (var13 Heap)) (or (not (and (inv_main_30 var13 var12 var11 var10) (and (and (= var9 nullAddr) (and (and (and (and (= var8 var7) (= var6 var5)) (= var4 var3)) (= var2 var1)) (= var9 (|TSLL::next| (getTSLL (read var7 (|TSLL::next| (getTSLL (read var7 var5))))))))) (and (and (not (= var0 nullAddr)) (and (and (and (and (= var7 var13) (= var5 var12)) (= var3 var11)) (= var1 var10)) (= var0 (|TSLL::next| (getTSLL (read var13 var12)))))) (and (not (= var12 nullAddr)) (= var10 3)))))) (inv_main1047_12 var8 var6 var4 var2))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Int) (var9 Addr) (var10 Addr) (var11 Heap) (var12 Int) (var13 Addr) (var14 Int) (var15 Addr) (var16 Addr) (var17 TSLL) (var18 Heap) (var19 Addr) (var20 Int) (var21 Int) (var22 Addr) (var23 Addr) (var24 Addr) (var25 Addr) (var26 Heap) (var27 Heap) (var28 Int) (var29 Int) (var30 Addr) (var31 Addr) (var32 Heap)) (or (not (and (inv_main1002_2 var32 var31 var30 var29) (and (and (and (and (= var28 0) (and (and (and (and (and (and (= var27 var26) (= var25 var24)) (= var23 var22)) (= var21 var20)) (= var19 (|TSLL::next| (getTSLL (read var26 var22))))) (and (and (and (and (and (and (= var18 (newHeap (alloc var32 (O_TSLL var17)))) (= var16 var31)) (= var15 var30)) (= var14 var29)) (= var13 (newAddr (alloc var32 (O_TSLL var17))))) (not (= var12 0))) (and (and (and (= var11 (write var18 var15 (O_TSLL (TSLL var13 (|TSLL::prev| (getTSLL (read var18 var15))) (|TSLL::data| (getTSLL (read var18 var15))))))) (= var10 var16)) (= var9 var15)) (= var8 var14)))) (and (and (and (= var26 (write var11 (|TSLL::next| (getTSLL (read var11 var9))) (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var11 (|TSLL::next| (getTSLL (read var11 var9)))))) var9 (|TSLL::data| (getTSLL (read var11 (|TSLL::next| (getTSLL (read var11 var9)))))))))) (= var24 var10)) (= var22 var9)) (= var20 var8)))) (and (and (and (= var7 (write var27 var19 (O_TSLL (TSLL nullAddr (|TSLL::prev| (getTSLL (read var27 var19))) (|TSLL::data| (getTSLL (read var27 var19))))))) (= var6 var25)) (= var5 var19)) (= var28 var21))) (and (and (and (= var4 (write var7 var5 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var7 var5))) (|TSLL::prev| (getTSLL (read var7 var5))) 1)))) (= var3 var6)) (= var2 var5)) (= var1 var28))) (= var0 1)))) (inv_main_10 var4 var3 var2 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Int) (var9 Addr) (var10 Addr) (var11 Heap) (var12 Int) (var13 Addr) (var14 Int) (var15 Addr) (var16 Addr) (var17 TSLL) (var18 Heap) (var19 Addr) (var20 Int) (var21 Int) (var22 Addr) (var23 Addr) (var24 Addr) (var25 Addr) (var26 Heap) (var27 Heap) (var28 Int) (var29 Int) (var30 Addr) (var31 Addr) (var32 Heap)) (or (not (and (inv_main1002_2 var32 var31 var30 var29) (and (and (and (= var28 1) (and (and (not (= var28 0)) (and (and (and (and (and (and (= var27 var26) (= var25 var24)) (= var23 var22)) (= var21 var20)) (= var19 (|TSLL::next| (getTSLL (read var26 var22))))) (and (and (and (and (and (and (= var18 (newHeap (alloc var32 (O_TSLL var17)))) (= var16 var31)) (= var15 var30)) (= var14 var29)) (= var13 (newAddr (alloc var32 (O_TSLL var17))))) (not (= var12 0))) (and (and (and (= var11 (write var18 var15 (O_TSLL (TSLL var13 (|TSLL::prev| (getTSLL (read var18 var15))) (|TSLL::data| (getTSLL (read var18 var15))))))) (= var10 var16)) (= var9 var15)) (= var8 var14)))) (and (and (and (= var26 (write var11 (|TSLL::next| (getTSLL (read var11 var9))) (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var11 (|TSLL::next| (getTSLL (read var11 var9)))))) var9 (|TSLL::data| (getTSLL (read var11 (|TSLL::next| (getTSLL (read var11 var9)))))))))) (= var24 var10)) (= var22 var9)) (= var20 var8)))) (and (and (and (= var7 (write var27 var19 (O_TSLL (TSLL nullAddr (|TSLL::prev| (getTSLL (read var27 var19))) (|TSLL::data| (getTSLL (read var27 var19))))))) (= var6 var25)) (= var5 var19)) (= var28 var21)))) (and (and (and (= var4 (write var7 var5 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var7 var5))) (|TSLL::prev| (getTSLL (read var7 var5))) 2)))) (= var3 var6)) (= var2 var5)) (= var1 var28))) (= var0 2)))) (inv_main_10 var4 var3 var2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Int) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Int) (var8 Addr) (var9 Int) (var10 Addr) (var11 Addr) (var12 TSLL) (var13 Heap) (var14 Addr) (var15 Int) (var16 Int) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Heap) (var22 Heap) (var23 Int) (var24 Int) (var25 Addr) (var26 Addr) (var27 Heap)) (or (not (and (inv_main1002_2 var27 var26 var25 var24) (and (not (<= 0 (+ var23 (- 2)))) (and (not (= var23 1)) (and (and (not (= var23 0)) (and (and (and (and (and (and (= var22 var21) (= var20 var19)) (= var18 var17)) (= var16 var15)) (= var14 (|TSLL::next| (getTSLL (read var21 var17))))) (and (and (and (and (and (and (= var13 (newHeap (alloc var27 (O_TSLL var12)))) (= var11 var26)) (= var10 var25)) (= var9 var24)) (= var8 (newAddr (alloc var27 (O_TSLL var12))))) (not (= var7 0))) (and (and (and (= var6 (write var13 var10 (O_TSLL (TSLL var8 (|TSLL::prev| (getTSLL (read var13 var10))) (|TSLL::data| (getTSLL (read var13 var10))))))) (= var5 var11)) (= var4 var10)) (= var3 var9)))) (and (and (and (= var21 (write var6 (|TSLL::next| (getTSLL (read var6 var4))) (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var6 (|TSLL::next| (getTSLL (read var6 var4)))))) var4 (|TSLL::data| (getTSLL (read var6 (|TSLL::next| (getTSLL (read var6 var4)))))))))) (= var19 var5)) (= var17 var4)) (= var15 var3)))) (and (and (and (= var2 (write var22 var14 (O_TSLL (TSLL nullAddr (|TSLL::prev| (getTSLL (read var22 var14))) (|TSLL::data| (getTSLL (read var22 var14))))))) (= var1 var20)) (= var0 var14)) (= var23 var16))))))) (inv_main_10 var2 var1 var0 var23))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Int) (var9 Addr) (var10 Addr) (var11 Heap) (var12 Int) (var13 Addr) (var14 Int) (var15 Addr) (var16 Addr) (var17 TSLL) (var18 Heap) (var19 Addr) (var20 Int) (var21 Int) (var22 Addr) (var23 Addr) (var24 Addr) (var25 Addr) (var26 Heap) (var27 Heap) (var28 Int) (var29 Int) (var30 Addr) (var31 Addr) (var32 Heap)) (or (not (and (inv_main1002_2 var32 var31 var30 var29) (and (and (and (<= 0 (+ var28 (- 2))) (and (not (= var28 1)) (and (and (not (= var28 0)) (and (and (and (and (and (and (= var27 var26) (= var25 var24)) (= var23 var22)) (= var21 var20)) (= var19 (|TSLL::next| (getTSLL (read var26 var22))))) (and (and (and (and (and (and (= var18 (newHeap (alloc var32 (O_TSLL var17)))) (= var16 var31)) (= var15 var30)) (= var14 var29)) (= var13 (newAddr (alloc var32 (O_TSLL var17))))) (not (= var12 0))) (and (and (and (= var11 (write var18 var15 (O_TSLL (TSLL var13 (|TSLL::prev| (getTSLL (read var18 var15))) (|TSLL::data| (getTSLL (read var18 var15))))))) (= var10 var16)) (= var9 var15)) (= var8 var14)))) (and (and (and (= var26 (write var11 (|TSLL::next| (getTSLL (read var11 var9))) (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var11 (|TSLL::next| (getTSLL (read var11 var9)))))) var9 (|TSLL::data| (getTSLL (read var11 (|TSLL::next| (getTSLL (read var11 var9)))))))))) (= var24 var10)) (= var22 var9)) (= var20 var8)))) (and (and (and (= var7 (write var27 var19 (O_TSLL (TSLL nullAddr (|TSLL::prev| (getTSLL (read var27 var19))) (|TSLL::data| (getTSLL (read var27 var19))))))) (= var6 var25)) (= var5 var19)) (= var28 var21))))) (and (and (and (= var4 (write var7 var5 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var7 var5))) (|TSLL::prev| (getTSLL (read var7 var5))) 3)))) (= var3 var6)) (= var2 var5)) (= var1 var28))) (= var0 3)))) (inv_main_10 var4 var3 var2 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Int) (var7 Int) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Heap) (var13 Heap) (var14 Addr) (var15 Int) (var16 Addr) (var17 Addr) (var18 Heap)) (or (not (and (inv_main_30 var18 var17 var16 var15) (and (and (= var14 nullAddr) (and (and (and (and (= var13 var12) (= var11 var10)) (= var9 var8)) (= var7 var6)) (= var14 (|TSLL::next| (getTSLL (read var12 (|TSLL::next| (getTSLL (read var12 (|TSLL::next| (getTSLL (read var12 var10)))))))))))) (and (and (not (= var5 nullAddr)) (and (and (and (and (= var12 var4) (= var10 var3)) (= var8 var2)) (= var6 var1)) (= var5 (|TSLL::next| (getTSLL (read var4 (|TSLL::next| (getTSLL (read var4 var3))))))))) (and (and (not (= var0 nullAddr)) (and (and (and (and (= var4 var18) (= var3 var17)) (= var2 var16)) (= var1 var15)) (= var0 (|TSLL::next| (getTSLL (read var18 var17)))))) (and (not (= var17 nullAddr)) (= var15 3))))))) (inv_main1048_12 var13 var11 var9 var7))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main_10 var3 var2 var1 var0) (and (not (= var1 nullAddr)) (not (= var2 nullAddr))))) (inv_main1002_2 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Heap) (var7 Addr) (var8 TSLL) (var9 Heap) (var10 Heap)) (or (not (and (inv_main997_2 var10) (and (and (and (and (and (= var9 (newHeap (alloc var10 (O_TSLL var8)))) (= var7 (newAddr (alloc var10 (O_TSLL var8))))) (and (= var6 (write var9 var7 (O_TSLL (TSLL nullAddr (|TSLL::prev| (getTSLL (read var9 var7))) (|TSLL::data| (getTSLL (read var9 var7))))))) (= var5 var7))) (and (= var4 (write var6 var5 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var6 var5))) nullAddr (|TSLL::data| (getTSLL (read var6 var5))))))) (= var3 var5))) (and (= var2 (write var4 var3 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var4 var3))) (|TSLL::prev| (getTSLL (read var4 var3))) 0)))) (= var1 var3))) (= var0 0)))) (inv_main1002_2 var2 var1 var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Int) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main1002_2 var9 var8 var7 var6) (and (and (= var5 nullAddr) (and (and (and (and (= var4 var9) (= var3 var8)) (= var2 var7)) (= var1 var6)) (= var5 (|TSLL::next| (getTSLL (read var9 var8)))))) (and (not (= var8 nullAddr)) (and (= var6 1) (and (not (= var8 nullAddr)) (= var0 0))))))) (inv_main1035_12 var4 var3 var2 var1))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main1002_2 var4 var3 var2 var1) (and (= var3 nullAddr) (= var0 0)))) (inv_main1031_11 var4 var3 var2 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (inv_main1027_12 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (inv_main1028_12 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (inv_main1031_11 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (inv_main1034_12 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (inv_main1035_12 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (inv_main1039_12 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (inv_main1040_12 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (inv_main1041_12 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (inv_main1045_12 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (inv_main1046_12 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (inv_main1047_12 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (inv_main1048_12 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (inv_main1049_12 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (inv_main1055_12 var3 var2 var1 var0))))
(check-sat)
