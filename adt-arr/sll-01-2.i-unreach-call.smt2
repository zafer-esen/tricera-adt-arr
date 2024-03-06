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
                   ((TSLL (|TSLL::next| Addr) (|TSLL::inner| Addr)))))
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
(declare-fun inv_main1002_2 (Heap) Bool)
(declare-fun inv_main1004_11 (Heap Addr) Bool)
(declare-fun inv_main1004_256 (Heap Addr) Bool)
(declare-fun inv_main1006_2 (Heap Addr Addr) Bool)
(declare-fun inv_main1015_12 (Heap Addr Addr) Bool)
(declare-fun inv_main1016_12 (Heap Addr Addr) Bool)
(declare-fun inv_main1016_252 (Heap Addr Addr) Bool)
(declare-fun inv_main1023_11 (Heap Addr Addr) Bool)
(declare-fun inv_main1028_3 (Heap Addr Addr Int Addr) Bool)
(declare-fun inv_main1035_13 (Heap Addr Addr Int Addr) Bool)
(declare-fun inv_main1036_13 (Heap Addr Addr Int Addr) Bool)
(declare-fun inv_main1037_13 (Heap Addr Addr Int Addr) Bool)
(declare-fun inv_main1042_12 (Heap Addr Addr Int Addr) Bool)
(declare-fun inv_main1054_13 (Heap Addr Addr) Bool)
(declare-fun inv_main1055_13 (Heap Addr Addr) Bool)
(declare-fun inv_main1056_13 (Heap Addr Addr) Bool)
(declare-fun inv_main_24 (Heap Addr Addr) Bool)
(declare-fun inv_main_36 (Heap Addr Addr) Bool)
(declare-fun inv_main_40 (Heap Addr Addr Int Addr) Bool)
(declare-fun inv_main_5 (Heap Addr) Bool)
(assert (forall ((var0 Heap)) (or (not (= var0 emptyHeap)) (inv_main1002_2 var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 TSLL) (var3 Heap) (var4 Addr) (var5 Heap)) (or (not (and (inv_main1002_2 var5) (and (and (= var4 nullAddr) (and (= var3 (newHeap (alloc var5 (O_TSLL var2)))) (= var1 (newAddr (alloc var5 (O_TSLL var2)))))) (and (= var0 (write var3 var1 (O_TSLL (TSLL nullAddr (|TSLL::inner| (getTSLL (read var3 var1))))))) (= var4 var1))))) (inv_main1004_11 var0 var4))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Heap) (var10 Addr) (var11 Int) (var12 Addr) (var13 Addr) (var14 Heap)) (or (not (and (inv_main_24 var14 var13 var12) (and (and (= var11 0) (and (and (= var10 nullAddr) (and (and (and (= var9 var14) (= var8 var13)) (= var7 var12)) (= var10 (|TSLL::inner| (getTSLL (read var14 var12)))))) (and (and (and (= var6 var9) (= var5 var8)) (= var4 var7)) (= var3 (|TSLL::inner| (getTSLL (read var9 var7))))))) (and (and (and (= var2 var6) (= var1 var5)) (= var0 var4)) (or (and (= var3 nullAddr) (= var11 1)) (and (not (= var3 nullAddr)) (= var11 0))))))) (inv_main1016_252 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main_40 var4 var3 var2 var1 var0) (= nullAddr var0))) (inv_main1035_13 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main_40 var4 var3 var2 var1 var0) (and (not (= nullAddr (|TSLL::next| (getTSLL (read var4 var0))))) (and (= nullAddr (|TSLL::inner| (getTSLL (read var4 var0)))) (not (= nullAddr var0)))))) (inv_main1037_13 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Heap) (var3 Int) (var4 Addr) (var5 Addr) (var6 Addr) (var7 TSLL) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Heap) (var15 Heap) (var16 Addr) (var17 Int) (var18 Addr) (var19 Addr) (var20 Heap)) (or (not (and (inv_main1006_2 var20 var19 var18) (and (and (not (= var17 0)) (and (not (= var16 nullAddr)) (and (and (not (= nullAddr var16)) (and (and (and (and (and (= var15 var14) (= var13 var12)) (= var11 var10)) (= var9 (|TSLL::next| (getTSLL (read var14 var10))))) (and (and (and (and (= var8 (newHeap (alloc var20 (O_TSLL var7)))) (= var6 var19)) (= var5 var18)) (= var4 (newAddr (alloc var20 (O_TSLL var7))))) (not (= var3 0)))) (and (and (= var14 (write var8 var5 (O_TSLL (TSLL var4 (|TSLL::inner| (getTSLL (read var8 var5))))))) (= var12 var6)) (= var10 var5)))) (and (and (= var2 (write var15 var9 (O_TSLL (TSLL nullAddr (|TSLL::inner| (getTSLL (read var15 var9))))))) (= var1 var13)) (= var16 var9))))) (= var0 (write var2 var16 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var2 var16))) nullAddr))))))) (inv_main_24 var0 var1 var16))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Int) (var8 Addr) (var9 Addr) (var10 Addr) (var11 TSLL) (var12 Heap) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Heap) (var19 Heap) (var20 Int) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Addr) (var25 Addr) (var26 TSLL) (var27 Heap) (var28 Heap) (var29 Addr) (var30 Addr) (var31 Heap)) (or (not (and (inv_main1006_2 var31 var30 var29) (and (and (and (and (and (and (and (= var28 (newHeap (alloc var27 (O_TSLL var26)))) (= var25 var24)) (= var23 var22)) (= var21 (newAddr (alloc var27 (O_TSLL var26))))) (and (= var20 0) (and (not (= var22 nullAddr)) (and (and (not (= nullAddr var22)) (and (and (and (and (and (= var19 var18) (= var17 var16)) (= var15 var14)) (= var13 (|TSLL::next| (getTSLL (read var18 var14))))) (and (and (and (and (= var12 (newHeap (alloc var31 (O_TSLL var11)))) (= var10 var30)) (= var9 var29)) (= var8 (newAddr (alloc var31 (O_TSLL var11))))) (not (= var7 0)))) (and (and (= var18 (write var12 var9 (O_TSLL (TSLL var8 (|TSLL::inner| (getTSLL (read var12 var9))))))) (= var16 var10)) (= var14 var9)))) (and (and (= var27 (write var19 var13 (O_TSLL (TSLL nullAddr (|TSLL::inner| (getTSLL (read var19 var13))))))) (= var24 var17)) (= var22 var13)))))) (and (and (= var6 (write var28 var23 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var28 var23))) var21)))) (= var5 var25)) (= var4 var23))) (and (and (= var3 (write var6 (|TSLL::inner| (getTSLL (read var6 var4))) (O_TSLL (TSLL nullAddr (|TSLL::inner| (getTSLL (read var6 (|TSLL::inner| (getTSLL (read var6 var4)))))))))) (= var2 var5)) (= var1 var4))) (= var0 (write var3 (|TSLL::inner| (getTSLL (read var3 var1))) (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var3 (|TSLL::inner| (getTSLL (read var3 var1)))))) nullAddr))))))) (inv_main_24 var0 var2 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main1028_3 var5 var4 var3 var2 var1) (and (and (= var2 0) (not (= nullAddr var1))) (= var0 1)))) (inv_main_40 var5 var4 var3 var0 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main1028_3 var5 var4 var3 var2 var1) (and (and (not (= var2 0)) (not (= nullAddr var1))) (= var0 2)))) (inv_main_40 var5 var4 var3 var0 var1))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main_40 var4 var3 var2 var1 var0) (and (not (= nullAddr (|TSLL::inner| (getTSLL (read var4 var0))))) (not (= nullAddr var0))))) (inv_main1036_13 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main_36 var6 var5 var4) (and (not (= nullAddr (|TSLL::next| (getTSLL (read var3 var2))))) (and (= nullAddr (|TSLL::inner| (getTSLL (read var3 var2)))) (and (not (= nullAddr var2)) (and (not (= nullAddr var2)) (and (and (and (and (= var3 var6) (= var1 var5)) (= var0 var4)) (= var2 (|TSLL::inner| (getTSLL (read var6 var5))))) (not (= nullAddr var5))))))))) (inv_main1056_13 var3 var1 var2))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 TSLL) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Heap) (var14 Heap) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Heap)) (or (not (and (inv_main1006_2 var18 var17 var16) (and (and (= nullAddr var15) (and (and (and (and (and (= var14 var13) (= var12 var11)) (= var10 var9)) (= var8 (|TSLL::next| (getTSLL (read var13 var9))))) (and (and (and (and (= var7 (newHeap (alloc var18 (O_TSLL var6)))) (= var5 var17)) (= var4 var16)) (= var3 (newAddr (alloc var18 (O_TSLL var6))))) (not (= var2 0)))) (and (and (= var13 (write var7 var4 (O_TSLL (TSLL var3 (|TSLL::inner| (getTSLL (read var7 var4))))))) (= var11 var5)) (= var9 var4)))) (and (and (= var1 (write var14 var8 (O_TSLL (TSLL nullAddr (|TSLL::inner| (getTSLL (read var14 var8))))))) (= var0 var12)) (= var15 var8))))) (inv_main1015_12 var1 var0 var15))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 TSLL) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Heap) (var14 Heap) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Heap)) (or (not (and (inv_main1006_2 var18 var17 var16) (and (= var15 nullAddr) (and (and (not (= nullAddr var15)) (and (and (and (and (and (= var14 var13) (= var12 var11)) (= var10 var9)) (= var8 (|TSLL::next| (getTSLL (read var13 var9))))) (and (and (and (and (= var7 (newHeap (alloc var18 (O_TSLL var6)))) (= var5 var17)) (= var4 var16)) (= var3 (newAddr (alloc var18 (O_TSLL var6))))) (not (= var2 0)))) (and (and (= var13 (write var7 var4 (O_TSLL (TSLL var3 (|TSLL::inner| (getTSLL (read var7 var4))))))) (= var11 var5)) (= var9 var4)))) (and (and (= var1 (write var14 var8 (O_TSLL (TSLL nullAddr (|TSLL::inner| (getTSLL (read var14 var8))))))) (= var0 var12)) (= var15 var8)))))) (inv_main1016_12 var1 var0 var15))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main_36 var6 var5 var4) (and (not (= nullAddr (|TSLL::inner| (getTSLL (read var3 var2))))) (and (not (= nullAddr var2)) (and (not (= nullAddr var2)) (and (and (and (and (= var3 var6) (= var1 var5)) (= var0 var4)) (= var2 (|TSLL::inner| (getTSLL (read var6 var5))))) (not (= nullAddr var5)))))))) (inv_main1055_13 var3 var1 var2))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Int) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main1028_3 var10 var9 var8 var7 var6) (and (= nullAddr var5) (and (and (and (and (and (and (= var4 var10) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var0 var6)) (= var5 (|TSLL::next| (getTSLL (read var10 var8))))) (and (<= 0 (+ 1 (* (- 1) var7))) (= nullAddr var6)))))) (inv_main_36 var4 var3 var5))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main1006_2 var6 var5 var4) (and (= nullAddr var3) (and (not (= nullAddr var3)) (and (= var2 0) (and (and (= var1 var6) (= var3 var5)) (= var0 nullAddr))))))) (inv_main_36 var1 var3 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap) (var10 Heap) (var11 Addr) (var12 Addr) (var13 Heap)) (or (not (and (inv_main_36 var13 var12 var11) (and (and (and (and (and (= var10 var9) (= var8 var7)) (= var6 var5)) (= var4 (|TSLL::next| (getTSLL (read var9 var7))))) (and (and (= var3 (write var10 var8 defObj)) (= var2 var8)) (= var1 var4))) (and (= nullAddr var5) (and (and (and (and (= var9 var13) (= var7 var12)) (= var0 var11)) (= var5 (|TSLL::inner| (getTSLL (read var13 var12))))) (not (= nullAddr var12))))))) (inv_main_36 var3 var1 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Heap) (var16 Heap) (var17 Addr) (var18 Addr) (var19 Heap)) (or (not (and (inv_main_36 var19 var18 var17) (and (and (and (and (and (and (= var16 var15) (= var14 var13)) (= var12 var11)) (= var10 (|TSLL::next| (getTSLL (read var15 var13))))) (and (and (= var9 (write var16 var14 defObj)) (= var8 var14)) (= var7 var10))) (and (and (= nullAddr (|TSLL::next| (getTSLL (read var6 var5)))) (and (= nullAddr (|TSLL::inner| (getTSLL (read var6 var5)))) (and (not (= nullAddr var5)) (and (not (= nullAddr var5)) (and (and (and (and (= var6 var19) (= var4 var18)) (= var3 var17)) (= var5 (|TSLL::inner| (getTSLL (read var19 var18))))) (not (= nullAddr var18))))))) (and (and (= var2 (write var6 var5 defObj)) (= var1 var4)) (= var0 var5)))) (and (and (= var15 var2) (= var13 var1)) (= var11 nullAddr))))) (inv_main_36 var9 var7 var7))))
(assert (forall ((var0 Heap) (var1 Heap) (var2 Addr) (var3 TSLL) (var4 Heap) (var5 Addr) (var6 Int) (var7 Heap)) (or (not (and (inv_main1002_2 var7) (and (and (not (= var6 0)) (and (and (not (= var5 nullAddr)) (and (= var4 (newHeap (alloc var7 (O_TSLL var3)))) (= var2 (newAddr (alloc var7 (O_TSLL var3)))))) (and (= var1 (write var4 var2 (O_TSLL (TSLL nullAddr (|TSLL::inner| (getTSLL (read var4 var2))))))) (= var5 var2)))) (= var0 (write var1 var5 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var1 var5))) nullAddr))))))) (inv_main_5 var0 var5))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Heap) (var5 Addr) (var6 TSLL) (var7 Heap) (var8 Int) (var9 Addr) (var10 Addr) (var11 Addr) (var12 TSLL) (var13 Heap) (var14 Heap) (var15 Heap)) (or (not (and (inv_main1002_2 var15) (and (and (and (and (and (and (= var14 (newHeap (alloc var13 (O_TSLL var12)))) (= var11 var10)) (= var9 (newAddr (alloc var13 (O_TSLL var12))))) (and (= var8 0) (and (and (not (= var10 nullAddr)) (and (= var7 (newHeap (alloc var15 (O_TSLL var6)))) (= var5 (newAddr (alloc var15 (O_TSLL var6)))))) (and (= var13 (write var7 var5 (O_TSLL (TSLL nullAddr (|TSLL::inner| (getTSLL (read var7 var5))))))) (= var10 var5))))) (and (= var4 (write var14 var11 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var14 var11))) var9)))) (= var3 var11))) (and (= var2 (write var4 (|TSLL::inner| (getTSLL (read var4 var3))) (O_TSLL (TSLL nullAddr (|TSLL::inner| (getTSLL (read var4 (|TSLL::inner| (getTSLL (read var4 var3)))))))))) (= var1 var3))) (= var0 (write var2 (|TSLL::inner| (getTSLL (read var2 var1))) (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var2 (|TSLL::inner| (getTSLL (read var2 var1)))))) nullAddr))))))) (inv_main_5 var0 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main_36 var6 var5 var4) (and (= nullAddr var3) (and (not (= nullAddr var3)) (and (and (and (and (= var2 var6) (= var1 var5)) (= var0 var4)) (= var3 (|TSLL::inner| (getTSLL (read var6 var5))))) (not (= nullAddr var5))))))) (inv_main1054_13 var2 var1 var3))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main1028_3 var4 var3 var2 var1 var0) (and (not (<= 0 (+ 1 (* (- 1) var1)))) (= nullAddr var0)))) (inv_main1042_12 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Int) (var9 Addr) (var10 Heap)) (or (not (and (inv_main_5 var10 var9) (and (and (= var8 0) (and (and (= var7 nullAddr) (and (and (= var6 var10) (= var5 var9)) (= var7 (|TSLL::inner| (getTSLL (read var10 var9)))))) (and (and (= var4 var6) (= var3 var5)) (= var2 (|TSLL::inner| (getTSLL (read var6 var5))))))) (and (and (= var1 var4) (= var0 var3)) (or (and (= var2 nullAddr) (= var8 1)) (and (not (= var2 nullAddr)) (= var8 0))))))) (inv_main1004_256 var1 var0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main1006_2 var6 var5 var4) (and (= nullAddr var3) (and (= var2 0) (and (and (= var1 var6) (= var3 var5)) (= var0 nullAddr)))))) (inv_main1023_11 var1 var3 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Int) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap) (var11 Heap) (var12 Addr) (var13 Int) (var14 Addr) (var15 Addr) (var16 Heap)) (or (not (and (inv_main_40 var16 var15 var14 var13 var12) (and (and (and (and (and (and (= var11 var10) (= var9 var8)) (= var7 var6)) (= var5 var4)) (= var3 var2)) (= var1 (|TSLL::inner| (getTSLL (read var10 var2))))) (and (= var4 1) (and (and (and (and (and (and (= var10 var16) (= var8 var15)) (= var6 var14)) (= var4 var13)) (= var0 var12)) (= var2 (|TSLL::inner| (getTSLL (read var16 var12))))) (and (= nullAddr (|TSLL::next| (getTSLL (read var16 var12)))) (and (= nullAddr (|TSLL::inner| (getTSLL (read var16 var12)))) (not (= nullAddr var12))))))))) (inv_main1028_3 var11 var9 var7 var5 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Int) (var6 Addr) (var7 Int) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main_40 var10 var9 var8 var7 var6) (and (not (= var5 1)) (and (and (and (and (and (and (= var4 var10) (= var3 var9)) (= var2 var8)) (= var5 var7)) (= var1 var6)) (= var0 (|TSLL::inner| (getTSLL (read var10 var6))))) (and (= nullAddr (|TSLL::next| (getTSLL (read var10 var6)))) (and (= nullAddr (|TSLL::inner| (getTSLL (read var10 var6)))) (not (= nullAddr var6)))))))) (inv_main1028_3 var4 var3 var2 var5 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Int) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Int) (var10 Addr) (var11 Addr) (var12 Heap)) (or (not (and (inv_main1028_3 var12 var11 var10 var9 var8) (and (and (and (not (= nullAddr var7)) (and (and (and (and (and (and (= var6 var12) (= var5 var11)) (= var4 var10)) (= var3 var9)) (= var2 var8)) (= var7 (|TSLL::next| (getTSLL (read var12 var10))))) (and (<= 0 (+ 1 (* (- 1) var9))) (= nullAddr var8)))) (= var1 0)) (= var0 (|TSLL::inner| (getTSLL (read var6 var7))))))) (inv_main1028_3 var6 var5 var7 var1 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main1006_2 var8 var7 var6) (and (and (and (not (= nullAddr var5)) (and (not (= nullAddr var5)) (and (= var4 0) (and (and (= var3 var8) (= var5 var7)) (= var2 nullAddr))))) (= var1 0)) (= var0 (|TSLL::inner| (getTSLL (read var3 var5))))))) (inv_main1028_3 var3 var5 var5 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main_24 var6 var5 var4) (and (not (= var3 nullAddr)) (and (and (and (= var2 var6) (= var1 var5)) (= var0 var4)) (= var3 (|TSLL::inner| (getTSLL (read var6 var4)))))))) (inv_main1006_2 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Heap) (var10 Addr) (var11 Int) (var12 Addr) (var13 Addr) (var14 Heap)) (or (not (and (inv_main_24 var14 var13 var12) (and (and (not (= var11 0)) (and (and (= var10 nullAddr) (and (and (and (= var9 var14) (= var8 var13)) (= var7 var12)) (= var10 (|TSLL::inner| (getTSLL (read var14 var12)))))) (and (and (and (= var6 var9) (= var5 var8)) (= var4 var7)) (= var3 (|TSLL::inner| (getTSLL (read var9 var7))))))) (and (and (and (= var2 var6) (= var1 var5)) (= var0 var4)) (or (and (= var3 nullAddr) (= var11 1)) (and (not (= var3 nullAddr)) (= var11 0))))))) (inv_main1006_2 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main_5 var4 var3) (and (not (= var2 nullAddr)) (and (and (= var1 var4) (= var0 var3)) (= var2 (|TSLL::inner| (getTSLL (read var4 var3)))))))) (inv_main1006_2 var1 var0 var0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Int) (var9 Addr) (var10 Heap)) (or (not (and (inv_main_5 var10 var9) (and (and (not (= var8 0)) (and (and (= var7 nullAddr) (and (and (= var6 var10) (= var5 var9)) (= var7 (|TSLL::inner| (getTSLL (read var10 var9)))))) (and (and (= var4 var6) (= var3 var5)) (= var2 (|TSLL::inner| (getTSLL (read var6 var5))))))) (and (and (= var1 var4) (= var0 var3)) (or (and (= var2 nullAddr) (= var8 1)) (and (not (= var2 nullAddr)) (= var8 0))))))) (inv_main1006_2 var1 var0 var0))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (inv_main1004_11 var1 var0))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (inv_main1004_256 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (inv_main1015_12 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (inv_main1016_12 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (inv_main1016_252 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (inv_main1023_11 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap)) (not (inv_main1035_13 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap)) (not (inv_main1036_13 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap)) (not (inv_main1037_13 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap)) (not (inv_main1042_12 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (inv_main1054_13 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (inv_main1055_13 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (inv_main1056_13 var2 var1 var0))))
(check-sat)