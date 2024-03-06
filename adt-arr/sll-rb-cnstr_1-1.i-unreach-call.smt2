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
                   ((TSLL (|TSLL::next| Addr) (|TSLL::colour| Int)))))
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
(declare-fun inv_main1006_2 (Heap) Bool)
(declare-fun inv_main1010_2 (Heap Addr Addr) Bool)
(declare-fun inv_main1038_11 (Heap Addr Addr) Bool)
(declare-fun inv_main1039_11 (Heap Addr Addr) Bool)
(declare-fun inv_main1046_13 (Heap Addr Addr) Bool)
(declare-fun inv_main1047_13 (Heap Addr Addr) Bool)
(declare-fun inv_main_17 (Heap Addr Addr) Bool)
(declare-fun inv_main_20 (Heap Addr Addr) Bool)
(assert (forall ((var0 Heap)) (or (not (= var0 emptyHeap)) (inv_main1006_2 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main1010_2 var6 var5 var4) (and (not (= 1 (|TSLL::colour| (getTSLL (read var3 var2))))) (and (not (= nullAddr var2)) (and (= var1 0) (and (and (= var3 var6) (= var2 var5)) (= var0 nullAddr))))))) (inv_main1039_11 var3 var2 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main_17 var6 var5 var4) (and (= nullAddr var3) (and (and (and (and (= var2 var6) (= var1 var5)) (= var0 var4)) (= var3 (|TSLL::next| (getTSLL (read var6 var4))))) (and (= 0 (|TSLL::colour| (getTSLL (read var6 var4)))) (not (= nullAddr var4))))))) (inv_main1046_13 var2 var1 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main_17 var6 var5 var4) (and (not (= 1 (|TSLL::colour| (getTSLL (read var3 var2))))) (and (not (= nullAddr var2)) (and (and (and (and (= var3 var6) (= var1 var5)) (= var0 var4)) (= var2 (|TSLL::next| (getTSLL (read var6 var4))))) (and (= 0 (|TSLL::colour| (getTSLL (read var6 var4)))) (not (= nullAddr var4)))))))) (inv_main1047_13 var3 var1 var2))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main1010_2 var6 var5 var4) (and (= 1 (|TSLL::colour| (getTSLL (read var3 var2)))) (and (not (= nullAddr var2)) (and (= var1 0) (and (and (= var3 var6) (= var2 var5)) (= var0 nullAddr))))))) (inv_main_17 var3 var2 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main_17 var6 var5 var4) (and (and (and (and (= var3 var6) (= var2 var5)) (= var1 var4)) (= var0 (|TSLL::next| (getTSLL (read var6 var4))))) (and (not (= 0 (|TSLL::colour| (getTSLL (read var6 var4))))) (not (= nullAddr var4)))))) (inv_main_17 var3 var2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main_17 var10 var9 var8) (and (and (and (and (= var7 var6) (= var5 var4)) (= var3 var2)) (= var1 (|TSLL::next| (getTSLL (read var6 var2))))) (and (= 1 (|TSLL::colour| (getTSLL (read var6 var2)))) (and (not (= nullAddr var2)) (and (and (and (and (= var6 var10) (= var4 var9)) (= var0 var8)) (= var2 (|TSLL::next| (getTSLL (read var10 var8))))) (and (= 0 (|TSLL::colour| (getTSLL (read var10 var8)))) (not (= nullAddr var8))))))))) (inv_main_17 var7 var5 var1))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr) (var7 Addr) (var8 TSLL) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Heap) (var16 Heap) (var17 Int) (var18 Addr) (var19 Addr) (var20 Heap)) (or (not (and (inv_main1010_2 var20 var19 var18) (and (and (not (= var17 0)) (and (and (and (and (and (and (= var16 var15) (= var14 var13)) (= var12 var11)) (= var10 (|TSLL::next| (getTSLL (read var15 var11))))) (and (and (and (and (= var9 (newHeap (alloc var20 (O_TSLL var8)))) (= var7 var19)) (= var6 var18)) (= var5 (newAddr (alloc var20 (O_TSLL var8))))) (not (= var4 0)))) (and (and (= var15 (write var9 var6 (O_TSLL (TSLL var5 (|TSLL::colour| (getTSLL (read var9 var6))))))) (= var13 var7)) (= var11 var6))) (and (and (= var3 (write var16 var10 (O_TSLL (TSLL nullAddr (|TSLL::colour| (getTSLL (read var16 var10))))))) (= var2 var14)) (= var1 var10)))) (= var0 (write var3 var1 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var3 var1))) 1))))))) (inv_main1010_2 var0 var2 var1))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Int) (var8 Addr) (var9 Addr) (var10 Addr) (var11 TSLL) (var12 Heap) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Heap) (var19 Heap) (var20 Int) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Addr) (var25 Addr) (var26 TSLL) (var27 Heap) (var28 Heap) (var29 Addr) (var30 Addr) (var31 Addr) (var32 Addr) (var33 Addr) (var34 Heap) (var35 Heap) (var36 Addr) (var37 Addr) (var38 Heap)) (or (not (and (inv_main1010_2 var38 var37 var36) (and (and (and (and (and (and (and (= var35 var34) (= var33 var32)) (= var31 var30)) (= var29 (|TSLL::next| (getTSLL (read var34 var30))))) (and (and (and (and (and (= var28 (newHeap (alloc var27 (O_TSLL var26)))) (= var25 var24)) (= var23 var22)) (= var21 (newAddr (alloc var27 (O_TSLL var26))))) (and (= var20 0) (and (and (and (and (and (and (= var19 var18) (= var17 var16)) (= var15 var14)) (= var13 (|TSLL::next| (getTSLL (read var18 var14))))) (and (and (and (and (= var12 (newHeap (alloc var38 (O_TSLL var11)))) (= var10 var37)) (= var9 var36)) (= var8 (newAddr (alloc var38 (O_TSLL var11))))) (not (= var7 0)))) (and (and (= var18 (write var12 var9 (O_TSLL (TSLL var8 (|TSLL::colour| (getTSLL (read var12 var9))))))) (= var16 var10)) (= var14 var9))) (and (and (= var6 (write var19 var13 (O_TSLL (TSLL nullAddr (|TSLL::colour| (getTSLL (read var19 var13))))))) (= var5 var17)) (= var4 var13))))) (and (and (= var27 (write var6 var4 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var6 var4))) 0)))) (= var24 var5)) (= var22 var4)))) (and (and (= var34 (write var28 var23 (O_TSLL (TSLL var21 (|TSLL::colour| (getTSLL (read var28 var23))))))) (= var32 var25)) (= var30 var23))) (and (and (= var3 (write var35 var29 (O_TSLL (TSLL nullAddr (|TSLL::colour| (getTSLL (read var35 var29))))))) (= var2 var33)) (= var1 var29))) (= var0 (write var3 var1 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var3 var1))) 1))))))) (inv_main1010_2 var0 var2 var1))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Heap) (var4 Addr) (var5 TSLL) (var6 Heap) (var7 Heap)) (or (not (and (inv_main1006_2 var7) (and (and (and (= var6 (newHeap (alloc var7 (O_TSLL var5)))) (= var4 (newAddr (alloc var7 (O_TSLL var5))))) (and (= var3 (write var6 var4 (O_TSLL (TSLL nullAddr (|TSLL::colour| (getTSLL (read var6 var4))))))) (= var2 var4))) (and (= var1 (write var3 var2 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var3 var2))) 1)))) (= var0 var2))))) (inv_main1010_2 var1 var0 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (and (inv_main_17 var2 var1 var0) (= nullAddr var0))) (inv_main_20 var2 var1 var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap) (var11 Heap) (var12 Addr) (var13 Addr) (var14 Heap)) (or (not (and (inv_main_20 var14 var13 var12) (and (and (and (and (and (and (= var11 var10) (= var9 var8)) (= var7 var6)) (= var5 (|TSLL::next| (getTSLL (read var10 var6))))) (and (and (and (and (= var4 var14) (= var3 var13)) (= var2 var12)) (= var1 (|TSLL::next| (getTSLL (read var14 var13))))) (and (= 0 (|TSLL::colour| (getTSLL (read var14 var13)))) (not (= nullAddr var13))))) (and (and (= var10 (write var4 var3 defObj)) (= var8 var3)) (= var6 var1))) (= var0 (write var11 var7 defObj))))) (inv_main_20 var0 var5 var7))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main_20 var9 var8 var7) (and (and (and (and (and (= var6 var9) (= var5 var8)) (= var4 var7)) (= var3 (|TSLL::next| (getTSLL (read var9 var8))))) (and (not (= 0 (|TSLL::colour| (getTSLL (read var9 var8))))) (not (= nullAddr var8)))) (and (and (= var2 (write var6 var5 defObj)) (= var1 var5)) (= var0 var3))))) (inv_main_20 var2 var0 var0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main1010_2 var6 var5 var4) (and (= nullAddr var3) (and (= var2 0) (and (and (= var1 var6) (= var3 var5)) (= var0 nullAddr)))))) (inv_main1038_11 var1 var3 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (inv_main1038_11 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (inv_main1039_11 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (inv_main1046_13 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (inv_main1047_13 var2 var1 var0))))
(check-sat)
