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
                   ((TSLL (|TSLL::next| Addr) (|TSLL::prev| Addr) (|TSLL::colour| Int)))))
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
(declare-fun inv_main1005_2 (Heap) Bool)
(declare-fun inv_main1010_2 (Heap Addr Addr) Bool)
(declare-fun inv_main1040_11 (Heap Addr Addr) Bool)
(declare-fun inv_main1041_11 (Heap Addr Addr) Bool)
(declare-fun inv_main1051_12 (Heap Addr Addr) Bool)
(declare-fun inv_main_20 (Heap Addr Addr) Bool)
(declare-fun inv_main_23 (Heap Addr Addr) Bool)
(assert (forall ((var0 Heap)) (or (not (= var0 emptyHeap)) (inv_main1005_2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (and (inv_main_20 var2 var1 var0) (and (= (|TSLL::next| (getTSLL (read var2 var0))) nullAddr) (and (not (= 0 (|TSLL::colour| (getTSLL (read var2 var0))))) (not (= nullAddr var0)))))) (inv_main1051_12 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main_20 var10 var9 var8) (and (= (|TSLL::next| (getTSLL (read var7 var6))) nullAddr) (and (and (and (and (= var7 var5) (= var4 var3)) (= var2 var1)) (= var6 (|TSLL::next| (getTSLL (read var5 var1))))) (and (and (and (and (= var5 var10) (= var3 var9)) (= var0 var8)) (= var1 (|TSLL::next| (getTSLL (read var10 var8))))) (and (= 0 (|TSLL::colour| (getTSLL (read var10 var8)))) (not (= nullAddr var8)))))))) (inv_main1051_12 var7 var4 var6))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main1010_2 var6 var5 var4) (and (= nullAddr var3) (and (= var2 0) (and (and (= var1 var6) (= var3 var5)) (= var0 nullAddr)))))) (inv_main1040_11 var1 var3 var3))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main1010_2 var6 var5 var4) (and (not (= 1 (|TSLL::colour| (getTSLL (read var3 var2))))) (and (not (= nullAddr var2)) (and (= var1 0) (and (and (= var3 var6) (= var2 var5)) (= var0 nullAddr))))))) (inv_main1041_11 var3 var2 var2))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Int) (var8 Addr) (var9 Addr) (var10 Addr) (var11 TSLL) (var12 Heap) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Heap) (var19 Heap) (var20 Int) (var21 Addr) (var22 Addr) (var23 Heap)) (or (not (and (inv_main1010_2 var23 var22 var21) (and (and (not (= var20 0)) (and (and (and (and (and (and (= var19 var18) (= var17 var16)) (= var15 var14)) (= var13 (|TSLL::next| (getTSLL (read var18 var14))))) (and (and (and (and (and (= var12 (newHeap (alloc var23 (O_TSLL var11)))) (= var10 var22)) (= var9 var21)) (= var8 (newAddr (alloc var23 (O_TSLL var11))))) (not (= var7 0))) (and (and (= var6 (write var12 var9 (O_TSLL (TSLL var8 (|TSLL::prev| (getTSLL (read var12 var9))) (|TSLL::colour| (getTSLL (read var12 var9))))))) (= var5 var10)) (= var4 var9)))) (and (and (= var18 (write var6 (|TSLL::next| (getTSLL (read var6 var4))) (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var6 (|TSLL::next| (getTSLL (read var6 var4)))))) var4 (|TSLL::colour| (getTSLL (read var6 (|TSLL::next| (getTSLL (read var6 var4)))))))))) (= var16 var5)) (= var14 var4))) (and (and (= var3 (write var19 var13 (O_TSLL (TSLL nullAddr (|TSLL::prev| (getTSLL (read var19 var13))) (|TSLL::colour| (getTSLL (read var19 var13))))))) (= var2 var17)) (= var1 var13)))) (= var0 (write var3 var1 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var3 var1))) (|TSLL::prev| (getTSLL (read var3 var1))) 1))))))) (inv_main1010_2 var0 var2 var1))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Heap) (var13 Int) (var14 Addr) (var15 Addr) (var16 Addr) (var17 TSLL) (var18 Heap) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Heap) (var25 Heap) (var26 Int) (var27 Addr) (var28 Addr) (var29 Addr) (var30 Addr) (var31 Addr) (var32 TSLL) (var33 Heap) (var34 Heap) (var35 Addr) (var36 Addr) (var37 Addr) (var38 Addr) (var39 Addr) (var40 Heap) (var41 Heap) (var42 Addr) (var43 Addr) (var44 Heap)) (or (not (and (inv_main1010_2 var44 var43 var42) (and (and (and (and (and (and (and (= var41 var40) (= var39 var38)) (= var37 var36)) (= var35 (|TSLL::next| (getTSLL (read var40 var36))))) (and (and (and (and (and (and (= var34 (newHeap (alloc var33 (O_TSLL var32)))) (= var31 var30)) (= var29 var28)) (= var27 (newAddr (alloc var33 (O_TSLL var32))))) (and (= var26 0) (and (and (and (and (and (and (= var25 var24) (= var23 var22)) (= var21 var20)) (= var19 (|TSLL::next| (getTSLL (read var24 var20))))) (and (and (and (and (and (= var18 (newHeap (alloc var44 (O_TSLL var17)))) (= var16 var43)) (= var15 var42)) (= var14 (newAddr (alloc var44 (O_TSLL var17))))) (not (= var13 0))) (and (and (= var12 (write var18 var15 (O_TSLL (TSLL var14 (|TSLL::prev| (getTSLL (read var18 var15))) (|TSLL::colour| (getTSLL (read var18 var15))))))) (= var11 var16)) (= var10 var15)))) (and (and (= var24 (write var12 (|TSLL::next| (getTSLL (read var12 var10))) (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var12 (|TSLL::next| (getTSLL (read var12 var10)))))) var10 (|TSLL::colour| (getTSLL (read var12 (|TSLL::next| (getTSLL (read var12 var10)))))))))) (= var22 var11)) (= var20 var10))) (and (and (= var9 (write var25 var19 (O_TSLL (TSLL nullAddr (|TSLL::prev| (getTSLL (read var25 var19))) (|TSLL::colour| (getTSLL (read var25 var19))))))) (= var8 var23)) (= var7 var19))))) (and (and (= var33 (write var9 var7 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var9 var7))) (|TSLL::prev| (getTSLL (read var9 var7))) 0)))) (= var30 var8)) (= var28 var7))) (and (and (= var6 (write var34 var29 (O_TSLL (TSLL var27 (|TSLL::prev| (getTSLL (read var34 var29))) (|TSLL::colour| (getTSLL (read var34 var29))))))) (= var5 var31)) (= var4 var29)))) (and (and (= var40 (write var6 (|TSLL::next| (getTSLL (read var6 var4))) (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var6 (|TSLL::next| (getTSLL (read var6 var4)))))) var4 (|TSLL::colour| (getTSLL (read var6 (|TSLL::next| (getTSLL (read var6 var4)))))))))) (= var38 var5)) (= var36 var4))) (and (and (= var3 (write var41 var35 (O_TSLL (TSLL nullAddr (|TSLL::prev| (getTSLL (read var41 var35))) (|TSLL::colour| (getTSLL (read var41 var35))))))) (= var2 var39)) (= var1 var35))) (= var0 (write var3 var1 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var3 var1))) (|TSLL::prev| (getTSLL (read var3 var1))) 1))))))) (inv_main1010_2 var0 var2 var1))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Heap) (var6 Addr) (var7 TSLL) (var8 Heap) (var9 Heap)) (or (not (and (inv_main1005_2 var9) (and (and (and (and (= var8 (newHeap (alloc var9 (O_TSLL var7)))) (= var6 (newAddr (alloc var9 (O_TSLL var7))))) (and (= var5 (write var8 var6 (O_TSLL (TSLL nullAddr (|TSLL::prev| (getTSLL (read var8 var6))) (|TSLL::colour| (getTSLL (read var8 var6))))))) (= var4 var6))) (and (= var3 (write var5 var4 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var5 var4))) nullAddr (|TSLL::colour| (getTSLL (read var5 var4))))))) (= var2 var4))) (and (= var1 (write var3 var2 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var3 var2))) (|TSLL::prev| (getTSLL (read var3 var2))) 1)))) (= var0 var2))))) (inv_main1010_2 var1 var0 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (and (inv_main_20 var2 var1 var0) (= nullAddr var0))) (inv_main_23 var2 var1 var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap) (var11 Heap) (var12 Addr) (var13 Addr) (var14 Heap)) (or (not (and (inv_main_23 var14 var13 var12) (and (and (and (and (and (and (= var11 var10) (= var9 var8)) (= var7 var6)) (= var5 (|TSLL::next| (getTSLL (read var10 var6))))) (and (and (and (and (= var4 var14) (= var3 var13)) (= var2 var12)) (= var1 (|TSLL::next| (getTSLL (read var14 var13))))) (and (= 0 (|TSLL::colour| (getTSLL (read var14 var13)))) (not (= nullAddr var13))))) (and (and (= var10 (write var4 var3 defObj)) (= var8 var3)) (= var6 var1))) (= var0 (write var11 var7 defObj))))) (inv_main_23 var0 var5 var7))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main_23 var9 var8 var7) (and (and (and (and (and (= var6 var9) (= var5 var8)) (= var4 var7)) (= var3 (|TSLL::next| (getTSLL (read var9 var8))))) (and (not (= 0 (|TSLL::colour| (getTSLL (read var9 var8))))) (not (= nullAddr var8)))) (and (and (= var2 (write var6 var5 defObj)) (= var1 var5)) (= var0 var3))))) (inv_main_23 var2 var0 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main1010_2 var6 var5 var4) (and (= 1 (|TSLL::colour| (getTSLL (read var3 var2)))) (and (not (= nullAddr var2)) (and (= var1 0) (and (and (= var3 var6) (= var2 var5)) (= var0 nullAddr))))))) (inv_main_20 var3 var2 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main_20 var6 var5 var4) (and (and (and (and (and (= var3 var6) (= var2 var5)) (= var1 var4)) (= var0 (|TSLL::next| (getTSLL (read var6 var4))))) (not (= (|TSLL::next| (getTSLL (read var6 var4))) nullAddr))) (and (not (= 0 (|TSLL::colour| (getTSLL (read var6 var4))))) (not (= nullAddr var4)))))) (inv_main_20 var3 var2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap) (var11 Heap) (var12 Addr) (var13 Addr) (var14 Heap)) (or (not (and (inv_main_20 var14 var13 var12) (and (and (and (and (and (= var11 var10) (= var9 var8)) (= var7 var6)) (= var5 (|TSLL::next| (getTSLL (read var10 var6))))) (not (= (|TSLL::next| (getTSLL (read var10 var6))) nullAddr))) (and (and (and (and (= var10 var4) (= var8 var3)) (= var2 var1)) (= var6 (|TSLL::next| (getTSLL (read var4 var1))))) (and (and (and (and (= var4 var14) (= var3 var13)) (= var0 var12)) (= var1 (|TSLL::next| (getTSLL (read var14 var12))))) (and (= 0 (|TSLL::colour| (getTSLL (read var14 var12)))) (not (= nullAddr var12)))))))) (inv_main_20 var11 var9 var5))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (inv_main1040_11 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (inv_main1041_11 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (inv_main1051_12 var2 var1 var0))))
(check-sat)
