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
(declare-fun inv_main1005_2 (Heap) Bool)
(declare-fun inv_main1013_2 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main1041_11 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main1042_11 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main1049_13 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main1050_13 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main_19 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main_22 (Heap Addr Addr Addr) Bool)
(assert (forall ((var0 Heap)) (or (not (= var0 emptyHeap)) (inv_main1005_2 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main1013_2 var4 var3 var2 var1) (and (not (= 1 (|TSLL::colour| (getTSLL (read var4 var2))))) (and (not (= var3 var2)) (= var0 0))))) (inv_main1042_11 var4 var3 var2 var2))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Int) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 TSLL) (var11 Heap) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Heap) (var20 Heap) (var21 Int) (var22 Addr) (var23 Addr) (var24 Addr) (var25 Heap)) (or (not (and (inv_main1013_2 var25 var24 var23 var22) (and (and (not (= var21 0)) (and (and (and (and (and (and (and (= var20 var19) (= var18 var17)) (= var16 var15)) (= var14 var13)) (= var12 (|TSLL::next| (getTSLL (read var19 var13))))) (and (and (and (and (and (= var11 (newHeap (alloc var25 (O_TSLL var10)))) (= var9 var24)) (= var8 var23)) (= var7 var22)) (= var6 (newAddr (alloc var25 (O_TSLL var10))))) (not (= var5 0)))) (and (and (and (= var19 (write var11 var7 (O_TSLL (TSLL var6 (|TSLL::colour| (getTSLL (read var11 var7))))))) (= var17 var9)) (= var15 var8)) (= var13 var7))) (and (and (and (= var4 (write var20 var12 (O_TSLL (TSLL var18 (|TSLL::colour| (getTSLL (read var20 var12))))))) (= var3 var18)) (= var2 var16)) (= var1 var12)))) (= var0 (write var4 var1 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var4 var1))) 1))))))) (inv_main1013_2 var0 var3 var2 var1))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap) (var9 Int) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 TSLL) (var15 Heap) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Heap) (var24 Heap) (var25 Int) (var26 Addr) (var27 Addr) (var28 Addr) (var29 Addr) (var30 Addr) (var31 Addr) (var32 Addr) (var33 TSLL) (var34 Heap) (var35 Heap) (var36 Addr) (var37 Addr) (var38 Addr) (var39 Addr) (var40 Addr) (var41 Addr) (var42 Addr) (var43 Heap) (var44 Heap) (var45 Addr) (var46 Addr) (var47 Addr) (var48 Heap)) (or (not (and (inv_main1013_2 var48 var47 var46 var45) (and (and (and (and (and (and (and (and (= var44 var43) (= var42 var41)) (= var40 var39)) (= var38 var37)) (= var36 (|TSLL::next| (getTSLL (read var43 var37))))) (and (and (and (and (and (and (= var35 (newHeap (alloc var34 (O_TSLL var33)))) (= var32 var31)) (= var30 var29)) (= var28 var27)) (= var26 (newAddr (alloc var34 (O_TSLL var33))))) (and (= var25 0) (and (and (and (and (and (and (and (= var24 var23) (= var22 var21)) (= var20 var19)) (= var18 var17)) (= var16 (|TSLL::next| (getTSLL (read var23 var17))))) (and (and (and (and (and (= var15 (newHeap (alloc var48 (O_TSLL var14)))) (= var13 var47)) (= var12 var46)) (= var11 var45)) (= var10 (newAddr (alloc var48 (O_TSLL var14))))) (not (= var9 0)))) (and (and (and (= var23 (write var15 var11 (O_TSLL (TSLL var10 (|TSLL::colour| (getTSLL (read var15 var11))))))) (= var21 var13)) (= var19 var12)) (= var17 var11))) (and (and (and (= var8 (write var24 var16 (O_TSLL (TSLL var22 (|TSLL::colour| (getTSLL (read var24 var16))))))) (= var7 var22)) (= var6 var20)) (= var5 var16))))) (and (and (and (= var34 (write var8 var5 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var8 var5))) 0)))) (= var31 var7)) (= var29 var6)) (= var27 var5)))) (and (and (and (= var43 (write var35 var28 (O_TSLL (TSLL var26 (|TSLL::colour| (getTSLL (read var35 var28))))))) (= var41 var32)) (= var39 var30)) (= var37 var28))) (and (and (and (= var4 (write var44 var36 (O_TSLL (TSLL var42 (|TSLL::colour| (getTSLL (read var44 var36))))))) (= var3 var42)) (= var2 var40)) (= var1 var36))) (= var0 (write var4 var1 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var4 var1))) 1))))))) (inv_main1013_2 var0 var3 var2 var1))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 TSLL) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Heap) (var11 Addr) (var12 Addr) (var13 Addr) (var14 TSLL) (var15 Heap) (var16 Heap) (var17 Heap)) (or (not (and (inv_main1005_2 var17) (and (and (and (and (and (and (= var16 (newHeap (alloc var15 (O_TSLL var14)))) (= var13 var12)) (= var11 (newAddr (alloc var15 (O_TSLL var14))))) (and (and (= var10 (write var16 var11 (O_TSLL (TSLL var13 (|TSLL::colour| (getTSLL (read var16 var11))))))) (= var9 var13)) (= var8 var11))) (and (and (= var7 (write var10 var8 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var10 var8))) 1)))) (= var6 var9)) (= var5 var8))) (and (and (= var4 (newHeap (alloc var17 (O_TSLL var3)))) (= var2 (newAddr (alloc var17 (O_TSLL var3))))) (and (= var1 (write var4 var2 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var4 var2))) 1)))) (= var0 var2)))) (and (= var15 (write var1 var0 (O_TSLL (TSLL nullAddr (|TSLL::colour| (getTSLL (read var1 var0))))))) (= var12 var0))))) (inv_main1013_2 var7 var6 var5 var5))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main_19 var8 var7 var6 var5) (and (= var4 var3) (and (and (and (and (and (= var2 var8) (= var4 var7)) (= var1 var6)) (= var0 var5)) (= var3 (|TSLL::next| (getTSLL (read var8 var5))))) (and (= 0 (|TSLL::colour| (getTSLL (read var8 var5)))) (not (= var7 var5))))))) (inv_main1049_13 var2 var4 var1 var3))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main1013_2 var4 var3 var2 var1) (and (= 1 (|TSLL::colour| (getTSLL (read var4 var2)))) (and (not (= var3 var2)) (= var0 0))))) (inv_main_19 var4 var3 var2 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main_19 var8 var7 var6 var5) (and (and (and (and (and (= var4 var8) (= var3 var7)) (= var2 var6)) (= var1 var5)) (= var0 (|TSLL::next| (getTSLL (read var8 var5))))) (and (not (= 0 (|TSLL::colour| (getTSLL (read var8 var5))))) (not (= var7 var5)))))) (inv_main_19 var4 var3 var2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Heap)) (or (not (and (inv_main_19 var13 var12 var11 var10) (and (and (and (and (and (= var9 var8) (= var7 var6)) (= var5 var4)) (= var3 var2)) (= var1 (|TSLL::next| (getTSLL (read var8 var2))))) (and (not (= 1 (|TSLL::colour| (getTSLL (read var8 var2))))) (and (not (= var6 var2)) (and (and (and (and (and (= var8 var13) (= var6 var12)) (= var4 var11)) (= var0 var10)) (= var2 (|TSLL::next| (getTSLL (read var13 var10))))) (and (= 0 (|TSLL::colour| (getTSLL (read var13 var10)))) (not (= var12 var10))))))))) (inv_main_19 var9 var7 var5 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main1013_2 var4 var3 var2 var1) (and (= var3 var2) (= var0 0)))) (inv_main1041_11 var4 var3 var2 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main_19 var8 var7 var6 var5) (and (= 1 (|TSLL::colour| (getTSLL (read var4 var3)))) (and (not (= var2 var3)) (and (and (and (and (and (= var4 var8) (= var2 var7)) (= var1 var6)) (= var0 var5)) (= var3 (|TSLL::next| (getTSLL (read var8 var5))))) (and (= 0 (|TSLL::colour| (getTSLL (read var8 var5)))) (not (= var7 var5)))))))) (inv_main1050_13 var4 var2 var1 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main_19 var3 var2 var1 var0) (= var2 var0))) (inv_main_22 var3 var2 var1 var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Heap) (var14 Heap) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Heap)) (or (not (and (inv_main_22 var18 var17 var16 var15) (and (and (and (and (and (and (and (= var14 var13) (= var12 var11)) (= var10 var9)) (= var8 var7)) (= var6 (|TSLL::next| (getTSLL (read var13 var7))))) (and (and (and (and (and (= var5 var18) (= var4 var17)) (= var3 var16)) (= var2 var15)) (= var1 (|TSLL::next| (getTSLL (read var18 var16))))) (and (= 0 (|TSLL::colour| (getTSLL (read var18 var16)))) (not (= var17 var16))))) (and (and (and (= var13 (write var5 var3 defObj)) (= var11 var4)) (= var9 var3)) (= var7 var1))) (= var0 (write var14 var8 defObj))))) (inv_main_22 var0 var12 var6 var8))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Heap)) (or (not (and (inv_main_22 var12 var11 var10 var9) (and (and (and (and (and (and (= var8 var12) (= var7 var11)) (= var6 var10)) (= var5 var9)) (= var4 (|TSLL::next| (getTSLL (read var12 var10))))) (and (not (= 0 (|TSLL::colour| (getTSLL (read var12 var10))))) (not (= var11 var10)))) (and (and (and (= var3 (write var8 var6 defObj)) (= var2 var7)) (= var1 var6)) (= var0 var4))))) (inv_main_22 var3 var2 var0 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (inv_main1041_11 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (inv_main1042_11 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (inv_main1049_13 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (inv_main1050_13 var3 var2 var1 var0))))
(check-sat)
