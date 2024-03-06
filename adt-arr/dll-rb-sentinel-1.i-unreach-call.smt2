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
(declare-fun inv_main1008_2 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main1032_12 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main1033_12 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main1034_12 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main1041_11 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main1042_11 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main1048_13 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main1049_13 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main998_2 (Heap) Bool)
(declare-fun inv_main_13 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main_32 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main_35 (Heap Addr Addr Addr) Bool)
(assert (forall ((var0 Heap)) (or (not (= var0 emptyHeap)) (inv_main998_2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main_13 var3 var2 var1 var0) (and (not (= var2 var0)) (and (= var2 (|TSLL::next| (getTSLL (read var3 var0)))) (= 1 (|TSLL::colour| (getTSLL (read var3 var0)))))))) (inv_main1008_2 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Heap) (var4 Addr) (var5 TSLL) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Heap) (var13 Addr) (var14 Addr) (var15 Heap) (var16 Addr) (var17 Addr) (var18 Addr) (var19 TSLL) (var20 Heap) (var21 Heap) (var22 Heap)) (or (not (and (inv_main998_2 var22) (and (and (and (and (and (and (and (= var21 (newHeap (alloc var20 (O_TSLL var19)))) (= var18 var17)) (= var16 (newAddr (alloc var20 (O_TSLL var19))))) (and (and (= var15 (write var21 var16 (O_TSLL (TSLL var18 (|TSLL::prev| (getTSLL (read var21 var16))) (|TSLL::colour| (getTSLL (read var21 var16))))))) (= var14 var18)) (= var13 var16))) (and (and (= var12 (write var15 var13 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var15 var13))) var14 (|TSLL::colour| (getTSLL (read var15 var13))))))) (= var11 var14)) (= var10 var13))) (and (and (= var9 (write var12 var10 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var12 var10))) (|TSLL::prev| (getTSLL (read var12 var10))) 1)))) (= var8 var11)) (= var7 var10))) (and (and (and (= var6 (newHeap (alloc var22 (O_TSLL var5)))) (= var4 (newAddr (alloc var22 (O_TSLL var5))))) (and (= var3 (write var6 var4 (O_TSLL (TSLL nullAddr (|TSLL::prev| (getTSLL (read var6 var4))) (|TSLL::colour| (getTSLL (read var6 var4))))))) (= var2 var4))) (and (= var1 (write var3 var2 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var3 var2))) nullAddr (|TSLL::colour| (getTSLL (read var3 var2))))))) (= var0 var2)))) (and (= var20 (write var1 var0 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var1 var0))) (|TSLL::prev| (getTSLL (read var1 var0))) 1)))) (= var17 var0))))) (inv_main1008_2 var9 var8 var7 var7))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main1008_2 var4 var3 var2 var1) (and (= var3 var2) (= var0 0)))) (inv_main1041_11 var4 var3 var2 var2))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main1008_2 var4 var3 var2 var1) (and (not (= 1 (|TSLL::colour| (getTSLL (read var4 var2))))) (and (not (= var3 var2)) (= var0 0))))) (inv_main1042_11 var4 var3 var2 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main_32 var3 var2 var1 var0) (= var2 var0))) (inv_main_35 var3 var2 var1 var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Heap) (var14 Heap) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Heap)) (or (not (and (inv_main_35 var18 var17 var16 var15) (and (and (and (and (and (and (and (= var14 var13) (= var12 var11)) (= var10 var9)) (= var8 var7)) (= var6 (|TSLL::next| (getTSLL (read var13 var7))))) (and (and (and (and (and (= var5 var18) (= var4 var17)) (= var3 var16)) (= var2 var15)) (= var1 (|TSLL::next| (getTSLL (read var18 var16))))) (and (= 0 (|TSLL::colour| (getTSLL (read var18 var16)))) (not (= var17 var16))))) (and (and (and (= var13 (write var5 var3 defObj)) (= var11 var4)) (= var9 var3)) (= var7 var1))) (= var0 (write var14 var8 defObj))))) (inv_main_35 var0 var12 var6 var8))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Heap)) (or (not (and (inv_main_35 var12 var11 var10 var9) (and (and (and (and (and (and (= var8 var12) (= var7 var11)) (= var6 var10)) (= var5 var9)) (= var4 (|TSLL::next| (getTSLL (read var12 var10))))) (and (not (= 0 (|TSLL::colour| (getTSLL (read var12 var10))))) (not (= var11 var10)))) (and (and (and (= var3 (write var8 var6 defObj)) (= var2 var7)) (= var1 var6)) (= var0 var4))))) (inv_main_35 var3 var2 var0 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main_32 var8 var7 var6 var5) (and (= var4 var3) (and (and (and (and (and (= var2 var8) (= var4 var7)) (= var1 var6)) (= var0 var5)) (= var3 (|TSLL::next| (getTSLL (read var8 var5))))) (and (= 0 (|TSLL::colour| (getTSLL (read var8 var5)))) (not (= var7 var5))))))) (inv_main1048_13 var2 var4 var1 var3))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main1008_2 var4 var3 var2 var1) (and (= 1 (|TSLL::colour| (getTSLL (read var4 var2)))) (and (not (= var3 var2)) (= var0 0))))) (inv_main_32 var4 var3 var2 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main_32 var8 var7 var6 var5) (and (and (and (and (and (= var4 var8) (= var3 var7)) (= var2 var6)) (= var1 var5)) (= var0 (|TSLL::next| (getTSLL (read var8 var5))))) (and (not (= 0 (|TSLL::colour| (getTSLL (read var8 var5))))) (not (= var7 var5)))))) (inv_main_32 var4 var3 var2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Heap)) (or (not (and (inv_main_32 var13 var12 var11 var10) (and (and (and (and (and (= var9 var8) (= var7 var6)) (= var5 var4)) (= var3 var2)) (= var1 (|TSLL::next| (getTSLL (read var8 var2))))) (and (not (= 1 (|TSLL::colour| (getTSLL (read var8 var2))))) (and (not (= var6 var2)) (and (and (and (and (and (= var8 var13) (= var6 var12)) (= var4 var11)) (= var0 var10)) (= var2 (|TSLL::next| (getTSLL (read var13 var10))))) (and (= 0 (|TSLL::colour| (getTSLL (read var13 var10)))) (not (= var12 var10))))))))) (inv_main_32 var9 var7 var5 var1))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap) (var9 Int) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 TSLL) (var15 Heap) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Heap) (var24 Heap) (var25 Int) (var26 Addr) (var27 Addr) (var28 Addr) (var29 Heap)) (or (not (and (inv_main1008_2 var29 var28 var27 var26) (and (and (not (= var25 0)) (and (and (and (and (and (and (and (= var24 var23) (= var22 var21)) (= var20 var19)) (= var18 var17)) (= var16 (|TSLL::next| (getTSLL (read var23 var17))))) (and (and (and (and (and (and (= var15 (newHeap (alloc var29 (O_TSLL var14)))) (= var13 var28)) (= var12 var27)) (= var11 var26)) (= var10 (newAddr (alloc var29 (O_TSLL var14))))) (not (= var9 0))) (and (and (and (= var8 (write var15 var11 (O_TSLL (TSLL var10 (|TSLL::prev| (getTSLL (read var15 var11))) (|TSLL::colour| (getTSLL (read var15 var11))))))) (= var7 var13)) (= var6 var12)) (= var5 var11)))) (and (and (and (= var23 (write var8 (|TSLL::next| (getTSLL (read var8 var5))) (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var8 (|TSLL::next| (getTSLL (read var8 var5)))))) var5 (|TSLL::colour| (getTSLL (read var8 (|TSLL::next| (getTSLL (read var8 var5)))))))))) (= var21 var7)) (= var19 var6)) (= var17 var5))) (and (and (and (= var4 (write var24 var16 (O_TSLL (TSLL var22 (|TSLL::prev| (getTSLL (read var24 var16))) (|TSLL::colour| (getTSLL (read var24 var16))))))) (= var3 var22)) (= var2 var20)) (= var1 var16)))) (= var0 (write var4 var1 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var4 var1))) (|TSLL::prev| (getTSLL (read var4 var1))) 1))))))) (inv_main_13 var0 var3 var2 var1))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Heap) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Heap) (var17 Int) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Addr) (var22 TSLL) (var23 Heap) (var24 Addr) (var25 Addr) (var26 Addr) (var27 Addr) (var28 Addr) (var29 Addr) (var30 Addr) (var31 Heap) (var32 Heap) (var33 Int) (var34 Addr) (var35 Addr) (var36 Addr) (var37 Addr) (var38 Addr) (var39 Addr) (var40 Addr) (var41 TSLL) (var42 Heap) (var43 Heap) (var44 Addr) (var45 Addr) (var46 Addr) (var47 Addr) (var48 Addr) (var49 Addr) (var50 Addr) (var51 Heap) (var52 Heap) (var53 Addr) (var54 Addr) (var55 Addr) (var56 Heap)) (or (not (and (inv_main1008_2 var56 var55 var54 var53) (and (and (and (and (and (and (and (and (= var52 var51) (= var50 var49)) (= var48 var47)) (= var46 var45)) (= var44 (|TSLL::next| (getTSLL (read var51 var45))))) (and (and (and (and (and (and (and (= var43 (newHeap (alloc var42 (O_TSLL var41)))) (= var40 var39)) (= var38 var37)) (= var36 var35)) (= var34 (newAddr (alloc var42 (O_TSLL var41))))) (and (= var33 0) (and (and (and (and (and (and (and (= var32 var31) (= var30 var29)) (= var28 var27)) (= var26 var25)) (= var24 (|TSLL::next| (getTSLL (read var31 var25))))) (and (and (and (and (and (and (= var23 (newHeap (alloc var56 (O_TSLL var22)))) (= var21 var55)) (= var20 var54)) (= var19 var53)) (= var18 (newAddr (alloc var56 (O_TSLL var22))))) (not (= var17 0))) (and (and (and (= var16 (write var23 var19 (O_TSLL (TSLL var18 (|TSLL::prev| (getTSLL (read var23 var19))) (|TSLL::colour| (getTSLL (read var23 var19))))))) (= var15 var21)) (= var14 var20)) (= var13 var19)))) (and (and (and (= var31 (write var16 (|TSLL::next| (getTSLL (read var16 var13))) (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var16 (|TSLL::next| (getTSLL (read var16 var13)))))) var13 (|TSLL::colour| (getTSLL (read var16 (|TSLL::next| (getTSLL (read var16 var13)))))))))) (= var29 var15)) (= var27 var14)) (= var25 var13))) (and (and (and (= var12 (write var32 var24 (O_TSLL (TSLL var30 (|TSLL::prev| (getTSLL (read var32 var24))) (|TSLL::colour| (getTSLL (read var32 var24))))))) (= var11 var30)) (= var10 var28)) (= var9 var24))))) (and (and (and (= var42 (write var12 var9 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var12 var9))) (|TSLL::prev| (getTSLL (read var12 var9))) 0)))) (= var39 var11)) (= var37 var10)) (= var35 var9))) (and (and (and (= var8 (write var43 var36 (O_TSLL (TSLL var34 (|TSLL::prev| (getTSLL (read var43 var36))) (|TSLL::colour| (getTSLL (read var43 var36))))))) (= var7 var40)) (= var6 var38)) (= var5 var36)))) (and (and (and (= var51 (write var8 (|TSLL::next| (getTSLL (read var8 var5))) (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var8 (|TSLL::next| (getTSLL (read var8 var5)))))) var5 (|TSLL::colour| (getTSLL (read var8 (|TSLL::next| (getTSLL (read var8 var5)))))))))) (= var49 var7)) (= var47 var6)) (= var45 var5))) (and (and (and (= var4 (write var52 var44 (O_TSLL (TSLL var50 (|TSLL::prev| (getTSLL (read var52 var44))) (|TSLL::colour| (getTSLL (read var52 var44))))))) (= var3 var50)) (= var2 var48)) (= var1 var44))) (= var0 (write var4 var1 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var4 var1))) (|TSLL::prev| (getTSLL (read var4 var1))) 1))))))) (inv_main_13 var0 var3 var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main_13 var3 var2 var1 var0) (and (= var2 var0) (and (= var2 (|TSLL::next| (getTSLL (read var3 var0)))) (= 1 (|TSLL::colour| (getTSLL (read var3 var0)))))))) (inv_main1034_12 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main_13 var3 var2 var1 var0) (not (= 1 (|TSLL::colour| (getTSLL (read var3 var0))))))) (inv_main1032_12 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main_32 var8 var7 var6 var5) (and (= 1 (|TSLL::colour| (getTSLL (read var4 var3)))) (and (not (= var2 var3)) (and (and (and (and (and (= var4 var8) (= var2 var7)) (= var1 var6)) (= var0 var5)) (= var3 (|TSLL::next| (getTSLL (read var8 var5))))) (and (= 0 (|TSLL::colour| (getTSLL (read var8 var5)))) (not (= var7 var5)))))))) (inv_main1049_13 var4 var2 var1 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main_13 var3 var2 var1 var0) (and (not (= var2 (|TSLL::next| (getTSLL (read var3 var0))))) (= 1 (|TSLL::colour| (getTSLL (read var3 var0))))))) (inv_main1033_12 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (inv_main1032_12 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (inv_main1033_12 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (inv_main1034_12 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (inv_main1041_11 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (inv_main1042_11 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (inv_main1048_13 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (inv_main1049_13 var3 var2 var1 var0))))
(check-sat)
