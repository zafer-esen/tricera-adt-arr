(set-logic HORN)
(set-info :source |
    Benchmark: C_VC
    Output by Princess (http://www.philipp.ruemmer.org/princess.shtml)
|)
(set-info :status unknown)
(declare-datatype bool ((true) (false)))
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
(declare-fun inv_exit (Heap Addr) Bool)
(declare-fun inv_main1006_2 (Heap Addr) Bool)
(declare-fun inv_main1010_2 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main1071_9 (Heap Addr Int) Bool)
(declare-fun inv_main_17 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main_20 (Heap Addr Addr Addr) Bool)
(assert (forall ((var0 Addr) (var1 Heap)) (or (not (and (= var1 emptyHeap) (= var0 nullAddr))) (inv_main1006_2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main_17 var3 var2 var1 var0) (= nullAddr var0))) (inv_main_20 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Heap) (var15 Heap) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Heap)) (or (not (and (inv_main_20 var19 var18 var17 var16) (and (and (and (and (and (and (and (and (= var15 var14) (= var13 var12)) (= var11 var10)) (= var9 var8)) (= var7 (|TSLL::next| (getTSLL (read var14 var8))))) (and (and (and (and (and (= var6 var19) (= var5 var18)) (= var4 var17)) (= var3 var16)) (= var2 (|TSLL::next| (getTSLL (read var19 var17))))) (and (= 0 (|TSLL::colour| (getTSLL (read var19 var17)))) (not (= nullAddr var17))))) (and (and (and (= var14 (write var6 var4 defObj)) (or (and (= var5 var4) (= var12 nullAddr)) (and (not (= var5 var4)) (= var12 var5)))) (= var10 var4)) (= var8 var2))) (= var1 (write var15 var9 defObj))) (or (and (= var13 var9) (= var0 nullAddr)) (and (not (= var13 var9)) (= var0 var13)))))) (inv_main_20 var1 var0 var7 var9))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Heap)) (or (not (and (inv_main_20 var12 var11 var10 var9) (and (and (and (and (and (and (= var8 var12) (= var7 var11)) (= var6 var10)) (= var5 var9)) (= var4 (|TSLL::next| (getTSLL (read var12 var10))))) (and (not (= 0 (|TSLL::colour| (getTSLL (read var12 var10))))) (not (= nullAddr var10)))) (and (and (and (= var3 (write var8 var6 defObj)) (or (and (= var7 var6) (= var2 nullAddr)) (and (not (= var7 var6)) (= var2 var7)))) (= var1 var6)) (= var0 var4))))) (inv_main_20 var3 var2 var0 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Int) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main1010_2 var8 var7 var6 var5) (and (= nullAddr var4) (and (= var3 0) (and (and (and (= var2 var8) (= var1 var7)) (= var4 var6)) (= var0 nullAddr)))))) (inv_exit var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main1010_2 var8 var7 var6 var5) (and (not (= 1 (|TSLL::colour| (getTSLL (read var4 var3))))) (and (not (= nullAddr var3)) (and (= var2 0) (and (and (and (= var4 var8) (= var1 var7)) (= var3 var6)) (= var0 nullAddr))))))) (inv_exit var4 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main_17 var3 var2 var1 var0) (and (= (|TSLL::next| (getTSLL (read var3 var0))) nullAddr) (and (not (= 0 (|TSLL::colour| (getTSLL (read var3 var0))))) (not (= nullAddr var0)))))) (inv_exit var3 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Heap)) (or (not (and (inv_main_17 var13 var12 var11 var10) (and (= (|TSLL::next| (getTSLL (read var9 var8))) nullAddr) (and (and (and (and (and (= var9 var7) (= var6 var5)) (= var4 var3)) (= var2 var1)) (= var8 (|TSLL::next| (getTSLL (read var7 var1))))) (and (and (and (and (and (= var7 var13) (= var5 var12)) (= var3 var11)) (= var0 var10)) (= var1 (|TSLL::next| (getTSLL (read var13 var10))))) (and (= 0 (|TSLL::colour| (getTSLL (read var13 var10)))) (not (= nullAddr var10)))))))) (inv_exit var9 var6))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main_20 var4 var3 var2 var1) (and (= nullAddr var2) (= var0 0)))) (inv_main1071_9 var4 var3 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main1010_2 var8 var7 var6 var5) (and (= 1 (|TSLL::colour| (getTSLL (read var4 var3)))) (and (not (= nullAddr var3)) (and (= var2 0) (and (and (and (= var4 var8) (= var1 var7)) (= var3 var6)) (= var0 nullAddr))))))) (inv_main_17 var4 var1 var3 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main_17 var8 var7 var6 var5) (and (and (and (and (and (and (= var4 var8) (= var3 var7)) (= var2 var6)) (= var1 var5)) (= var0 (|TSLL::next| (getTSLL (read var8 var5))))) (not (= (|TSLL::next| (getTSLL (read var8 var5))) nullAddr))) (and (not (= 0 (|TSLL::colour| (getTSLL (read var8 var5))))) (not (= nullAddr var5)))))) (inv_main_17 var4 var3 var2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Heap) (var14 Heap) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Heap)) (or (not (and (inv_main_17 var18 var17 var16 var15) (and (and (and (and (and (and (= var14 var13) (= var12 var11)) (= var10 var9)) (= var8 var7)) (= var6 (|TSLL::next| (getTSLL (read var13 var7))))) (not (= (|TSLL::next| (getTSLL (read var13 var7))) nullAddr))) (and (and (and (and (and (= var13 var5) (= var11 var4)) (= var9 var3)) (= var2 var1)) (= var7 (|TSLL::next| (getTSLL (read var5 var1))))) (and (and (and (and (and (= var5 var18) (= var4 var17)) (= var3 var16)) (= var0 var15)) (= var1 (|TSLL::next| (getTSLL (read var18 var15))))) (and (= 0 (|TSLL::colour| (getTSLL (read var18 var15)))) (not (= nullAddr var15)))))))) (inv_main_17 var14 var12 var10 var6))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Int) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Bool) (var10 Addr) (var11 TSLL) (var12 Heap) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Heap) (var21 Heap) (var22 Int) (var23 Addr) (var24 Addr) (var25 Addr) (var26 Heap)) (or (not (and (inv_main1010_2 var26 var25 var24 var23) (and (and (not (= var22 0)) (and (and (and (and (and (and (and (= var21 var20) (= var19 var18)) (= var17 var16)) (= var15 var14)) (= var13 (|TSLL::next| (getTSLL (read var20 var14))))) (and (and (and (and (and (= var12 (newHeap (alloc var26 (O_TSLL var11)))) (or (and var9 (= var10 (newAddr (alloc var26 (O_TSLL var11))))) (and (not var9) (= var10 var25)))) (= var8 var24)) (= var7 var23)) (= var6 (newAddr (alloc var26 (O_TSLL var11))))) (not (= var5 0)))) (and (and (and (= var20 (write var12 var7 (O_TSLL (TSLL var6 (|TSLL::colour| (getTSLL (read var12 var7))))))) (= var18 var10)) (= var16 var8)) (= var14 var7))) (and (and (and (= var4 (write var21 var13 (O_TSLL (TSLL nullAddr (|TSLL::colour| (getTSLL (read var21 var13))))))) (= var3 var19)) (= var2 var17)) (= var1 var13)))) (= var0 (write var4 var1 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var4 var1))) 1))))))) (inv_main1010_2 var0 var3 var2 var1))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap) (var9 Int) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Bool) (var14 Addr) (var15 TSLL) (var16 Heap) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Heap) (var25 Heap) (var26 Int) (var27 Addr) (var28 Addr) (var29 Addr) (var30 Addr) (var31 Addr) (var32 Addr) (var33 Bool) (var34 Addr) (var35 TSLL) (var36 Heap) (var37 Heap) (var38 Addr) (var39 Addr) (var40 Addr) (var41 Addr) (var42 Addr) (var43 Addr) (var44 Addr) (var45 Heap) (var46 Heap) (var47 Addr) (var48 Addr) (var49 Addr) (var50 Heap)) (or (not (and (inv_main1010_2 var50 var49 var48 var47) (and (and (and (and (and (and (and (and (= var46 var45) (= var44 var43)) (= var42 var41)) (= var40 var39)) (= var38 (|TSLL::next| (getTSLL (read var45 var39))))) (and (and (and (and (and (and (= var37 (newHeap (alloc var36 (O_TSLL var35)))) (or (and var33 (= var34 (newAddr (alloc var36 (O_TSLL var35))))) (and (not var33) (= var34 var32)))) (= var31 var30)) (= var29 var28)) (= var27 (newAddr (alloc var36 (O_TSLL var35))))) (and (= var26 0) (and (and (and (and (and (and (and (= var25 var24) (= var23 var22)) (= var21 var20)) (= var19 var18)) (= var17 (|TSLL::next| (getTSLL (read var24 var18))))) (and (and (and (and (and (= var16 (newHeap (alloc var50 (O_TSLL var15)))) (or (and var13 (= var14 (newAddr (alloc var50 (O_TSLL var15))))) (and (not var13) (= var14 var49)))) (= var12 var48)) (= var11 var47)) (= var10 (newAddr (alloc var50 (O_TSLL var15))))) (not (= var9 0)))) (and (and (and (= var24 (write var16 var11 (O_TSLL (TSLL var10 (|TSLL::colour| (getTSLL (read var16 var11))))))) (= var22 var14)) (= var20 var12)) (= var18 var11))) (and (and (and (= var8 (write var25 var17 (O_TSLL (TSLL nullAddr (|TSLL::colour| (getTSLL (read var25 var17))))))) (= var7 var23)) (= var6 var21)) (= var5 var17))))) (and (and (and (= var36 (write var8 var5 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var8 var5))) 0)))) (= var32 var7)) (= var30 var6)) (= var28 var5)))) (and (and (and (= var45 (write var37 var29 (O_TSLL (TSLL var27 (|TSLL::colour| (getTSLL (read var37 var29))))))) (= var43 var34)) (= var41 var31)) (= var39 var29))) (and (and (and (= var4 (write var46 var38 (O_TSLL (TSLL nullAddr (|TSLL::colour| (getTSLL (read var46 var38))))))) (= var3 var44)) (= var2 var42)) (= var1 var38))) (= var0 (write var4 var1 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var4 var1))) 1))))))) (inv_main1010_2 var0 var3 var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Bool) (var8 Addr) (var9 TSLL) (var10 Heap) (var11 Addr) (var12 Heap)) (or (not (and (inv_main1006_2 var12 var11) (and (and (and (and (= var10 (newHeap (alloc var12 (O_TSLL var9)))) (or (and var7 (= var8 (newAddr (alloc var12 (O_TSLL var9))))) (and (not var7) (= var8 var11)))) (= var6 (newAddr (alloc var12 (O_TSLL var9))))) (and (and (= var5 (write var10 var6 (O_TSLL (TSLL nullAddr (|TSLL::colour| (getTSLL (read var10 var6))))))) (= var4 var8)) (= var3 var6))) (and (and (= var2 (write var5 var3 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var5 var3))) 1)))) (= var1 var4)) (= var0 var3))))) (inv_main1010_2 var2 var1 var0 var0))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_exit var1 var0) (not (= var0 nullAddr))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap)) (not (and (inv_main1071_9 var2 var1 var0) (not (= var1 nullAddr))))))
(check-sat)
