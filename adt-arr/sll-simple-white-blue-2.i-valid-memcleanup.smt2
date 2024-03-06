(set-logic HORN)
(set-info :source |
    Benchmark: C_VC
    Output by Princess (http://www.philipp.ruemmer.org/princess.shtml)
|)
(set-info :status unsat)
(declare-datatype bool ((true) (false)))
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
(declare-fun inv_exit (Heap Addr) Bool)
(declare-fun inv_main1003_2 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main1066_9 (Heap Addr Int) Bool)
(declare-fun inv_main999_2 (Heap Addr) Bool)
(declare-fun inv_main_12 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main_20 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main_23 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main_31 (Heap Addr Addr Addr) Bool)
(assert (forall ((var0 Addr) (var1 Heap)) (or (not (and (= var1 emptyHeap) (= var0 nullAddr))) (inv_main999_2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Heap)) (or (not (and (inv_main_20 var13 var12 var11 var10) (and (and (and (and (and (= var9 var8) (= var7 var6)) (= var5 var4)) (= var3 var2)) (= var1 (|TSLL::next| (getTSLL (read var8 var2))))) (and (= var0 1) (and (and (and (and (= var8 var13) (= var6 var12)) (= var4 var11)) (= var2 var10)) (= var0 (|TSLL::data| (getTSLL (read var13 var10))))))))) (inv_main_23 var9 var7 var5 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Heap)) (or (not (and (inv_main_23 var13 var12 var11 var10) (and (and (and (and (and (= var9 var8) (= var7 var6)) (= var5 var4)) (= var3 var2)) (= var1 (|TSLL::next| (getTSLL (read var8 var2))))) (and (and (= var0 1) (and (and (and (and (= var8 var13) (= var6 var12)) (= var4 var11)) (= var2 var10)) (= var0 (|TSLL::data| (getTSLL (read var13 var10)))))) (not (= var10 nullAddr)))))) (inv_main_23 var9 var7 var5 var1))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main1003_2 var5 var4 var3 var2) (and (= var1 0) (= var0 0)))) (inv_main_12 var5 var4 var3 var3))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main_12 var9 var8 var7 var6) (and (and (and (and (and (= var5 var9) (= var4 var8)) (= var3 var7)) (= var2 var6)) (= var1 (|TSLL::next| (getTSLL (read var9 var6))))) (and (= var0 0) (not (= (|TSLL::next| (getTSLL (read var9 var6))) nullAddr)))))) (inv_main_12 var5 var4 var3 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main_31 var4 var3 var2 var1) (and (= var1 nullAddr) (= var0 0)))) (inv_main1066_9 var4 var3 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main_23 var8 var7 var6 var5) (and (and (not (= var4 1)) (and (and (and (and (= var3 var8) (= var2 var7)) (= var1 var6)) (= var0 var5)) (= var4 (|TSLL::data| (getTSLL (read var8 var5)))))) (not (= var5 nullAddr))))) (inv_exit var3 var2))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Int) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Bool) (var10 Addr) (var11 TSLL) (var12 Heap) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Heap) (var21 Heap) (var22 Addr) (var23 Addr) (var24 Addr) (var25 Heap)) (or (not (and (inv_main1003_2 var25 var24 var23 var22) (and (and (and (and (and (and (and (and (= var21 var20) (= var19 var18)) (= var17 var16)) (= var15 var14)) (= var13 (|TSLL::next| (getTSLL (read var20 var14))))) (and (and (and (and (and (= var12 (newHeap (alloc var25 (O_TSLL var11)))) (or (and var9 (= var10 (newAddr (alloc var25 (O_TSLL var11))))) (and (not var9) (= var10 var24)))) (= var8 var23)) (= var7 var22)) (= var6 (newAddr (alloc var25 (O_TSLL var11))))) (not (= var5 0)))) (and (and (and (= var20 (write var12 var7 (O_TSLL (TSLL var6 (|TSLL::data| (getTSLL (read var12 var7))))))) (= var18 var10)) (= var16 var8)) (= var14 var7))) (and (and (and (= var4 (write var21 var13 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var21 var13))) 0)))) (= var3 var19)) (= var2 var17)) (= var1 var13))) (= var0 (write var4 var1 (O_TSLL (TSLL nullAddr (|TSLL::data| (getTSLL (read var4 var1)))))))))) (inv_main1003_2 var0 var3 var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Bool) (var8 Addr) (var9 TSLL) (var10 Heap) (var11 Addr) (var12 Heap)) (or (not (and (inv_main999_2 var12 var11) (and (and (and (and (= var10 (newHeap (alloc var12 (O_TSLL var9)))) (or (and var7 (= var8 (newAddr (alloc var12 (O_TSLL var9))))) (and (not var7) (= var8 var11)))) (= var6 (newAddr (alloc var12 (O_TSLL var9))))) (and (and (= var5 (write var10 var6 (O_TSLL (TSLL nullAddr (|TSLL::data| (getTSLL (read var10 var6))))))) (= var4 var8)) (= var3 var6))) (and (and (= var2 (write var5 var3 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var5 var3))) 0)))) (= var1 var4)) (= var0 var3))))) (inv_main1003_2 var2 var1 var0 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main_23 var3 var2 var1 var0) (= var0 nullAddr))) (inv_main_31 var3 var2 var1 var1))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main_31 var10 var9 var8 var7) (and (and (and (and (and (and (and (= var6 var10) (= var5 var9)) (= var4 var7)) (= var3 var7)) (= var2 (|TSLL::next| (getTSLL (read var10 var7))))) (not (= var7 nullAddr))) (= var1 (write var6 var4 defObj))) (or (and (= var5 var4) (= var0 nullAddr)) (and (not (= var5 var4)) (= var0 var5)))))) (inv_main_31 var1 var0 var4 var2))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Heap)) (or (not (and (inv_main_20 var13 var12 var11 var10) (and (and (and (and (and (= var9 var8) (= var7 var6)) (= var5 var4)) (= var3 var2)) (= var1 (|TSLL::next| (getTSLL (read var8 var2))))) (and (not (= var0 1)) (and (and (and (and (= var8 var13) (= var6 var12)) (= var4 var11)) (= var2 var10)) (= var0 (|TSLL::data| (getTSLL (read var13 var10))))))))) (inv_main_20 var9 var7 var5 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Int) (var9 Int) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Bool) (var14 Addr) (var15 TSLL) (var16 Heap) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Heap)) (or (not (and (inv_main1003_2 var20 var19 var18 var17) (and (and (and (and (and (and (and (= var16 (newHeap (alloc var20 (O_TSLL var15)))) (or (and var13 (= var14 (newAddr (alloc var20 (O_TSLL var15))))) (and (not var13) (= var14 var19)))) (= var12 var18)) (= var11 var17)) (= var10 (newAddr (alloc var20 (O_TSLL var15))))) (and (not (= var9 0)) (= var8 0))) (and (and (and (= var7 (write var16 var10 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var16 var10))) 1)))) (= var6 var14)) (= var5 var12)) (= var4 var10))) (and (and (and (= var3 (write var7 var4 (O_TSLL (TSLL var5 (|TSLL::data| (getTSLL (read var7 var4))))))) (= var2 var6)) (= var1 var5)) (= var0 var4))))) (inv_main_20 var3 var2 var0 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Heap) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Bool) (var23 Addr) (var24 TSLL) (var25 Heap) (var26 Heap) (var27 Addr) (var28 Addr) (var29 Addr) (var30 Heap)) (or (not (and (inv_main_12 var30 var29 var28 var27) (and (and (and (and (and (and (and (and (and (and (= var26 (newHeap (alloc var25 (O_TSLL var24)))) (or (and var22 (= var23 (newAddr (alloc var25 (O_TSLL var24))))) (and (not var22) (= var23 var21)))) (= var20 var19)) (= var18 var17)) (= var16 var15)) (= var14 (newAddr (alloc var25 (O_TSLL var24))))) (and (and (and (and (= var25 var30) (= var21 var29)) (= var19 var28)) (= var17 var27)) (= var15 (|TSLL::next| (getTSLL (read var30 var27)))))) (and (and (and (and (= var13 (write var26 var18 (O_TSLL (TSLL var14 (|TSLL::data| (getTSLL (read var26 var18))))))) (= var12 var23)) (= var11 var20)) (= var10 var18)) (= var9 var16))) (and (and (and (and (= var8 (write var13 (|TSLL::next| (getTSLL (read var13 var10))) (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var13 (|TSLL::next| (getTSLL (read var13 var10)))))) 1)))) (= var7 var12)) (= var6 var11)) (= var5 var10)) (= var4 var9))) (and (and (and (= var3 (write var8 (|TSLL::next| (getTSLL (read var8 var5))) (O_TSLL (TSLL var4 (|TSLL::data| (getTSLL (read var8 (|TSLL::next| (getTSLL (read var8 var5)))))))))) (= var2 var7)) (= var1 var6)) (= var0 var5))) (= (|TSLL::next| (getTSLL (read var30 var27))) nullAddr)))) (inv_main_20 var3 var2 var1 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Heap) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Bool) (var24 Addr) (var25 TSLL) (var26 Heap) (var27 Heap) (var28 Addr) (var29 Addr) (var30 Addr) (var31 Heap)) (or (not (and (inv_main_12 var31 var30 var29 var28) (and (and (and (and (and (and (and (and (and (and (= var27 (newHeap (alloc var26 (O_TSLL var25)))) (or (and var23 (= var24 (newAddr (alloc var26 (O_TSLL var25))))) (and (not var23) (= var24 var22)))) (= var21 var20)) (= var19 var18)) (= var17 var16)) (= var15 (newAddr (alloc var26 (O_TSLL var25))))) (and (and (and (and (= var26 var31) (= var22 var30)) (= var20 var29)) (= var18 var28)) (= var16 (|TSLL::next| (getTSLL (read var31 var28)))))) (and (and (and (and (= var14 (write var27 var19 (O_TSLL (TSLL var15 (|TSLL::data| (getTSLL (read var27 var19))))))) (= var13 var24)) (= var12 var21)) (= var11 var19)) (= var10 var17))) (and (and (and (and (= var9 (write var14 (|TSLL::next| (getTSLL (read var14 var11))) (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var14 (|TSLL::next| (getTSLL (read var14 var11)))))) 1)))) (= var8 var13)) (= var7 var12)) (= var6 var11)) (= var5 var10))) (and (and (and (= var4 (write var9 (|TSLL::next| (getTSLL (read var9 var6))) (O_TSLL (TSLL var5 (|TSLL::data| (getTSLL (read var9 (|TSLL::next| (getTSLL (read var9 var6)))))))))) (= var3 var8)) (= var2 var7)) (= var1 var6))) (and (not (= var0 0)) (not (= (|TSLL::next| (getTSLL (read var31 var28))) nullAddr)))))) (inv_main_20 var4 var3 var2 var2))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_exit var1 var0) (not (= var0 nullAddr))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap)) (not (and (inv_main1066_9 var2 var1 var0) (not (= var1 nullAddr))))))
(check-sat)
