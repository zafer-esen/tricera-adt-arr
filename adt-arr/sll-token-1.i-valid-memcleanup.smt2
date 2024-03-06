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
(declare-fun inv_main1003_2 (Heap Addr) Bool)
(declare-fun inv_main1007_2 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main1047_9 (Heap Addr Int) Bool)
(declare-fun inv_main_14 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main_29 (Heap Addr Addr Addr) Bool)
(assert (forall ((var0 Addr) (var1 Heap)) (or (not (and (= var1 emptyHeap) (= var0 nullAddr))) (inv_main1003_2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Int) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Bool) (var8 Addr) (var9 TSLL) (var10 Heap) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Heap) (var19 Heap) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Heap)) (or (not (and (inv_main1007_2 var24 var23 var22 var21) (and (and (= nullAddr var20) (and (and (and (and (and (and (= var19 var18) (= var17 var16)) (= var15 var14)) (= var13 var12)) (= var11 (|TSLL::next| (getTSLL (read var18 var12))))) (and (and (and (and (and (= var10 (newHeap (alloc var24 (O_TSLL var9)))) (or (and var7 (= var8 (newAddr (alloc var24 (O_TSLL var9))))) (and (not var7) (= var8 var23)))) (= var6 var22)) (= var5 var21)) (= var4 (newAddr (alloc var24 (O_TSLL var9))))) (not (= var3 0)))) (and (and (and (= var18 (write var10 var5 (O_TSLL (TSLL var4 (|TSLL::data| (getTSLL (read var10 var5))))))) (= var16 var8)) (= var14 var6)) (= var12 var5)))) (and (and (and (= var2 (write var19 var11 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var19 var11))) 0)))) (= var1 var17)) (= var0 var15)) (= var20 var11))))) (inv_exit var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Int) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Bool) (var15 Addr) (var16 TSLL) (var17 Heap) (var18 Heap) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Heap)) (or (not (and (inv_main1007_2 var23 var22 var21 var20) (and (= nullAddr var19) (and (and (and (and (and (and (and (and (= var18 (newHeap (alloc var17 (O_TSLL var16)))) (or (and var14 (= var15 (newAddr (alloc var17 (O_TSLL var16))))) (and (not var14) (= var15 var13)))) (= var12 var11)) (= var10 var9)) (= var8 (newAddr (alloc var17 (O_TSLL var16))))) (= var7 0)) (and (and (and (= var17 (write var23 var20 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var23 var20))) 1)))) (= var13 var22)) (= var11 var21)) (= var9 var20))) (and (and (and (= var6 (write var18 var10 (O_TSLL (TSLL var8 (|TSLL::data| (getTSLL (read var18 var10))))))) (= var5 var15)) (= var4 var12)) (= var3 var10))) (and (and (and (= var2 (write var6 (|TSLL::next| (getTSLL (read var6 var3))) (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var6 (|TSLL::next| (getTSLL (read var6 var3)))))) 2)))) (= var1 var5)) (= var19 var4)) (= var0 var3)))))) (inv_exit var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main_14 var3 var2 var1 var0) (and (not (= 0 (|TSLL::data| (getTSLL (read var3 var0))))) (not (= 1 (|TSLL::data| (getTSLL (read var3 var0)))))))) (inv_exit var3 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main_14 var3 var2 var1 var0) (and (not (= 2 (|TSLL::data| (getTSLL (read var3 var0))))) (= 1 (|TSLL::data| (getTSLL (read var3 var0))))))) (inv_exit var3 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main_14 var8 var7 var6 var5) (and (not (= 2 (|TSLL::data| (getTSLL (read var4 var3))))) (and (and (and (and (and (= var4 var8) (= var2 var7)) (= var1 var6)) (= var0 var5)) (= var3 (|TSLL::next| (getTSLL (read var8 var5))))) (and (= 2 (|TSLL::data| (getTSLL (read var8 var5)))) (= 1 (|TSLL::data| (getTSLL (read var8 var5))))))))) (inv_exit var4 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main_29 var3 var2 var1 var0) (and (not (= 1 (|TSLL::data| (getTSLL (read var3 var0))))) (= 1 (|TSLL::data| (getTSLL (read var3 var0))))))) (inv_exit var3 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Int) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Bool) (var8 Addr) (var9 TSLL) (var10 Heap) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Heap) (var19 Heap) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Heap)) (or (not (and (inv_main1007_2 var24 var23 var22 var21) (and (and (not (= nullAddr var20)) (and (and (and (and (and (and (= var19 var18) (= var17 var16)) (= var15 var14)) (= var13 var12)) (= var11 (|TSLL::next| (getTSLL (read var18 var12))))) (and (and (and (and (and (= var10 (newHeap (alloc var24 (O_TSLL var9)))) (or (and var7 (= var8 (newAddr (alloc var24 (O_TSLL var9))))) (and (not var7) (= var8 var23)))) (= var6 var22)) (= var5 var21)) (= var4 (newAddr (alloc var24 (O_TSLL var9))))) (not (= var3 0)))) (and (and (and (= var18 (write var10 var5 (O_TSLL (TSLL var4 (|TSLL::data| (getTSLL (read var10 var5))))))) (= var16 var8)) (= var14 var6)) (= var12 var5)))) (and (and (and (= var2 (write var19 var11 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var19 var11))) 0)))) (= var1 var17)) (= var0 var15)) (= var20 var11))))) (inv_main1007_2 var2 var1 var0 var20))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Bool) (var8 Addr) (var9 TSLL) (var10 Heap) (var11 Addr) (var12 Heap)) (or (not (and (inv_main1003_2 var12 var11) (and (and (and (and (= var10 (newHeap (alloc var12 (O_TSLL var9)))) (or (and var7 (= var8 (newAddr (alloc var12 (O_TSLL var9))))) (and (not var7) (= var8 var11)))) (= var6 (newAddr (alloc var12 (O_TSLL var9))))) (and (and (= var5 (write var10 var6 (O_TSLL (TSLL nullAddr (|TSLL::data| (getTSLL (read var10 var6))))))) (= var4 var8)) (= var3 var6))) (and (and (= var2 (write var5 var3 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var5 var3))) 0)))) (= var1 var4)) (= var0 var3))))) (inv_main1007_2 var2 var1 var0 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Heap)) (or (not (and (inv_main_29 var12 var11 var10 var9) (and (and (and (and (= 1 (|TSLL::data| (getTSLL (read var12 var9)))) (= 1 (|TSLL::data| (getTSLL (read var12 var9))))) (and (and (and (= var8 (write var12 (|TSLL::next| (getTSLL (read var12 var9))) defObj)) (or (and (= var11 (|TSLL::next| (getTSLL (read var12 var9)))) (= var7 nullAddr)) (and (not (= var11 (|TSLL::next| (getTSLL (read var12 var9))))) (= var7 var11)))) (= var6 var10)) (= var5 var9))) (and (and (and (= var4 (write var8 var5 defObj)) (or (and (= var7 var5) (= var3 nullAddr)) (and (not (= var7 var5)) (= var3 var7)))) (= var2 var6)) (= var1 var5))) (= var0 0)))) (inv_main1047_9 var4 var3 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Int) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Bool) (var15 Addr) (var16 TSLL) (var17 Heap) (var18 Heap) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Heap)) (or (not (and (inv_main1007_2 var23 var22 var21 var20) (and (not (= nullAddr var19)) (and (and (and (and (and (and (and (and (= var18 (newHeap (alloc var17 (O_TSLL var16)))) (or (and var14 (= var15 (newAddr (alloc var17 (O_TSLL var16))))) (and (not var14) (= var15 var13)))) (= var12 var11)) (= var10 var9)) (= var8 (newAddr (alloc var17 (O_TSLL var16))))) (= var7 0)) (and (and (and (= var17 (write var23 var20 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var23 var20))) 1)))) (= var13 var22)) (= var11 var21)) (= var9 var20))) (and (and (and (= var6 (write var18 var10 (O_TSLL (TSLL var8 (|TSLL::data| (getTSLL (read var18 var10))))))) (= var5 var15)) (= var4 var12)) (= var3 var10))) (and (and (and (= var2 (write var6 (|TSLL::next| (getTSLL (read var6 var3))) (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var6 (|TSLL::next| (getTSLL (read var6 var3)))))) 2)))) (= var1 var5)) (= var19 var4)) (= var0 var3)))))) (inv_main_14 var2 var1 var19 var19))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main_14 var8 var7 var6 var5) (and (and (and (and (and (= var4 var8) (= var3 var7)) (= var2 var6)) (= var1 var5)) (= var0 (|TSLL::next| (getTSLL (read var8 var5))))) (and (= 0 (|TSLL::data| (getTSLL (read var8 var5)))) (not (= 1 (|TSLL::data| (getTSLL (read var8 var5))))))))) (inv_main_14 var4 var3 var2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main_14 var8 var7 var6 var5) (and (= 2 (|TSLL::data| (getTSLL (read var4 var3)))) (and (and (and (and (and (= var4 var8) (= var2 var7)) (= var1 var6)) (= var0 var5)) (= var3 (|TSLL::next| (getTSLL (read var8 var5))))) (and (= 2 (|TSLL::data| (getTSLL (read var8 var5)))) (= 1 (|TSLL::data| (getTSLL (read var8 var5))))))))) (inv_main_29 var4 var2 var1 var1))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main_29 var10 var9 var8 var7) (and (and (and (and (and (and (and (= var6 var10) (= var5 var9)) (= var4 var7)) (= var3 var7)) (= var2 (|TSLL::next| (getTSLL (read var10 var7))))) (not (= 1 (|TSLL::data| (getTSLL (read var10 var7)))))) (= var1 (write var6 var4 defObj))) (or (and (= var5 var4) (= var0 nullAddr)) (and (not (= var5 var4)) (= var0 var5)))))) (inv_main_29 var1 var0 var4 var2))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_exit var1 var0) (not (= var0 nullAddr))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap)) (not (and (inv_main1047_9 var2 var1 var0) (not (= var1 nullAddr))))))
(check-sat)
