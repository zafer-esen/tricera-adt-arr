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
(declare-fun inv_main1004_2 (Heap) Bool)
(declare-fun inv_main1009_2 (Heap Addr Addr) Bool)
(declare-fun inv_main_17 (Heap Addr Addr) Bool)
(declare-fun inv_main_36 (Heap Addr Addr) Bool)
(declare-fun inv_main_37 (Heap Addr Addr) Bool)
(declare-fun inv_main_40 (Heap Addr Addr) Bool)
(assert (forall ((var0 Heap)) (or (not (= var0 emptyHeap)) (inv_main1004_2 var0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Int) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 TSLL) (var15 Heap) (var16 Heap) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Heap)) (or (not (and (inv_main1009_2 var20 var19 var18) (and (not (= nullAddr var17)) (and (and (and (and (and (and (and (and (= var16 (newHeap (alloc var15 (O_TSLL var14)))) (= var13 var12)) (= var11 var10)) (= var9 (newAddr (alloc var15 (O_TSLL var14))))) (= var8 0)) (and (and (= var15 (write var20 var18 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var20 var18))) (|TSLL::prev| (getTSLL (read var20 var18))) 1)))) (= var12 var19)) (= var10 var18))) (and (and (= var7 (write var16 var11 (O_TSLL (TSLL var9 (|TSLL::prev| (getTSLL (read var16 var11))) (|TSLL::data| (getTSLL (read var16 var11))))))) (= var6 var13)) (= var5 var11))) (and (and (= var4 (write var7 (|TSLL::next| (getTSLL (read var7 var5))) (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var7 (|TSLL::next| (getTSLL (read var7 var5)))))) var5 (|TSLL::data| (getTSLL (read var7 (|TSLL::next| (getTSLL (read var7 var5)))))))))) (= var3 var6)) (= var2 var5))) (and (and (= var1 (write var4 (|TSLL::next| (getTSLL (read var4 var2))) (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var4 (|TSLL::next| (getTSLL (read var4 var2)))))) (|TSLL::prev| (getTSLL (read var4 (|TSLL::next| (getTSLL (read var4 var2)))))) 2)))) (= var17 var3)) (= var0 var2)))))) (inv_main_17 var1 var17 var17))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main_17 var6 var5 var4) (and (and (and (and (= var3 var6) (= var2 var5)) (= var1 var4)) (= var0 (|TSLL::next| (getTSLL (read var6 var4))))) (and (= 0 (|TSLL::data| (getTSLL (read var6 var4)))) (not (= 1 (|TSLL::data| (getTSLL (read var6 var4))))))))) (inv_main_17 var3 var2 var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main_37 var3 var2 var1) (= var0 (write var3 (|TSLL::next| (getTSLL (read var3 var1))) defObj)))) (inv_main_40 var0 var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main_36 var5 var4 var3) (and (and (= 1 (|TSLL::data| (getTSLL (read var2 var1)))) (= 1 (|TSLL::data| (getTSLL (read var2 var1))))) (and (and (= var2 (write var5 var4 defObj)) (= var0 var4)) (= var1 var3))))) (inv_main_37 var2 var0 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main_17 var6 var5 var4) (and (and (= 1 (|TSLL::data| (getTSLL (read var3 var2)))) (= 1 (|TSLL::data| (getTSLL (read var3 var2))))) (and (= 2 (|TSLL::data| (getTSLL (read var3 var1)))) (and (and (and (and (= var3 var6) (= var2 var5)) (= var0 var4)) (= var1 (|TSLL::next| (getTSLL (read var6 var4))))) (and (= 1 (|TSLL::data| (getTSLL (read var6 var4)))) (= 1 (|TSLL::data| (getTSLL (read var6 var4)))))))))) (inv_main_37 var3 var2 var2))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Int) (var6 Addr) (var7 Addr) (var8 Addr) (var9 TSLL) (var10 Heap) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Heap) (var17 Heap) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Heap)) (or (not (and (inv_main1009_2 var21 var20 var19) (and (and (not (= nullAddr var18)) (and (and (and (and (and (= var17 var16) (= var15 var14)) (= var13 var12)) (= var11 (|TSLL::next| (getTSLL (read var16 var12))))) (and (and (and (and (and (= var10 (newHeap (alloc var21 (O_TSLL var9)))) (= var8 var20)) (= var7 var19)) (= var6 (newAddr (alloc var21 (O_TSLL var9))))) (not (= var5 0))) (and (and (= var4 (write var10 var7 (O_TSLL (TSLL var6 (|TSLL::prev| (getTSLL (read var10 var7))) (|TSLL::data| (getTSLL (read var10 var7))))))) (= var3 var8)) (= var2 var7)))) (and (and (= var16 (write var4 (|TSLL::next| (getTSLL (read var4 var2))) (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var4 (|TSLL::next| (getTSLL (read var4 var2)))))) var2 (|TSLL::data| (getTSLL (read var4 (|TSLL::next| (getTSLL (read var4 var2)))))))))) (= var14 var3)) (= var12 var2)))) (and (and (= var1 (write var17 var11 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var17 var11))) (|TSLL::prev| (getTSLL (read var17 var11))) 0)))) (= var0 var15)) (= var18 var11))))) (inv_main1009_2 var1 var0 var18))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Heap) (var6 Addr) (var7 TSLL) (var8 Heap) (var9 Heap)) (or (not (and (inv_main1004_2 var9) (and (and (and (and (= var8 (newHeap (alloc var9 (O_TSLL var7)))) (= var6 (newAddr (alloc var9 (O_TSLL var7))))) (and (= var5 (write var8 var6 (O_TSLL (TSLL nullAddr (|TSLL::prev| (getTSLL (read var8 var6))) (|TSLL::data| (getTSLL (read var8 var6))))))) (= var4 var6))) (and (= var3 (write var5 var4 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var5 var4))) nullAddr (|TSLL::data| (getTSLL (read var5 var4))))))) (= var2 var4))) (and (= var1 (write var3 var2 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var3 var2))) (|TSLL::prev| (getTSLL (read var3 var2))) 0)))) (= var0 var2))))) (inv_main1009_2 var1 var0 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main_36 var9 var8 var7) (and (and (and (and (and (= var6 var5) (= var4 var3)) (= var2 var3)) (= var1 (|TSLL::next| (getTSLL (read var5 var3))))) (not (= 1 (|TSLL::data| (getTSLL (read var5 var3)))))) (and (and (= var5 (write var9 var8 defObj)) (= var0 var8)) (= var3 var7))))) (inv_main_36 var6 var4 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main_17 var10 var9 var8) (and (and (and (and (and (= var7 var6) (= var5 var4)) (= var3 var4)) (= var2 (|TSLL::next| (getTSLL (read var6 var4))))) (not (= 1 (|TSLL::data| (getTSLL (read var6 var4)))))) (and (= 2 (|TSLL::data| (getTSLL (read var6 var1)))) (and (and (and (and (= var6 var10) (= var4 var9)) (= var0 var8)) (= var1 (|TSLL::next| (getTSLL (read var10 var8))))) (and (= 1 (|TSLL::data| (getTSLL (read var10 var8)))) (= 1 (|TSLL::data| (getTSLL (read var10 var8)))))))))) (inv_main_36 var7 var5 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_36 var2 var1 var0) (and (not (= var1 nullAddr)) (= (read var2 var1) defObj))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_37 var2 var1 var0) (and (not (= (|TSLL::next| (getTSLL (read var2 var0))) nullAddr)) (= (read var2 (|TSLL::next| (getTSLL (read var2 var0)))) defObj))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_40 var2 var1 var0) (and (not (= var0 nullAddr)) (= (read var2 var0) defObj))))))
(check-sat)
