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
(declare-fun inv_main1003_2 (Heap) Bool)
(declare-fun inv_main1007_2 (Heap Addr Addr) Bool)
(declare-fun inv_main1016_12 (Heap Addr Addr) Bool)
(declare-fun inv_main1024_11 (Heap Addr Addr) Bool)
(declare-fun inv_main1028_12 (Heap Addr Addr) Bool)
(declare-fun inv_main1031_11 (Heap Addr Addr) Bool)
(declare-fun inv_main1033_11 (Heap Addr Addr) Bool)
(declare-fun inv_main1043_11 (Heap Addr Addr) Bool)
(declare-fun inv_main_14 (Heap Addr Addr) Bool)
(declare-fun inv_main_29 (Heap Addr Addr) Bool)
(assert (forall ((var0 Heap)) (or (not (= var0 emptyHeap)) (inv_main1003_2 var0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Int) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 TSLL) (var12 Heap) (var13 Heap) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Heap)) (or (not (and (inv_main1007_2 var17 var16 var15) (and (not (= nullAddr var14)) (and (and (and (and (and (and (and (= var13 (newHeap (alloc var12 (O_TSLL var11)))) (= var10 var9)) (= var8 var7)) (= var6 (newAddr (alloc var12 (O_TSLL var11))))) (= var5 0)) (and (and (= var12 (write var17 var15 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var17 var15))) 1)))) (= var9 var16)) (= var7 var15))) (and (and (= var4 (write var13 var8 (O_TSLL (TSLL var6 (|TSLL::data| (getTSLL (read var13 var8))))))) (= var3 var10)) (= var2 var8))) (and (and (= var1 (write var4 (|TSLL::next| (getTSLL (read var4 var2))) (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var4 (|TSLL::next| (getTSLL (read var4 var2)))))) 2)))) (= var14 var3)) (= var0 var2)))))) (inv_main_14 var1 var14 var14))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main_14 var6 var5 var4) (and (and (and (and (= var3 var6) (= var2 var5)) (= var1 var4)) (= var0 (|TSLL::next| (getTSLL (read var6 var4))))) (and (= 0 (|TSLL::data| (getTSLL (read var6 var4)))) (not (= 1 (|TSLL::data| (getTSLL (read var6 var4))))))))) (inv_main_14 var3 var2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main_14 var6 var5 var4) (and (= 2 (|TSLL::data| (getTSLL (read var3 var2)))) (and (and (and (and (= var3 var6) (= var1 var5)) (= var0 var4)) (= var2 (|TSLL::next| (getTSLL (read var6 var4))))) (and (= 1 (|TSLL::data| (getTSLL (read var6 var4)))) (= 1 (|TSLL::data| (getTSLL (read var6 var4))))))))) (inv_main_29 var3 var1 var1))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main_29 var7 var6 var5) (and (and (and (and (and (= var4 var7) (= var3 var5)) (= var2 var5)) (= var1 (|TSLL::next| (getTSLL (read var7 var5))))) (not (= 1 (|TSLL::data| (getTSLL (read var7 var5)))))) (= var0 (write var4 var3 defObj))))) (inv_main_29 var0 var3 var1))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 TSLL) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Heap) (var14 Heap) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Heap)) (or (not (and (inv_main1007_2 var18 var17 var16) (and (and (= nullAddr var15) (and (and (and (and (and (= var14 var13) (= var12 var11)) (= var10 var9)) (= var8 (|TSLL::next| (getTSLL (read var13 var9))))) (and (and (and (and (= var7 (newHeap (alloc var18 (O_TSLL var6)))) (= var5 var17)) (= var4 var16)) (= var3 (newAddr (alloc var18 (O_TSLL var6))))) (not (= var2 0)))) (and (and (= var13 (write var7 var4 (O_TSLL (TSLL var3 (|TSLL::data| (getTSLL (read var7 var4))))))) (= var11 var5)) (= var9 var4)))) (and (and (= var1 (write var14 var8 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var14 var8))) 0)))) (= var0 var12)) (= var15 var8))))) (inv_main1016_12 var1 var0 var15))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 TSLL) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Heap) (var14 Heap) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Heap)) (or (not (and (inv_main1007_2 var18 var17 var16) (and (and (not (= nullAddr var15)) (and (and (and (and (and (= var14 var13) (= var12 var11)) (= var10 var9)) (= var8 (|TSLL::next| (getTSLL (read var13 var9))))) (and (and (and (and (= var7 (newHeap (alloc var18 (O_TSLL var6)))) (= var5 var17)) (= var4 var16)) (= var3 (newAddr (alloc var18 (O_TSLL var6))))) (not (= var2 0)))) (and (and (= var13 (write var7 var4 (O_TSLL (TSLL var3 (|TSLL::data| (getTSLL (read var7 var4))))))) (= var11 var5)) (= var9 var4)))) (and (and (= var1 (write var14 var8 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var14 var8))) 0)))) (= var0 var12)) (= var15 var8))))) (inv_main1007_2 var1 var0 var15))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Heap) (var4 Addr) (var5 TSLL) (var6 Heap) (var7 Heap)) (or (not (and (inv_main1003_2 var7) (and (and (and (= var6 (newHeap (alloc var7 (O_TSLL var5)))) (= var4 (newAddr (alloc var7 (O_TSLL var5))))) (and (= var3 (write var6 var4 (O_TSLL (TSLL nullAddr (|TSLL::data| (getTSLL (read var6 var4))))))) (= var2 var4))) (and (= var1 (write var3 var2 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var3 var2))) 0)))) (= var0 var2))))) (inv_main1007_2 var1 var0 var0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Int) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 TSLL) (var12 Heap) (var13 Heap) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Heap)) (or (not (and (inv_main1007_2 var17 var16 var15) (and (= nullAddr var14) (and (and (and (and (and (and (and (= var13 (newHeap (alloc var12 (O_TSLL var11)))) (= var10 var9)) (= var8 var7)) (= var6 (newAddr (alloc var12 (O_TSLL var11))))) (= var5 0)) (and (and (= var12 (write var17 var15 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var17 var15))) 1)))) (= var9 var16)) (= var7 var15))) (and (and (= var4 (write var13 var8 (O_TSLL (TSLL var6 (|TSLL::data| (getTSLL (read var13 var8))))))) (= var3 var10)) (= var2 var8))) (and (and (= var1 (write var4 (|TSLL::next| (getTSLL (read var4 var2))) (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var4 (|TSLL::next| (getTSLL (read var4 var2)))))) 2)))) (= var14 var3)) (= var0 var2)))))) (inv_main1024_11 var1 var14 var14))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main_14 var6 var5 var4) (and (not (= 2 (|TSLL::data| (getTSLL (read var3 var2))))) (and (and (and (and (= var3 var6) (= var1 var5)) (= var0 var4)) (= var2 (|TSLL::next| (getTSLL (read var6 var4))))) (and (= 1 (|TSLL::data| (getTSLL (read var6 var4)))) (= 1 (|TSLL::data| (getTSLL (read var6 var4))))))))) (inv_main1033_11 var3 var1 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (and (inv_main_14 var2 var1 var0) (and (not (= 1 (|TSLL::data| (getTSLL (read var2 var0))))) (= 1 (|TSLL::data| (getTSLL (read var2 var0))))))) (inv_main1031_11 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (and (inv_main_14 var2 var1 var0) (and (not (= 0 (|TSLL::data| (getTSLL (read var2 var0))))) (not (= 1 (|TSLL::data| (getTSLL (read var2 var0)))))))) (inv_main1028_12 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (and (inv_main_29 var2 var1 var0) (and (not (= 1 (|TSLL::data| (getTSLL (read var2 var0))))) (= 1 (|TSLL::data| (getTSLL (read var2 var0))))))) (inv_main1043_11 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (inv_main1016_12 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (inv_main1024_11 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (inv_main1028_12 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (inv_main1031_11 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (inv_main1033_11 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (inv_main1043_11 var2 var1 var0))))
(check-sat)
