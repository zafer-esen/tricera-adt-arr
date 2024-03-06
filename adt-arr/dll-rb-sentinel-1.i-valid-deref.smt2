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
(declare-fun inv_main (Heap Addr) Bool)
(declare-fun inv_main1003_2 (Heap Addr Addr) Bool)
(declare-fun inv_main1014_3 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main1020_3 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main1024_3 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main1026_4 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main1045_7 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main1059_3 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main1066_3 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main998_2 (Heap) Bool)
(declare-fun inv_main998_2_1 (Heap Addr) Bool)
(declare-fun inv_main_10 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main_11 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main_13 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main_15 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main_16 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main_17 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main_18 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main_19 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main_2 (Heap Addr) Bool)
(declare-fun inv_main_29 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main_36 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main_37 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main_4 (Heap Addr Addr) Bool)
(declare-fun inv_main_40 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main_46 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main_48 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main_5 (Heap Addr Addr) Bool)
(declare-fun inv_main_9 (Heap Addr Addr Addr) Bool)
(assert (forall ((var0 Heap)) (or (not (= var0 emptyHeap)) (inv_main998_2 var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main_17 var4 var3 var2 var1) (and (and (is-O_TSLL (read var4 var1)) (is-O_TSLL (read var4 var1))) (= var0 (write var4 var1 (O_TSLL (TSLL var3 (|TSLL::prev| (getTSLL (read var4 var1))) (|TSLL::colour| (getTSLL (read var4 var1)))))))))) (inv_main_18 var0 var3 var2 var1))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Heap)) (or (not (and (inv_main_48 var12 var11 var10 var9) (and (and (not (= var8 var7)) (and (is-O_TSLL (read var12 var9)) (and (and (and (and (= var6 var12) (= var5 var11)) (= var4 var10)) (= var3 var9)) (= var2 (|TSLL::next| (getTSLL (read var12 var9))))))) (and (and (and (= var1 (write var6 var3 defObj)) (= var8 var5)) (= var7 var2)) (= var0 var3))))) (inv_main_46 var1 var8 var7 var0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Heap)) (or (not (and (inv_main1066_3 var12 var11 var10 var9) (and (not (= var8 var7)) (and (and (is-O_TSLL (read var12 var10)) (and (and (and (and (= var6 var12) (= var5 var11)) (= var4 var10)) (= var3 var9)) (= var2 (|TSLL::next| (getTSLL (read var12 var10)))))) (and (and (and (= var1 (write var6 var4 defObj)) (= var8 var5)) (= var0 var4)) (= var7 var2)))))) (inv_main_46 var1 var8 var7 var7))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main_37 var8 var7 var6 var5) (and (not (= var4 var3)) (and (= var4 var2) (and (is-O_TSLL (read var8 var5)) (and (and (and (and (= var1 var8) (= var4 var7)) (= var3 var6)) (= var0 var5)) (= var2 (|TSLL::next| (getTSLL (read var8 var5)))))))))) (inv_main_46 var1 var4 var3 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main_29 var3 var2 var1 var0) (and (not (= var2 var1)) (and (= var2 var0) (and (is-O_TSLL (read var3 var0)) (= 1 (|TSLL::colour| (getTSLL (read var3 var0))))))))) (inv_main_46 var3 var2 var1 var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main1020_3 var4 var3 var2 var1) (and (and (is-O_TSLL (read var4 var1)) (is-O_TSLL (read var4 var1))) (= var0 (write var4 var1 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var4 var1))) (|TSLL::prev| (getTSLL (read var4 var1))) 1))))))) (inv_main_13 var0 var3 var2 var1))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main_18 var4 var3 var2 var1) (and (and (is-O_TSLL (read var4 var1)) (is-O_TSLL (read var4 var1))) (= var0 (write var4 var1 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var4 var1))) (|TSLL::prev| (getTSLL (read var4 var1))) 1))))))) (inv_main_13 var0 var3 var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main_36 var3 var2 var1 var0) (and (is-O_TSLL (read var3 var0)) (= 0 (|TSLL::colour| (getTSLL (read var3 var0))))))) (inv_main1045_7 var3 var2 var1 var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main_9 var4 var3 var2 var1) (and (and (and (is-O_TSLL (read var4 var1)) (is-O_TSLL (read var4 (|TSLL::next| (getTSLL (read var4 var1)))))) (is-O_TSLL (read var4 (|TSLL::next| (getTSLL (read var4 var1)))))) (= var0 (write var4 (|TSLL::next| (getTSLL (read var4 var1))) (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var4 (|TSLL::next| (getTSLL (read var4 var1)))))) var1 (|TSLL::colour| (getTSLL (read var4 (|TSLL::next| (getTSLL (read var4 var1))))))))))))) (inv_main_10 var0 var3 var2 var1))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main1003_2 var3 var2 var1) (and (and (is-O_TSLL (read var3 var1)) (is-O_TSLL (read var3 var1))) (= var0 (write var3 var1 (O_TSLL (TSLL var2 (|TSLL::prev| (getTSLL (read var3 var1))) (|TSLL::colour| (getTSLL (read var3 var1)))))))))) (inv_main_4 var0 var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main_11 var8 var7 var6 var5) (and (= var4 0) (and (and (is-O_TSLL (read var8 var5)) (is-O_TSLL (read var8 var5))) (and (and (and (= var3 (write var8 var5 (O_TSLL (TSLL var7 (|TSLL::prev| (getTSLL (read var8 var5))) (|TSLL::colour| (getTSLL (read var8 var5))))))) (= var2 var7)) (= var1 var6)) (= var0 var5)))))) (inv_main1024_3 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main_46 var3 var2 var1 var0) (and (is-O_TSLL (read var3 var1)) (not (= 0 (|TSLL::colour| (getTSLL (read var3 var1)))))))) (inv_main1066_3 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main1045_7 var8 var7 var6 var5) (and (not (= var4 var3)) (and (is-O_TSLL (read var8 var5)) (and (and (and (and (= var2 var8) (= var4 var7)) (= var1 var6)) (= var0 var5)) (= var3 (|TSLL::next| (getTSLL (read var8 var5))))))))) (inv_main_40 var2 var4 var1 var3))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main1014_3 var5 var4 var3 var2 var1) (and (and (is-O_TSLL (read var5 var2)) (is-O_TSLL (read var5 var2))) (= var0 (write var5 var2 (O_TSLL (TSLL var1 (|TSLL::prev| (getTSLL (read var5 var2))) (|TSLL::colour| (getTSLL (read var5 var2)))))))))) (inv_main_9 var0 var4 var3 var2))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main1026_4 var5 var4 var3 var2 var1) (and (and (is-O_TSLL (read var5 var2)) (is-O_TSLL (read var5 var2))) (= var0 (write var5 var2 (O_TSLL (TSLL var1 (|TSLL::prev| (getTSLL (read var5 var2))) (|TSLL::colour| (getTSLL (read var5 var2)))))))))) (inv_main_15 var0 var4 var3 var2))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main1059_3 var9 var8 var7 var6) (and (and (is-O_TSLL (read var9 var7)) (and (and (and (and (= var5 var9) (= var4 var8)) (= var3 var7)) (= var2 var6)) (= var1 (|TSLL::next| (getTSLL (read var9 var7)))))) (= var0 (write var5 var3 defObj))))) (inv_main_48 var0 var4 var3 var1))))
(assert (forall ((var0 Addr) (var1 TSLL) (var2 Heap) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Heap)) (or (not (and (inv_main_2 var6 var5) (and (and (and (and (is-O_TSLL (read var6 var5)) (is-O_TSLL (read var6 var5))) (and (= var4 (write var6 var5 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var6 var5))) (|TSLL::prev| (getTSLL (read var6 var5))) 1)))) (= var3 var5))) (= var2 (newHeap (alloc var4 (O_TSLL var1))))) (= var0 (newAddr (alloc var4 (O_TSLL var1))))))) (inv_main1003_2 var2 var3 var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Heap)) (or (not (and (inv_main var2 var1) (and (and (is-O_TSLL (read var2 var1)) (is-O_TSLL (read var2 var1))) (= var0 (write var2 var1 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var2 var1))) nullAddr (|TSLL::colour| (getTSLL (read var2 var1)))))))))) (inv_main_2 var0 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main_13 var3 var2 var1 var0) (and (is-O_TSLL (read var3 var0)) (= 1 (|TSLL::colour| (getTSLL (read var3 var0))))))) (inv_main_19 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main_10 var8 var7 var6 var5) (and (is-O_TSLL (read var8 var5)) (and (and (and (and (= var4 var8) (= var3 var7)) (= var2 var6)) (= var1 var5)) (= var0 (|TSLL::next| (getTSLL (read var8 var5)))))))) (inv_main_11 var4 var3 var2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main_11 var8 var7 var6 var5) (and (not (= var4 0)) (and (and (is-O_TSLL (read var8 var5)) (is-O_TSLL (read var8 var5))) (and (and (and (= var3 (write var8 var5 (O_TSLL (TSLL var7 (|TSLL::prev| (getTSLL (read var8 var5))) (|TSLL::colour| (getTSLL (read var8 var5))))))) (= var2 var7)) (= var1 var6)) (= var0 var5)))))) (inv_main1020_3 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 TSLL) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main1024_3 var10 var9 var8 var7) (and (and (and (and (is-O_TSLL (read var10 var7)) (is-O_TSLL (read var10 var7))) (and (and (and (= var6 (write var10 var7 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var10 var7))) (|TSLL::prev| (getTSLL (read var10 var7))) 0)))) (= var5 var9)) (= var4 var8)) (= var3 var7))) (= var2 (newHeap (alloc var6 (O_TSLL var1))))) (= var0 (newAddr (alloc var6 (O_TSLL var1))))))) (inv_main1026_4 var2 var5 var4 var3 var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main_4 var3 var2 var1) (and (and (is-O_TSLL (read var3 var1)) (is-O_TSLL (read var3 var1))) (= var0 (write var3 var1 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var3 var1))) var2 (|TSLL::colour| (getTSLL (read var3 var1)))))))))) (inv_main_5 var0 var2 var1))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main_15 var4 var3 var2 var1) (and (and (and (is-O_TSLL (read var4 var1)) (is-O_TSLL (read var4 (|TSLL::next| (getTSLL (read var4 var1)))))) (is-O_TSLL (read var4 (|TSLL::next| (getTSLL (read var4 var1)))))) (= var0 (write var4 (|TSLL::next| (getTSLL (read var4 var1))) (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var4 (|TSLL::next| (getTSLL (read var4 var1)))))) var1 (|TSLL::colour| (getTSLL (read var4 (|TSLL::next| (getTSLL (read var4 var1))))))))))))) (inv_main_16 var0 var3 var2 var1))))
(assert (forall ((var0 Addr) (var1 TSLL) (var2 Heap) (var3 Heap)) (or (not (and (inv_main998_2 var3) (and (= var2 (newHeap (alloc var3 (O_TSLL var1)))) (= var0 (newAddr (alloc var3 (O_TSLL var1))))))) (inv_main998_2_1 var2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main_37 var8 var7 var6 var5) (and (not (= var4 var3)) (and (is-O_TSLL (read var8 var5)) (and (and (and (and (= var2 var8) (= var4 var7)) (= var1 var6)) (= var0 var5)) (= var3 (|TSLL::next| (getTSLL (read var8 var5))))))))) (inv_main_36 var2 var4 var1 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main_29 var3 var2 var1 var0) (and (not (= var2 var0)) (and (is-O_TSLL (read var3 var0)) (= 1 (|TSLL::colour| (getTSLL (read var3 var0)))))))) (inv_main_36 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 TSLL) (var2 Heap) (var3 Int) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main_19 var7 var6 var5 var4) (and (and (and (not (= var3 0)) (and (not (= var6 var4)) (and (is-O_TSLL (read var7 var4)) (= var6 (|TSLL::next| (getTSLL (read var7 var4))))))) (= var2 (newHeap (alloc var7 (O_TSLL var1))))) (= var0 (newAddr (alloc var7 (O_TSLL var1))))))) (inv_main1014_3 var2 var6 var5 var4 var0))))
(assert (forall ((var0 Addr) (var1 TSLL) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Int) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main_5 var9 var8 var7) (and (and (and (not (= var6 0)) (and (and (is-O_TSLL (read var9 var7)) (is-O_TSLL (read var9 var7))) (and (and (= var5 (write var9 var7 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var9 var7))) (|TSLL::prev| (getTSLL (read var9 var7))) 1)))) (= var4 var8)) (= var3 var7)))) (= var2 (newHeap (alloc var5 (O_TSLL var1))))) (= var0 (newAddr (alloc var5 (O_TSLL var1))))))) (inv_main1014_3 var2 var4 var3 var3 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main_16 var8 var7 var6 var5) (and (is-O_TSLL (read var8 var5)) (and (and (and (and (= var4 var8) (= var3 var7)) (= var2 var6)) (= var1 var5)) (= var0 (|TSLL::next| (getTSLL (read var8 var5)))))))) (inv_main_17 var4 var3 var2 var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Heap)) (or (not (and (inv_main998_2_1 var2 var1) (and (and (is-O_TSLL (read var2 var1)) (is-O_TSLL (read var2 var1))) (= var0 (write var2 var1 (O_TSLL (TSLL nullAddr (|TSLL::prev| (getTSLL (read var2 var1))) (|TSLL::colour| (getTSLL (read var2 var1)))))))))) (inv_main var0 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main_19 var4 var3 var2 var1) (and (and (not (= var3 var2)) (= var0 0)) (and (not (= var3 var1)) (and (is-O_TSLL (read var4 var1)) (= var3 (|TSLL::next| (getTSLL (read var4 var1))))))))) (inv_main_29 var4 var3 var2 var2))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main_5 var6 var5 var4) (and (and (not (= var3 var2)) (= var1 0)) (and (and (is-O_TSLL (read var6 var4)) (is-O_TSLL (read var6 var4))) (and (and (= var0 (write var6 var4 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var6 var4))) (|TSLL::prev| (getTSLL (read var6 var4))) 1)))) (= var3 var5)) (= var2 var4)))))) (inv_main_29 var0 var3 var2 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main_46 var3 var2 var1 var0) (and (is-O_TSLL (read var3 var1)) (= 0 (|TSLL::colour| (getTSLL (read var3 var1))))))) (inv_main1059_3 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main_36 var3 var2 var1 var0) (and (is-O_TSLL (read var3 var0)) (not (= 0 (|TSLL::colour| (getTSLL (read var3 var0)))))))) (inv_main_37 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main_40 var3 var2 var1 var0) (and (is-O_TSLL (read var3 var0)) (not (= 1 (|TSLL::colour| (getTSLL (read var3 var0)))))))) (inv_main_37 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main998_2_1 var1 var0) (not (is-O_TSLL (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main998_2_1 var1 var0) (and (is-O_TSLL (read var1 var0)) (not (is-O_TSLL (read var1 var0))))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main var1 var0) (not (is-O_TSLL (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main var1 var0) (and (is-O_TSLL (read var1 var0)) (not (is-O_TSLL (read var1 var0))))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main_2 var1 var0) (not (is-O_TSLL (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main_2 var1 var0) (and (is-O_TSLL (read var1 var0)) (not (is-O_TSLL (read var1 var0))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main1003_2 var2 var1 var0) (not (is-O_TSLL (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main1003_2 var2 var1 var0) (and (is-O_TSLL (read var2 var0)) (not (is-O_TSLL (read var2 var0))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_4 var2 var1 var0) (not (is-O_TSLL (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_4 var2 var1 var0) (and (is-O_TSLL (read var2 var0)) (not (is-O_TSLL (read var2 var0))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_5 var2 var1 var0) (not (is-O_TSLL (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_5 var2 var1 var0) (and (is-O_TSLL (read var2 var0)) (not (is-O_TSLL (read var2 var0))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main1014_3 var4 var3 var2 var1 var0) (not (is-O_TSLL (read var4 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main1014_3 var4 var3 var2 var1 var0) (and (is-O_TSLL (read var4 var1)) (not (is-O_TSLL (read var4 var1))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_9 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_9 var3 var2 var1 var0) (and (is-O_TSLL (read var3 var0)) (not (is-O_TSLL (read var3 (|TSLL::next| (getTSLL (read var3 var0)))))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_9 var3 var2 var1 var0) (and (and (is-O_TSLL (read var3 var0)) (is-O_TSLL (read var3 (|TSLL::next| (getTSLL (read var3 var0)))))) (not (is-O_TSLL (read var3 (|TSLL::next| (getTSLL (read var3 var0)))))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_10 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_11 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_11 var3 var2 var1 var0) (and (is-O_TSLL (read var3 var0)) (not (is-O_TSLL (read var3 var0))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main1020_3 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main1020_3 var3 var2 var1 var0) (and (is-O_TSLL (read var3 var0)) (not (is-O_TSLL (read var3 var0))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main1024_3 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main1024_3 var3 var2 var1 var0) (and (is-O_TSLL (read var3 var0)) (not (is-O_TSLL (read var3 var0))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main1026_4 var4 var3 var2 var1 var0) (not (is-O_TSLL (read var4 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main1026_4 var4 var3 var2 var1 var0) (and (is-O_TSLL (read var4 var1)) (not (is-O_TSLL (read var4 var1))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_15 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_15 var3 var2 var1 var0) (and (is-O_TSLL (read var3 var0)) (not (is-O_TSLL (read var3 (|TSLL::next| (getTSLL (read var3 var0)))))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_15 var3 var2 var1 var0) (and (and (is-O_TSLL (read var3 var0)) (is-O_TSLL (read var3 (|TSLL::next| (getTSLL (read var3 var0)))))) (not (is-O_TSLL (read var3 (|TSLL::next| (getTSLL (read var3 var0)))))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_16 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_17 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_17 var3 var2 var1 var0) (and (is-O_TSLL (read var3 var0)) (not (is-O_TSLL (read var3 var0))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_18 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_18 var3 var2 var1 var0) (and (is-O_TSLL (read var3 var0)) (not (is-O_TSLL (read var3 var0))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_13 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_19 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_29 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_36 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main1045_7 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_40 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_37 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_46 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main1059_3 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_48 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main1066_3 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var1)))))))
(check-sat)
