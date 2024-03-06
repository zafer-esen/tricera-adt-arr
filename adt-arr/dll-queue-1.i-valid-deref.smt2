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
(declare-fun inv_main (Heap Addr) Bool)
(declare-fun inv_main1002_2 (Heap Addr Addr Int) Bool)
(declare-fun inv_main1006_3 (Heap Addr Addr Int Addr) Bool)
(declare-fun inv_main1012_3 (Heap Addr Addr Int) Bool)
(declare-fun inv_main1017_3 (Heap Addr Addr Int) Bool)
(declare-fun inv_main1021_12 (Heap Addr Addr Int) Bool)
(declare-fun inv_main997_2 (Heap) Bool)
(declare-fun inv_main997_2_1 (Heap Addr) Bool)
(declare-fun inv_main_2 (Heap Addr) Bool)
(declare-fun inv_main_25 (Heap Addr Addr Int) Bool)
(declare-fun inv_main_30 (Heap Addr Addr Int) Bool)
(declare-fun inv_main_32 (Heap Addr Addr Int) Bool)
(declare-fun inv_main_35 (Heap Addr Addr Int) Bool)
(declare-fun inv_main_40 (Heap Addr Addr Int) Bool)
(declare-fun inv_main_42 (Heap Addr Addr Int) Bool)
(declare-fun inv_main_45 (Heap Addr Addr Int) Bool)
(declare-fun inv_main_48 (Heap Addr Addr Int) Bool)
(declare-fun inv_main_51 (Heap Addr Addr Int) Bool)
(declare-fun inv_main_56 (Heap Addr Addr Int) Bool)
(declare-fun inv_main_58 (Heap Addr Addr Int) Bool)
(declare-fun inv_main_59 (Heap Addr Addr Int) Bool)
(declare-fun inv_main_6 (Heap Addr Addr Int) Bool)
(declare-fun inv_main_64 (Heap Addr Addr Int) Bool)
(declare-fun inv_main_7 (Heap Addr Addr Int) Bool)
(declare-fun inv_main_8 (Heap Addr Addr Int) Bool)
(assert (forall ((var0 Heap)) (or (not (= var0 emptyHeap)) (inv_main997_2 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main_30 var3 var2 var1 var0) (and (not (= var2 nullAddr)) (= var0 3)))) (inv_main_42 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Int) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main_45 var8 var7 var6 var5) (and (and (not (= var4 nullAddr)) (and (is-O_TSLL (read var8 var7)) (is-O_TSLL (read var8 (|TSLL::next| (getTSLL (read var8 var7))))))) (and (and (and (and (= var3 var8) (= var2 var7)) (= var1 var6)) (= var0 var5)) (= var4 (|TSLL::next| (getTSLL (read var8 (|TSLL::next| (getTSLL (read var8 var7))))))))))) (inv_main_48 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Int) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main_32 var8 var7 var6 var5) (and (and (not (= var4 nullAddr)) (is-O_TSLL (read var8 var7))) (and (and (and (and (= var3 var8) (= var2 var7)) (= var1 var6)) (= var0 var5)) (= var4 (|TSLL::next| (getTSLL (read var8 var7)))))))) (inv_main_35 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main1002_2 var4 var3 var2 var1) (and (not (= var3 nullAddr)) (and (= var1 1) (and (not (= var3 nullAddr)) (= var0 0)))))) (inv_main_25 var4 var3 var2 var1))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main1006_3 var5 var4 var3 var2 var1) (and (and (is-O_TSLL (read var5 var3)) (is-O_TSLL (read var5 var3))) (= var0 (write var5 var3 (O_TSLL (TSLL var1 (|TSLL::prev| (getTSLL (read var5 var3))) (|TSLL::data| (getTSLL (read var5 var3)))))))))) (inv_main_6 var0 var4 var3 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Int) (var4 Int) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main_8 var7 var6 var5 var4) (and (= var3 1) (and (and (not (= var3 0)) (and (is-O_TSLL (read var7 var5)) (is-O_TSLL (read var7 var5)))) (and (and (and (= var2 (write var7 var5 (O_TSLL (TSLL nullAddr (|TSLL::prev| (getTSLL (read var7 var5))) (|TSLL::data| (getTSLL (read var7 var5))))))) (= var1 var6)) (= var0 var5)) (= var3 var4)))))) (inv_main1017_3 var2 var1 var0 var3))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main_30 var3 var2 var1 var0) (not (= var0 3)))) (inv_main_40 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Int) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main_51 var8 var7 var6 var5) (and (and (= var4 3) (and (and (and (is-O_TSLL (read var8 var7)) (is-O_TSLL (read var8 (|TSLL::next| (getTSLL (read var8 var7)))))) (is-O_TSLL (read var8 (|TSLL::next| (getTSLL (read var8 (|TSLL::next| (getTSLL (read var8 var7))))))))) (is-O_TSLL (read var8 (|TSLL::next| (getTSLL (read var8 (|TSLL::next| (getTSLL (read var8 (|TSLL::next| (getTSLL (read var8 var7))))))))))))) (and (and (and (and (= var3 var8) (= var2 var7)) (= var1 var6)) (= var0 var5)) (= var4 (|TSLL::data| (getTSLL (read var8 (|TSLL::next| (getTSLL (read var8 (|TSLL::next| (getTSLL (read var8 (|TSLL::next| (getTSLL (read var8 var7))))))))))))))))) (inv_main_40 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Int) (var4 Int) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main_8 var7 var6 var5 var4) (and (<= 0 (+ var3 (- 2))) (and (not (= var3 1)) (and (and (not (= var3 0)) (and (is-O_TSLL (read var7 var5)) (is-O_TSLL (read var7 var5)))) (and (and (and (= var2 (write var7 var5 (O_TSLL (TSLL nullAddr (|TSLL::prev| (getTSLL (read var7 var5))) (|TSLL::data| (getTSLL (read var7 var5))))))) (= var1 var6)) (= var0 var5)) (= var3 var4))))))) (inv_main1021_12 var2 var1 var0 var3))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Int) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main_42 var8 var7 var6 var5) (and (and (not (= var4 nullAddr)) (is-O_TSLL (read var8 var7))) (and (and (and (and (= var3 var8) (= var2 var7)) (= var1 var6)) (= var0 var5)) (= var4 (|TSLL::next| (getTSLL (read var8 var7)))))))) (inv_main_45 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 TSLL) (var2 Heap) (var3 Heap)) (or (not (and (inv_main997_2 var3) (and (= var2 (newHeap (alloc var3 (O_TSLL var1)))) (= var0 (newAddr (alloc var3 (O_TSLL var1))))))) (inv_main997_2_1 var2 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Int) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main_48 var8 var7 var6 var5) (and (and (not (= var4 nullAddr)) (and (and (is-O_TSLL (read var8 var7)) (is-O_TSLL (read var8 (|TSLL::next| (getTSLL (read var8 var7)))))) (is-O_TSLL (read var8 (|TSLL::next| (getTSLL (read var8 (|TSLL::next| (getTSLL (read var8 var7)))))))))) (and (and (and (and (= var3 var8) (= var2 var7)) (= var1 var6)) (= var0 var5)) (= var4 (|TSLL::next| (getTSLL (read var8 (|TSLL::next| (getTSLL (read var8 (|TSLL::next| (getTSLL (read var8 var7)))))))))))))) (inv_main_51 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main1002_2 var4 var3 var2 var1) (and (and (not (= var3 nullAddr)) (= var1 2)) (and (not (= var1 1)) (and (not (= var3 nullAddr)) (= var0 0)))))) (inv_main_32 var4 var3 var2 var1))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Int) (var4 Addr) (var5 Int) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main_25 var8 var7 var6 var5) (and (and (not (= var4 nullAddr)) (= var3 2)) (and (and (not (= var2 nullAddr)) (is-O_TSLL (read var8 var7))) (and (and (and (and (= var1 var8) (= var4 var7)) (= var0 var6)) (= var3 var5)) (= var2 (|TSLL::next| (getTSLL (read var8 var7))))))))) (inv_main_32 var1 var4 var0 var3))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Int) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main_35 var8 var7 var6 var5) (and (and (not (= var4 nullAddr)) (and (is-O_TSLL (read var8 var7)) (is-O_TSLL (read var8 (|TSLL::next| (getTSLL (read var8 var7))))))) (and (and (and (and (= var3 var8) (= var2 var7)) (= var1 var6)) (= var0 var5)) (= var4 (|TSLL::next| (getTSLL (read var8 (|TSLL::next| (getTSLL (read var8 var7))))))))))) (inv_main_30 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main1002_2 var4 var3 var2 var1) (and (not (= var1 2)) (and (not (= var1 1)) (and (not (= var3 nullAddr)) (= var0 0)))))) (inv_main_30 var4 var3 var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Int) (var5 Int) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main_25 var8 var7 var6 var5) (and (not (= var4 2)) (and (and (not (= var3 nullAddr)) (is-O_TSLL (read var8 var7))) (and (and (and (and (= var2 var8) (= var1 var7)) (= var0 var6)) (= var4 var5)) (= var3 (|TSLL::next| (getTSLL (read var8 var7))))))))) (inv_main_30 var2 var1 var0 var4))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main_6 var4 var3 var2 var1) (and (and (and (is-O_TSLL (read var4 var2)) (is-O_TSLL (read var4 (|TSLL::next| (getTSLL (read var4 var2)))))) (is-O_TSLL (read var4 (|TSLL::next| (getTSLL (read var4 var2)))))) (= var0 (write var4 (|TSLL::next| (getTSLL (read var4 var2))) (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var4 (|TSLL::next| (getTSLL (read var4 var2)))))) var2 (|TSLL::data| (getTSLL (read var4 (|TSLL::next| (getTSLL (read var4 var2))))))))))))) (inv_main_7 var0 var3 var2 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main_58 var3 var2 var1 var0) (= var0 0))) (inv_main_59 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Int) (var6 Addr) (var7 Addr) (var8 Heap) (var9 Int) (var10 Int) (var11 Addr) (var12 Addr) (var13 Heap)) (or (not (and (inv_main_58 var13 var12 var11 var10) (and (and (not (= var9 0)) (and (and (not (= var10 0)) (is-O_TSLL (read var13 var11))) (and (and (and (and (= var8 var13) (= var7 var12)) (= var6 var11)) (= var5 var10)) (= var4 (|TSLL::data| (getTSLL (read var13 var11))))))) (and (and (and (and (= var3 var8) (= var2 var7)) (= var1 var6)) (= var0 var5)) (or (and (<= 0 (+ var4 (- 1))) (= var9 1)) (and (not (<= 0 (+ var4 (- 1)))) (= var9 0))))))) (inv_main_59 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 TSLL) (var2 Heap) (var3 Int) (var4 Int) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main1002_2 var7 var6 var5 var4) (and (and (not (= var3 0)) (= var2 (newHeap (alloc var7 (O_TSLL var1))))) (= var0 (newAddr (alloc var7 (O_TSLL var1))))))) (inv_main1006_3 var2 var6 var5 var4 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main_56 var4 var3 var2 var1) (and (not (= var0 0)) (not (= var2 nullAddr))))) (inv_main_58 var4 var3 var2 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main_56 var3 var2 var1 var0) (and (not (= var2 nullAddr)) (= var1 nullAddr)))) (inv_main_64 var3 var2 var2 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main_56 var4 var3 var2 var1) (and (not (= var3 nullAddr)) (and (= var0 0) (not (= var2 nullAddr)))))) (inv_main_64 var4 var3 var3 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Int) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Int) (var10 Addr) (var11 Addr) (var12 Heap)) (or (not (and (inv_main_64 var12 var11 var10 var9) (and (and (not (= var8 nullAddr)) (and (is-O_TSLL (read var12 var11)) (and (and (and (and (= var7 var12) (= var6 var11)) (= var5 var10)) (= var4 var9)) (= var3 (|TSLL::next| (getTSLL (read var12 var11))))))) (and (and (and (= var2 (write var7 var5 defObj)) (= var8 var3)) (= var1 var5)) (= var0 var4))))) (inv_main_64 var2 var8 var8 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Int) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main_40 var8 var7 var6 var5) (and (is-O_TSLL (read var8 var7)) (and (and (and (and (= var4 var8) (= var3 var7)) (= var2 var6)) (= var1 var5)) (= var0 (|TSLL::next| (getTSLL (read var8 var7)))))))) (inv_main_56 var4 var3 var0 var1))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Int) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main_59 var8 var7 var6 var5) (and (is-O_TSLL (read var8 var6)) (and (and (and (and (= var4 var8) (= var3 var7)) (= var2 var6)) (= var1 var5)) (= var0 (|TSLL::next| (getTSLL (read var8 var6)))))))) (inv_main_56 var4 var3 var0 var1))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Int) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main_7 var8 var7 var6 var5) (and (is-O_TSLL (read var8 var6)) (and (and (and (and (= var4 var8) (= var3 var7)) (= var2 var6)) (= var1 var5)) (= var0 (|TSLL::next| (getTSLL (read var8 var6)))))))) (inv_main_8 var4 var3 var0 var1))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Heap)) (or (not (and (inv_main var2 var1) (and (and (is-O_TSLL (read var2 var1)) (is-O_TSLL (read var2 var1))) (= var0 (write var2 var1 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var2 var1))) nullAddr (|TSLL::data| (getTSLL (read var2 var1)))))))))) (inv_main_2 var0 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Heap)) (or (not (and (inv_main_2 var4 var3) (and (and (and (is-O_TSLL (read var4 var3)) (is-O_TSLL (read var4 var3))) (and (= var2 (write var4 var3 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var4 var3))) (|TSLL::prev| (getTSLL (read var4 var3))) 0)))) (= var1 var3))) (= var0 0)))) (inv_main1002_2 var2 var1 var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Int) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main1012_3 var8 var7 var6 var5) (and (and (and (not (= var4 nullAddr)) (not (= var3 nullAddr))) (and (and (is-O_TSLL (read var8 var6)) (is-O_TSLL (read var8 var6))) (and (and (and (= var2 (write var8 var6 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var8 var6))) (|TSLL::prev| (getTSLL (read var8 var6))) 1)))) (= var3 var7)) (= var4 var6)) (= var1 var5)))) (= var0 1)))) (inv_main1002_2 var2 var3 var4 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Int) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main1017_3 var8 var7 var6 var5) (and (and (and (not (= var4 nullAddr)) (not (= var3 nullAddr))) (and (and (is-O_TSLL (read var8 var6)) (is-O_TSLL (read var8 var6))) (and (and (and (= var2 (write var8 var6 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var8 var6))) (|TSLL::prev| (getTSLL (read var8 var6))) 2)))) (= var3 var7)) (= var4 var6)) (= var1 var5)))) (= var0 2)))) (inv_main1002_2 var2 var3 var4 var0))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Addr) (var3 Addr) (var4 Int) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main_8 var7 var6 var5 var4) (and (and (not (= var3 nullAddr)) (not (= var2 nullAddr))) (and (not (<= 0 (+ var1 (- 2)))) (and (not (= var1 1)) (and (and (not (= var1 0)) (and (is-O_TSLL (read var7 var5)) (is-O_TSLL (read var7 var5)))) (and (and (and (= var0 (write var7 var5 (O_TSLL (TSLL nullAddr (|TSLL::prev| (getTSLL (read var7 var5))) (|TSLL::data| (getTSLL (read var7 var5))))))) (= var2 var6)) (= var3 var5)) (= var1 var4)))))))) (inv_main1002_2 var0 var2 var3 var1))))
(assert (forall ((var0 Int) (var1 Int) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Int) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main1021_12 var8 var7 var6 var5) (and (and (and (not (= var4 nullAddr)) (not (= var3 nullAddr))) (and (and (is-O_TSLL (read var8 var6)) (is-O_TSLL (read var8 var6))) (and (and (and (= var2 (write var8 var6 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var8 var6))) (|TSLL::prev| (getTSLL (read var8 var6))) 3)))) (= var3 var7)) (= var4 var6)) (= var1 var5)))) (= var0 3)))) (inv_main1002_2 var2 var3 var4 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Int) (var4 Int) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main_8 var7 var6 var5 var4) (and (and (= var3 0) (and (is-O_TSLL (read var7 var5)) (is-O_TSLL (read var7 var5)))) (and (and (and (= var2 (write var7 var5 (O_TSLL (TSLL nullAddr (|TSLL::prev| (getTSLL (read var7 var5))) (|TSLL::data| (getTSLL (read var7 var5))))))) (= var1 var6)) (= var0 var5)) (= var3 var4))))) (inv_main1012_3 var2 var1 var0 var3))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Heap)) (or (not (and (inv_main997_2_1 var2 var1) (and (and (is-O_TSLL (read var2 var1)) (is-O_TSLL (read var2 var1))) (= var0 (write var2 var1 (O_TSLL (TSLL nullAddr (|TSLL::prev| (getTSLL (read var2 var1))) (|TSLL::data| (getTSLL (read var2 var1)))))))))) (inv_main var0 var1))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main997_2_1 var1 var0) (not (is-O_TSLL (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main997_2_1 var1 var0) (and (is-O_TSLL (read var1 var0)) (not (is-O_TSLL (read var1 var0))))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main var1 var0) (not (is-O_TSLL (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main var1 var0) (and (is-O_TSLL (read var1 var0)) (not (is-O_TSLL (read var1 var0))))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main_2 var1 var0) (not (is-O_TSLL (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main_2 var1 var0) (and (is-O_TSLL (read var1 var0)) (not (is-O_TSLL (read var1 var0))))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main1006_3 var4 var3 var2 var1 var0) (not (is-O_TSLL (read var4 var2)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main1006_3 var4 var3 var2 var1 var0) (and (is-O_TSLL (read var4 var2)) (not (is-O_TSLL (read var4 var2))))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_6 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var1)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_6 var3 var2 var1 var0) (and (is-O_TSLL (read var3 var1)) (not (is-O_TSLL (read var3 (|TSLL::next| (getTSLL (read var3 var1)))))))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_6 var3 var2 var1 var0) (and (and (is-O_TSLL (read var3 var1)) (is-O_TSLL (read var3 (|TSLL::next| (getTSLL (read var3 var1)))))) (not (is-O_TSLL (read var3 (|TSLL::next| (getTSLL (read var3 var1)))))))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_7 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var1)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_8 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var1)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_8 var3 var2 var1 var0) (and (is-O_TSLL (read var3 var1)) (not (is-O_TSLL (read var3 var1))))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main1012_3 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var1)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main1012_3 var3 var2 var1 var0) (and (is-O_TSLL (read var3 var1)) (not (is-O_TSLL (read var3 var1))))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main1017_3 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var1)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main1017_3 var3 var2 var1 var0) (and (is-O_TSLL (read var3 var1)) (not (is-O_TSLL (read var3 var1))))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main1021_12 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var1)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main1021_12 var3 var2 var1 var0) (and (is-O_TSLL (read var3 var1)) (not (is-O_TSLL (read var3 var1))))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_25 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var2)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_32 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var2)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_35 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var2)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_35 var3 var2 var1 var0) (and (is-O_TSLL (read var3 var2)) (not (is-O_TSLL (read var3 (|TSLL::next| (getTSLL (read var3 var2)))))))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_42 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var2)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_45 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var2)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_45 var3 var2 var1 var0) (and (is-O_TSLL (read var3 var2)) (not (is-O_TSLL (read var3 (|TSLL::next| (getTSLL (read var3 var2)))))))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_48 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var2)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_48 var3 var2 var1 var0) (and (is-O_TSLL (read var3 var2)) (not (is-O_TSLL (read var3 (|TSLL::next| (getTSLL (read var3 var2)))))))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_48 var3 var2 var1 var0) (and (and (is-O_TSLL (read var3 var2)) (is-O_TSLL (read var3 (|TSLL::next| (getTSLL (read var3 var2)))))) (not (is-O_TSLL (read var3 (|TSLL::next| (getTSLL (read var3 (|TSLL::next| (getTSLL (read var3 var2))))))))))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_51 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var2)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_51 var3 var2 var1 var0) (and (is-O_TSLL (read var3 var2)) (not (is-O_TSLL (read var3 (|TSLL::next| (getTSLL (read var3 var2)))))))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_51 var3 var2 var1 var0) (and (and (is-O_TSLL (read var3 var2)) (is-O_TSLL (read var3 (|TSLL::next| (getTSLL (read var3 var2)))))) (not (is-O_TSLL (read var3 (|TSLL::next| (getTSLL (read var3 (|TSLL::next| (getTSLL (read var3 var2))))))))))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_51 var3 var2 var1 var0) (and (and (and (is-O_TSLL (read var3 var2)) (is-O_TSLL (read var3 (|TSLL::next| (getTSLL (read var3 var2)))))) (is-O_TSLL (read var3 (|TSLL::next| (getTSLL (read var3 (|TSLL::next| (getTSLL (read var3 var2))))))))) (not (is-O_TSLL (read var3 (|TSLL::next| (getTSLL (read var3 (|TSLL::next| (getTSLL (read var3 (|TSLL::next| (getTSLL (read var3 var2)))))))))))))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_40 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var2)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_58 var3 var2 var1 var0) (and (not (= var0 0)) (not (is-O_TSLL (read var3 var1))))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_59 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var1)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_64 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var2)))))))
(check-sat)
