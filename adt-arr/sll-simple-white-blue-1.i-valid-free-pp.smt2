(set-logic HORN)
(set-info :source |
    Benchmark: 
    Output by Princess (http://www.philipp.ruemmer.org/princess.shtml)
|)
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
(declare-fun _Glue17 (Heap Addr Addr Addr HeapObject) Bool)
(declare-fun _Glue6 (Heap Addr Addr Addr Addr HeapObject) Bool)
(declare-fun _Glue24 (Heap Addr Addr HeapObject) Bool)
(declare-fun _Glue19 (Addr Addr Addr Heap HeapObject) Bool)
(declare-fun inv_main1003_2 (Heap Addr Addr) Bool)
(declare-fun _Glue2 (Addr Addr Addr Addr Addr Heap HeapObject) Bool)
(declare-fun Inv_Heap (Addr HeapObject) Bool)
(declare-fun _Glue21 (Heap Addr HeapObject) Bool)
(declare-fun _Glue0_exp_exp (Addr Addr Addr Int Addr Heap Addr HeapObject) Bool)
(declare-fun _Glue4 (Heap Addr Addr Addr Addr HeapObject) Bool)
(declare-fun inv_main_12 (Heap Addr Addr) Bool)
(declare-fun _Glue27 (Addr Addr Heap HeapObject) Bool)
(declare-fun _Glue29 (Heap Addr HeapObject) Bool)
(declare-fun _Glue15 (Heap Addr Addr Addr HeapObject) Bool)
(declare-fun _Glue10 (Heap Addr Addr HeapObject) Bool)
(declare-fun inv_main_20 (Heap Addr Addr) Bool)
(declare-fun _Glue8 (Addr Addr Heap HeapObject) Bool)
(declare-fun inv_main_35 (Heap Addr Addr) Bool)
(declare-fun _Glue22 (Addr Heap Addr HeapObject) Bool)
(declare-fun _Glue13 (Addr Addr Addr Addr Heap HeapObject) Bool)
(declare-fun inv_main_23 (Heap Addr Addr) Bool)
(declare-fun _Glue11_exp_exp (Addr Addr Addr Int Addr Heap Addr HeapObject) Bool)
(assert (forall ((var0 AllocResHeap) (var1 Heap) (var2 HeapObject) (var3 TSLL)) (or (not (and (and (= (O_TSLL var3) var2) (= (alloc var1 var2) var0)) (= emptyHeap var1))) (Inv_Heap (newAddr var0) var2))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 HeapObject) (var3 TSLL) (var4 AllocResHeap) (var5 Heap) (var6 HeapObject) (var7 Addr)) (or (not (and (Inv_Heap var7 var6) (and (and (and (and (and (and (= (read var5 var7) var6) (valid var5 var7)) (= (AllocResHeap var5 var7) var4)) (= (O_TSLL var3) var2)) (= (alloc var1 var2) var4)) (= nullAddr var0)) (= emptyHeap var1)))) (_Glue27 var7 var0 var5 var6))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 HeapObject) (var3 TSLL) (var4 AllocResHeap) (var5 HeapObject) (var6 Addr) (var7 Heap)) (or (not (and (and (and (and (and (and (= (read var7 var6) var5) (not (valid var7 var6))) (= (AllocResHeap var7 var6) var4)) (= (O_TSLL var3) var2)) (= (alloc var1 var2) var4)) (= nullAddr var0)) (= emptyHeap var1))) (_Glue27 var6 var0 var7 var5))))
(assert (forall ((var0 HeapObject) (var1 TSLL) (var2 Int) (var3 TSLL) (var4 HeapObject) (var5 Heap) (var6 Addr) (var7 Addr)) (or (not (and (_Glue27 var7 var6 var5 var4) (and (and (and (and (= (getTSLL var4) var3) (= (|TSLL::data| var3) var2)) (= (TSLL var6 var2) var1)) (= (O_TSLL var1) var0)) (valid var5 var7)))) (Inv_Heap var7 var0))))
(assert (forall ((var0 HeapObject) (var1 TSLL) (var2 Int) (var3 TSLL) (var4 Heap) (var5 HeapObject) (var6 Heap) (var7 Addr) (var8 HeapObject) (var9 Addr)) (or (not (and (and (Inv_Heap var9 var8) (_Glue27 var9 var7 var6 var5)) (and (and (and (and (and (and (= (read var4 var9) var8) (valid var4 var9)) (= (getTSLL var5) var3)) (= (|TSLL::data| var3) var2)) (= (TSLL var7 var2) var1)) (= (O_TSLL var1) var0)) (= (write var6 var9 var0) var4)))) (_Glue29 var4 var9 var8))))
(assert (forall ((var0 HeapObject) (var1 TSLL) (var2 Int) (var3 TSLL) (var4 HeapObject) (var5 Heap) (var6 HeapObject) (var7 Heap) (var8 Addr) (var9 Addr)) (or (not (and (_Glue27 var9 var8 var7 var6) (and (and (and (and (and (and (= (read var5 var9) var4) (not (valid var5 var9))) (= (getTSLL var6) var3)) (= (|TSLL::data| var3) var2)) (= (TSLL var8 var2) var1)) (= (O_TSLL var1) var0)) (= (write var7 var9 var0) var5)))) (_Glue29 var5 var9 var4))))
(assert (forall ((var0 HeapObject) (var1 TSLL) (var2 Addr) (var3 TSLL) (var4 HeapObject) (var5 Addr) (var6 Heap)) (or (not (and (_Glue29 var6 var5 var4) (and (and (and (and (= (getTSLL var4) var3) (= (|TSLL::next| var3) var2)) (= (TSLL var2 0) var1)) (= (O_TSLL var1) var0)) (valid var6 var5)))) (Inv_Heap var5 var0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 HeapObject) (var3 TSLL) (var4 Addr) (var5 TSLL) (var6 HeapObject) (var7 Addr) (var8 Heap)) (or (not (and (_Glue29 var8 var7 var6) (and (and (and (and (and (= (getTSLL var6) var5) (= (|TSLL::next| var5) var4)) (= (TSLL var4 0) var3)) (= (O_TSLL var3) var2)) (= (write var8 var7 var2) var1)) (= var0 var7)))) (inv_main1003_2 var1 var7 var0))))
(assert (forall ((var0 AllocResHeap) (var1 HeapObject) (var2 TSLL) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main1003_2 var5 var4 var3) (and (= (O_TSLL var2) var1) (= (alloc var5 var1) var0)))) (Inv_Heap (newAddr var0) var1))))
(assert (forall ((var0 AllocResHeap) (var1 Addr) (var2 HeapObject) (var3 TSLL) (var4 Heap) (var5 Addr) (var6 Heap) (var7 HeapObject) (var8 Addr)) (or (not (and (and (Inv_Heap var8 var7) (inv_main1003_2 var6 var5 var8)) (and (and (and (and (and (= (read var4 var8) var7) (valid var4 var8)) true) (= (O_TSLL var3) var2)) (= (AllocResHeap var4 var1) var0)) (= (alloc var6 var2) var0)))) (_Glue19 var8 var5 var1 var4 var7))))
(assert (forall ((var0 AllocResHeap) (var1 Addr) (var2 HeapObject) (var3 TSLL) (var4 HeapObject) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main1003_2 var8 var7 var6) (and (and (and (and (= (read var5 var6) var4) (not (valid var5 var6))) (= (O_TSLL var3) var2)) (= (AllocResHeap var5 var1) var0)) (= (alloc var8 var2) var0)))) (_Glue19 var6 var7 var1 var5 var4))))
(assert (forall ((var0 HeapObject) (var1 TSLL) (var2 Int) (var3 TSLL) (var4 HeapObject) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr)) (or (not (and (_Glue19 var8 var7 var6 var5 var4) (and (and (and (and (= (getTSLL var4) var3) (= (|TSLL::data| var3) var2)) (= (TSLL var6 var2) var1)) (= (O_TSLL var1) var0)) (valid var5 var8)))) (Inv_Heap var8 var0))))
(assert (forall ((var0 HeapObject) (var1 TSLL) (var2 Int) (var3 TSLL) (var4 Heap) (var5 HeapObject) (var6 Heap) (var7 Addr) (var8 Addr) (var9 HeapObject) (var10 Addr)) (or (not (and (and (Inv_Heap var10 var9) (_Glue19 var10 var8 var7 var6 var5)) (and (and (and (and (and (and (and (= (read var4 var10) var9) (valid var4 var10)) true) (= (getTSLL var5) var3)) (= (|TSLL::data| var3) var2)) (= (TSLL var7 var2) var1)) (= (O_TSLL var1) var0)) (= (write var6 var10 var0) var4)))) (_Glue21 var4 var8 var9))))
(assert (forall ((var0 HeapObject) (var1 TSLL) (var2 Int) (var3 TSLL) (var4 HeapObject) (var5 Heap) (var6 HeapObject) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Addr)) (or (not (and (_Glue19 var10 var9 var8 var7 var6) (and (and (and (and (and (and (= (read var5 var10) var4) (not (valid var5 var10))) (= (getTSLL var6) var3)) (= (|TSLL::data| var3) var2)) (= (TSLL var8 var2) var1)) (= (O_TSLL var1) var0)) (= (write var7 var10 var0) var5)))) (_Glue21 var5 var9 var4))))
(assert (forall ((var0 TSLL) (var1 HeapObject) (var2 Addr) (var3 Heap) (var4 HeapObject) (var5 Addr)) (or (not (and (and (Inv_Heap var5 var4) (_Glue21 var3 var2 var1)) (and (and (and (= (getTSLL var1) var0) (= (|TSLL::next| var0) var5)) (= (read var3 var5) var4)) (valid var3 var5)))) (_Glue22 var2 var3 var5 var4))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 TSLL) (var3 HeapObject) (var4 Addr) (var5 Heap)) (or (not (and (_Glue21 var5 var4 var3) (and (and (and (= (getTSLL var3) var2) (= (|TSLL::next| var2) var1)) (= (read var5 var1) var0)) (not (valid var5 var1))))) (_Glue22 var4 var5 var1 var0))))
(assert (forall ((var0 HeapObject) (var1 TSLL) (var2 Addr) (var3 TSLL) (var4 HeapObject) (var5 Addr) (var6 Heap) (var7 Addr)) (or (not (and (_Glue22 var7 var6 var5 var4) (and (and (and (and (= (getTSLL var4) var3) (= (|TSLL::next| var3) var2)) (= (TSLL var2 0) var1)) (= (O_TSLL var1) var0)) (valid var6 var5)))) (Inv_Heap var5 var0))))
(assert (forall ((var0 HeapObject) (var1 TSLL) (var2 Addr) (var3 TSLL) (var4 Heap) (var5 HeapObject) (var6 Heap) (var7 Addr) (var8 HeapObject) (var9 Addr)) (or (not (and (and (Inv_Heap var9 var8) (_Glue22 var7 var6 var9 var5)) (and (and (and (and (and (and (and (= (read var4 var9) var8) (valid var4 var9)) true) (= (getTSLL var5) var3)) (= (|TSLL::next| var3) var2)) (= (TSLL var2 0) var1)) (= (O_TSLL var1) var0)) (= (write var6 var9 var0) var4)))) (_Glue24 var4 var7 var9 var8))))
(assert (forall ((var0 HeapObject) (var1 TSLL) (var2 Addr) (var3 TSLL) (var4 HeapObject) (var5 Heap) (var6 HeapObject) (var7 Addr) (var8 Heap) (var9 Addr)) (or (not (and (_Glue22 var9 var8 var7 var6) (and (and (and (and (and (and (= (read var5 var7) var4) (not (valid var5 var7))) (= (getTSLL var6) var3)) (= (|TSLL::next| var3) var2)) (= (TSLL var2 0) var1)) (= (O_TSLL var1) var0)) (= (write var8 var7 var0) var5)))) (_Glue24 var5 var9 var7 var4))))
(assert (forall ((var0 HeapObject) (var1 TSLL) (var2 Addr) (var3 Int) (var4 TSLL) (var5 HeapObject) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (_Glue24 var8 var7 var6 var5) (and (and (and (and (and (= (getTSLL var5) var4) (= (|TSLL::data| var4) var3)) (= nullAddr var2)) (= (TSLL var2 var3) var1)) (= (O_TSLL var1) var0)) (valid var8 var6)))) (Inv_Heap var6 var0))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 TSLL) (var3 Addr) (var4 Int) (var5 TSLL) (var6 HeapObject) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (_Glue24 var9 var8 var7 var6) (and (and (and (and (and (= (getTSLL var6) var5) (= (|TSLL::data| var5) var4)) (= nullAddr var3)) (= (TSLL var3 var4) var2)) (= (O_TSLL var2) var1)) (= (write var9 var7 var1) var0)))) (inv_main1003_2 var0 var8 var7))))
(assert (forall ((var0 TSLL) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 HeapObject) (var6 Addr)) (or (not (and (and (Inv_Heap var6 var5) (inv_main_12 var4 var3 var6)) (and (and (and (and (and (not (= var2 var1)) (= (read var4 var6) var5)) (= (getTSLL var5) var0)) (= (|TSLL::next| var0) var2)) (= nullAddr var1)) (valid var4 var6)))) (inv_main_12 var4 var3 var2))))
(assert (forall ((var0 TSLL) (var1 HeapObject) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main_12 var6 var5 var4) (and (and (and (and (and (not (= var3 var2)) (= (read var6 var4) var1)) (= (getTSLL var1) var0)) (= (|TSLL::next| var0) var3)) (= nullAddr var2)) (not (valid var6 var4))))) (inv_main_12 var6 var5 var3))))
(assert (forall ((var0 Addr) (var1 TSLL) (var2 Addr) (var3 Heap) (var4 HeapObject) (var5 Addr)) (or (not (and (and (Inv_Heap var5 var4) (inv_main_23 var3 var5 var2)) (and (and (and (and (and (not (= var5 var2)) (= nullAddr var2)) (= (read var3 var5) var4)) (= (getTSLL var4) var1)) (= (|TSLL::next| var1) var0)) (valid var3 var5)))) (inv_main_35 var3 var5 var0))))
(assert (forall ((var0 Addr) (var1 TSLL) (var2 HeapObject) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main_23 var5 var4 var3) (and (and (and (and (and (not (= var4 var3)) (= nullAddr var3)) (= (read var5 var4) var2)) (= (getTSLL var2) var1)) (= (|TSLL::next| var1) var0)) (not (valid var5 var4))))) (inv_main_35 var5 var4 var0))))
(assert (forall ((var0 Addr) (var1 TSLL) (var2 Addr) (var3 Heap) (var4 HeapObject) (var5 Addr)) (or (not (and (and (Inv_Heap var5 var4) (inv_main_20 var3 var2 var5)) (and (and (and (and (= (read var3 var5) var4) (= (getTSLL var4) var1)) (= (|TSLL::data| var1) 1)) (= (|TSLL::next| var1) var0)) (valid var3 var5)))) (inv_main_23 var3 var2 var0))))
(assert (forall ((var0 Addr) (var1 TSLL) (var2 HeapObject) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main_20 var5 var4 var3) (and (and (and (and (= (read var5 var3) var2) (= (getTSLL var2) var1)) (= (|TSLL::data| var1) 1)) (= (|TSLL::next| var1) var0)) (not (valid var5 var3))))) (inv_main_23 var5 var4 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 TSLL) (var3 Addr) (var4 Heap) (var5 HeapObject) (var6 Addr)) (or (not (and (and (Inv_Heap var6 var5) (inv_main_20 var4 var3 var6)) (and (and (and (and (and (= (read var4 var6) var5) (= (getTSLL var5) var2)) (= (|TSLL::data| var2) var1)) (= (|TSLL::next| var2) var0)) (not (= var1 1))) (valid var4 var6)))) (inv_main_20 var4 var3 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 TSLL) (var3 HeapObject) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main_20 var6 var5 var4) (and (and (and (and (and (= (read var6 var4) var3) (= (getTSLL var3) var2)) (= (|TSLL::data| var2) var1)) (= (|TSLL::next| var2) var0)) (not (= var1 1))) (not (valid var6 var4))))) (inv_main_20 var6 var5 var0))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main_35 var4 var3 var2) (and (and (and (= nullAddr var1) (not (= var2 var1))) (= defObj var0)) (valid var4 var3)))) (Inv_Heap var3 var0))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 TSLL) (var4 Heap) (var5 Addr) (var6 Heap) (var7 HeapObject) (var8 Addr)) (or (not (and (and (Inv_Heap var8 var7) (inv_main_35 var6 var5 var8)) (and (and (and (and (and (and (and (and (= (read var4 var8) var7) (= (getTSLL var7) var3)) (= (|TSLL::next| var3) var2)) (valid var4 var8)) true) (= nullAddr var1)) (not (= var8 var1))) (= defObj var0)) (= (write var6 var5 var0) var4)))) (inv_main_35 var4 var8 var2))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 TSLL) (var4 HeapObject) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main_35 var8 var7 var6) (and (and (and (and (and (and (and (= (read var5 var6) var4) (= (getTSLL var4) var3)) (= (|TSLL::next| var3) var2)) (not (valid var5 var6))) (= nullAddr var1)) (not (= var6 var1))) (= defObj var0)) (= (write var8 var7 var0) var5)))) (inv_main_35 var5 var6 var2))))
(assert (forall ((var0 AllocResHeap) (var1 HeapObject) (var2 TSLL) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main1003_2 var5 var4 var3) (and (= (O_TSLL var2) var1) (= (alloc var5 var1) var0)))) (Inv_Heap (newAddr var0) var1))))
(assert (forall ((var0 AllocResHeap) (var1 HeapObject) (var2 TSLL) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Heap) (var7 HeapObject) (var8 Addr)) (or (not (and (and (Inv_Heap var8 var7) (inv_main1003_2 var6 var5 var4)) (and (and (and (and (= (read var3 var8) var7) (valid var3 var8)) (= (O_TSLL var2) var1)) (= (AllocResHeap var3 var8) var0)) (= (alloc var6 var1) var0)))) (_Glue8 var5 var8 var3 var7))))
(assert (forall ((var0 AllocResHeap) (var1 HeapObject) (var2 TSLL) (var3 HeapObject) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main1003_2 var8 var7 var6) (and (and (and (and (= (read var5 var4) var3) (not (valid var5 var4))) (= (O_TSLL var2) var1)) (= (AllocResHeap var5 var4) var0)) (= (alloc var8 var1) var0)))) (_Glue8 var7 var4 var5 var3))))
(assert (forall ((var0 HeapObject) (var1 TSLL) (var2 Addr) (var3 TSLL) (var4 HeapObject) (var5 Heap) (var6 Addr) (var7 Addr)) (or (not (and (_Glue8 var7 var6 var5 var4) (and (and (and (and (= (getTSLL var4) var3) (= (|TSLL::next| var3) var2)) (= (TSLL var2 1) var1)) (= (O_TSLL var1) var0)) (valid var5 var6)))) (Inv_Heap var6 var0))))
(assert (forall ((var0 HeapObject) (var1 TSLL) (var2 Addr) (var3 TSLL) (var4 Heap) (var5 HeapObject) (var6 Heap) (var7 Addr) (var8 HeapObject) (var9 Addr)) (or (not (and (and (Inv_Heap var9 var8) (_Glue8 var7 var9 var6 var5)) (and (and (and (and (and (and (= (read var4 var9) var8) (valid var4 var9)) (= (getTSLL var5) var3)) (= (|TSLL::next| var3) var2)) (= (TSLL var2 1) var1)) (= (O_TSLL var1) var0)) (= (write var6 var9 var0) var4)))) (_Glue10 var4 var7 var9 var8))))
(assert (forall ((var0 HeapObject) (var1 TSLL) (var2 Addr) (var3 TSLL) (var4 HeapObject) (var5 Heap) (var6 HeapObject) (var7 Heap) (var8 Addr) (var9 Addr)) (or (not (and (_Glue8 var9 var8 var7 var6) (and (and (and (and (and (and (= (read var5 var8) var4) (not (valid var5 var8))) (= (getTSLL var6) var3)) (= (|TSLL::next| var3) var2)) (= (TSLL var2 1) var1)) (= (O_TSLL var1) var0)) (= (write var7 var8 var0) var5)))) (_Glue10 var5 var9 var8 var4))))
(assert (forall ((var0 HeapObject) (var1 TSLL) (var2 Int) (var3 TSLL) (var4 HeapObject) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (_Glue10 var7 var6 var5 var4) (and (and (and (and (= (getTSLL var4) var3) (= (|TSLL::data| var3) var2)) (= (TSLL var6 var2) var1)) (= (O_TSLL var1) var0)) (valid var7 var5)))) (Inv_Heap var5 var0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 HeapObject) (var3 TSLL) (var4 Int) (var5 TSLL) (var6 HeapObject) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (_Glue10 var9 var8 var7 var6) (and (and (and (and (and (= (getTSLL var6) var5) (= (|TSLL::data| var5) var4)) (= (TSLL var8 var4) var3)) (= (O_TSLL var3) var2)) (= (write var9 var7 var2) var1)) (= var0 var7)))) (inv_main_20 var1 var7 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 HeapObject) (var7 Addr)) (or (not (and (and (Inv_Heap var7 var6) (inv_main_12 var5 var4 var7)) (and (and (= nullAddr var3) (= (read var5 var7) var6)) (valid var5 var7)))) (_Glue0_exp_exp var2 var3 var1 var0 var4 var5 var7 var6))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 HeapObject) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main_12 var7 var6 var5) (and (and (= nullAddr var4) (= (read var7 var5) var3)) (not (valid var7 var5))))) (_Glue0_exp_exp var2 var4 var1 var0 var6 var7 var5 var3))))
(assert (forall ((var0 AllocResHeap) (var1 Addr) (var2 TSLL) (var3 HeapObject) (var4 TSLL) (var5 HeapObject) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Int) (var10 Addr) (var11 Addr) (var12 Addr)) (or (not (and (_Glue0_exp_exp var12 var11 var10 var9 var8 var7 var6 var5) (and (and (and (and (and (= (O_TSLL var4) var3) (= (TSLL var10 var9) var4)) (= (getTSLL var5) var2)) (= (|TSLL::next| var2) var1)) (not (= var1 var11))) (= (alloc var7 var3) var0)))) (Inv_Heap (newAddr var0) var3))))
(assert (forall ((var0 Addr) (var1 TSLL) (var2 HeapObject) (var3 TSLL) (var4 AllocResHeap) (var5 Addr) (var6 Heap) (var7 HeapObject) (var8 Heap) (var9 Addr) (var10 Int) (var11 Addr) (var12 Addr) (var13 Addr) (var14 HeapObject) (var15 Addr)) (or (not (and (and (Inv_Heap var15 var14) (_Glue0_exp_exp var13 var12 var11 var10 var9 var8 var15 var7)) (and (and (and (and (and (and (and (and (= (AllocResHeap var6 var5) var4) (= (O_TSLL var3) var2)) (= (TSLL var11 var10) var3)) (= (read var6 var15) var14)) (valid var6 var15)) (= (getTSLL var7) var1)) (= (|TSLL::next| var1) var0)) (not (= var0 var12))) (= (alloc var8 var2) var4)))) (_Glue2 var0 var13 var9 var15 var5 var6 var14))))
(assert (forall ((var0 Addr) (var1 TSLL) (var2 HeapObject) (var3 HeapObject) (var4 TSLL) (var5 AllocResHeap) (var6 Addr) (var7 Heap) (var8 HeapObject) (var9 Addr) (var10 Heap) (var11 Addr) (var12 Int) (var13 Addr) (var14 Addr) (var15 Addr)) (or (not (and (_Glue0_exp_exp var15 var14 var13 var12 var11 var10 var9 var8) (and (and (and (and (and (and (and (and (= (AllocResHeap var7 var6) var5) (= (O_TSLL var4) var3)) (= (TSLL var13 var12) var4)) (= (read var7 var9) var2)) (not (valid var7 var9))) (= (getTSLL var8) var1)) (= (|TSLL::next| var1) var0)) (not (= var0 var14))) (= (alloc var10 var3) var5)))) (_Glue2 var0 var15 var11 var9 var6 var7 var2))))
(assert (forall ((var0 HeapObject) (var1 TSLL) (var2 Int) (var3 TSLL) (var4 HeapObject) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr)) (or (not (and (_Glue2 var10 var9 var8 var7 var6 var5 var4) (and (and (and (and (= (getTSLL var4) var3) (= (|TSLL::data| var3) var2)) (= (TSLL var6 var2) var1)) (= (O_TSLL var1) var0)) (valid var5 var7)))) (Inv_Heap var7 var0))))
(assert (forall ((var0 HeapObject) (var1 TSLL) (var2 Int) (var3 TSLL) (var4 Heap) (var5 HeapObject) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 HeapObject) (var12 Addr)) (or (not (and (and (Inv_Heap var12 var11) (_Glue2 var10 var9 var8 var12 var7 var6 var5)) (and (and (and (and (and (and (and (= (read var4 var12) var11) (valid var4 var12)) true) (= (getTSLL var5) var3)) (= (|TSLL::data| var3) var2)) (= (TSLL var7 var2) var1)) (= (O_TSLL var1) var0)) (= (write var6 var12 var0) var4)))) (_Glue4 var4 var10 var9 var8 var12 var11))))
(assert (forall ((var0 HeapObject) (var1 TSLL) (var2 Int) (var3 TSLL) (var4 HeapObject) (var5 Heap) (var6 HeapObject) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr)) (or (not (and (_Glue2 var12 var11 var10 var9 var8 var7 var6) (and (and (and (and (and (and (= (read var5 var9) var4) (not (valid var5 var9))) (= (getTSLL var6) var3)) (= (|TSLL::data| var3) var2)) (= (TSLL var8 var2) var1)) (= (O_TSLL var1) var0)) (= (write var7 var9 var0) var5)))) (_Glue4 var5 var12 var11 var10 var9 var4))))
(assert (forall ((var0 HeapObject) (var1 TSLL) (var2 Addr) (var3 TSLL) (var4 HeapObject) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (_Glue4 var9 var8 var7 var6 var5 var4) (and (and (and (and (= (getTSLL var4) var3) (= (|TSLL::next| var3) var2)) (= (TSLL var2 1) var1)) (= (O_TSLL var1) var0)) (valid var9 var5)))) (Inv_Heap var5 var0))))
(assert (forall ((var0 HeapObject) (var1 TSLL) (var2 Addr) (var3 TSLL) (var4 Heap) (var5 HeapObject) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap) (var10 HeapObject) (var11 Addr)) (or (not (and (and (Inv_Heap var11 var10) (_Glue4 var9 var8 var7 var6 var11 var5)) (and (and (and (and (and (and (and (= (read var4 var11) var10) (valid var4 var11)) true) (= (getTSLL var5) var3)) (= (|TSLL::next| var3) var2)) (= (TSLL var2 1) var1)) (= (O_TSLL var1) var0)) (= (write var9 var11 var0) var4)))) (_Glue6 var4 var8 var7 var6 var11 var10))))
(assert (forall ((var0 HeapObject) (var1 TSLL) (var2 Addr) (var3 TSLL) (var4 HeapObject) (var5 Heap) (var6 HeapObject) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Heap)) (or (not (and (_Glue4 var11 var10 var9 var8 var7 var6) (and (and (and (and (and (and (= (read var5 var7) var4) (not (valid var5 var7))) (= (getTSLL var6) var3)) (= (|TSLL::next| var3) var2)) (= (TSLL var2 1) var1)) (= (O_TSLL var1) var0)) (= (write var11 var7 var0) var5)))) (_Glue6 var5 var10 var9 var8 var7 var4))))
(assert (forall ((var0 HeapObject) (var1 TSLL) (var2 Int) (var3 TSLL) (var4 HeapObject) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (_Glue6 var8 var7 var6 var6 var5 var4) (and (and (and (and (= (getTSLL var4) var3) (= (|TSLL::data| var3) var2)) (= (TSLL var7 var2) var1)) (= (O_TSLL var1) var0)) (valid var8 var5)))) (Inv_Heap var5 var0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 HeapObject) (var3 TSLL) (var4 Int) (var5 TSLL) (var6 HeapObject) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (_Glue6 var10 var9 var8 var8 var7 var6) (and (and (and (and (and (= (getTSLL var6) var5) (= (|TSLL::data| var5) var4)) (= (TSLL var9 var4) var3)) (= (O_TSLL var3) var2)) (= (write var10 var7 var2) var1)) (= var0 var8)))) (inv_main_20 var1 var0 var8))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 HeapObject) (var7 Addr)) (or (not (and (and (Inv_Heap var7 var6) (inv_main_12 var5 var4 var7)) (and (= (read var5 var7) var6) (valid var5 var7)))) (_Glue11_exp_exp var3 var2 var1 var0 var4 var5 var7 var6))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 HeapObject) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main_12 var7 var6 var5) (and (= (read var7 var5) var4) (not (valid var7 var5))))) (_Glue11_exp_exp var3 var2 var1 var0 var6 var7 var5 var4))))
(assert (forall ((var0 AllocResHeap) (var1 TSLL) (var2 HeapObject) (var3 TSLL) (var4 HeapObject) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Int) (var9 Addr) (var10 Addr) (var11 Addr)) (or (not (and (_Glue11_exp_exp var11 var10 var9 var8 var7 var6 var5 var4) (and (and (and (and (and (= (O_TSLL var3) var2) (= (TSLL var9 var8) var3)) (= nullAddr var11)) (= (getTSLL var4) var1)) (= (|TSLL::next| var1) var11)) (= (alloc var6 var2) var0)))) (Inv_Heap (newAddr var0) var2))))
(assert (forall ((var0 TSLL) (var1 HeapObject) (var2 TSLL) (var3 AllocResHeap) (var4 Addr) (var5 Heap) (var6 HeapObject) (var7 Heap) (var8 Addr) (var9 Int) (var10 Addr) (var11 Addr) (var12 Addr) (var13 HeapObject) (var14 Addr)) (or (not (and (and (Inv_Heap var14 var13) (_Glue11_exp_exp var12 var11 var10 var9 var8 var7 var14 var6)) (and (and (and (and (and (and (and (and (= (AllocResHeap var5 var4) var3) (= (O_TSLL var2) var1)) (= (TSLL var10 var9) var2)) (= (read var5 var14) var13)) (valid var5 var14)) (= nullAddr var12)) (= (getTSLL var6) var0)) (= (|TSLL::next| var0) var12)) (= (alloc var7 var1) var3)))) (_Glue13 var11 var8 var14 var4 var5 var13))))
(assert (forall ((var0 TSLL) (var1 HeapObject) (var2 HeapObject) (var3 TSLL) (var4 AllocResHeap) (var5 Addr) (var6 Heap) (var7 HeapObject) (var8 Addr) (var9 Heap) (var10 Addr) (var11 Int) (var12 Addr) (var13 Addr) (var14 Addr)) (or (not (and (_Glue11_exp_exp var14 var13 var12 var11 var10 var9 var8 var7) (and (and (and (and (and (and (and (and (= (AllocResHeap var6 var5) var4) (= (O_TSLL var3) var2)) (= (TSLL var12 var11) var3)) (= (read var6 var8) var1)) (not (valid var6 var8))) (= nullAddr var14)) (= (getTSLL var7) var0)) (= (|TSLL::next| var0) var14)) (= (alloc var9 var2) var4)))) (_Glue13 var13 var10 var8 var5 var6 var1))))
(assert (forall ((var0 HeapObject) (var1 TSLL) (var2 Int) (var3 TSLL) (var4 HeapObject) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr)) (or (not (and (_Glue13 var9 var8 var7 var6 var5 var4) (and (and (and (and (= (getTSLL var4) var3) (= (|TSLL::data| var3) var2)) (= (TSLL var6 var2) var1)) (= (O_TSLL var1) var0)) (valid var5 var7)))) (Inv_Heap var7 var0))))
(assert (forall ((var0 HeapObject) (var1 TSLL) (var2 Int) (var3 TSLL) (var4 Heap) (var5 HeapObject) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Addr) (var10 HeapObject) (var11 Addr)) (or (not (and (and (Inv_Heap var11 var10) (_Glue13 var9 var8 var11 var7 var6 var5)) (and (and (and (and (and (and (and (= (read var4 var11) var10) (valid var4 var11)) true) (= (getTSLL var5) var3)) (= (|TSLL::data| var3) var2)) (= (TSLL var7 var2) var1)) (= (O_TSLL var1) var0)) (= (write var6 var11 var0) var4)))) (_Glue15 var4 var9 var8 var11 var10))))
(assert (forall ((var0 HeapObject) (var1 TSLL) (var2 Int) (var3 TSLL) (var4 HeapObject) (var5 Heap) (var6 HeapObject) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr)) (or (not (and (_Glue13 var11 var10 var9 var8 var7 var6) (and (and (and (and (and (and (= (read var5 var9) var4) (not (valid var5 var9))) (= (getTSLL var6) var3)) (= (|TSLL::data| var3) var2)) (= (TSLL var8 var2) var1)) (= (O_TSLL var1) var0)) (= (write var7 var9 var0) var5)))) (_Glue15 var5 var11 var10 var9 var4))))
(assert (forall ((var0 HeapObject) (var1 TSLL) (var2 Addr) (var3 TSLL) (var4 HeapObject) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (_Glue15 var8 var7 var6 var5 var4) (and (and (and (and (= (getTSLL var4) var3) (= (|TSLL::next| var3) var2)) (= (TSLL var2 1) var1)) (= (O_TSLL var1) var0)) (valid var8 var5)))) (Inv_Heap var5 var0))))
(assert (forall ((var0 HeapObject) (var1 TSLL) (var2 Addr) (var3 TSLL) (var4 Heap) (var5 HeapObject) (var6 Addr) (var7 Addr) (var8 Heap) (var9 HeapObject) (var10 Addr)) (or (not (and (and (Inv_Heap var10 var9) (_Glue15 var8 var7 var6 var10 var5)) (and (and (and (and (and (and (and (= (read var4 var10) var9) (valid var4 var10)) true) (= (getTSLL var5) var3)) (= (|TSLL::next| var3) var2)) (= (TSLL var2 1) var1)) (= (O_TSLL var1) var0)) (= (write var8 var10 var0) var4)))) (_Glue17 var4 var7 var6 var10 var9))))
(assert (forall ((var0 HeapObject) (var1 TSLL) (var2 Addr) (var3 TSLL) (var4 HeapObject) (var5 Heap) (var6 HeapObject) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (_Glue15 var10 var9 var8 var7 var6) (and (and (and (and (and (and (= (read var5 var7) var4) (not (valid var5 var7))) (= (getTSLL var6) var3)) (= (|TSLL::next| var3) var2)) (= (TSLL var2 1) var1)) (= (O_TSLL var1) var0)) (= (write var10 var7 var0) var5)))) (_Glue17 var5 var9 var8 var7 var4))))
(assert (forall ((var0 HeapObject) (var1 TSLL) (var2 Addr) (var3 Int) (var4 TSLL) (var5 HeapObject) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (_Glue17 var8 var7 var7 var6 var5) (and (and (and (and (and (= (getTSLL var5) var4) (= (|TSLL::data| var4) var3)) (= nullAddr var2)) (= (TSLL var2 var3) var1)) (= (O_TSLL var1) var0)) (valid var8 var6)))) (Inv_Heap var6 var0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 HeapObject) (var3 TSLL) (var4 Addr) (var5 Int) (var6 TSLL) (var7 HeapObject) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (_Glue17 var10 var9 var9 var8 var7) (and (and (and (and (and (and (= (getTSLL var7) var6) (= (|TSLL::data| var6) var5)) (= nullAddr var4)) (= (TSLL var4 var5) var3)) (= (O_TSLL var3) var2)) (= (write var10 var8 var2) var1)) (= var0 var9)))) (inv_main_20 var1 var0 var9))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 HeapObject) (var4 Addr)) (not (and (and (Inv_Heap var4 var3) (inv_main_35 var2 var4 var1)) (and (and (and (and (not (= var4 var0)) (= (read var2 var4) var3)) (= defObj var3)) (= nullAddr var0)) (valid var2 var4))))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main_35 var4 var3 var2) (and (and (and (and (not (= var3 var1)) (= (read var4 var3) var0)) (= defObj var0)) (= nullAddr var1)) (not (valid var4 var3)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 TSLL) (var3 Addr) (var4 Addr) (var5 Heap) (var6 HeapObject) (var7 Addr)) (or (not (and (and (Inv_Heap var7 var6) (inv_main_23 var5 var4 var7)) (and (and (and (and (and (and (and (= nullAddr var3) (= (read var5 var7) var6)) (= (getTSLL var6) var2)) (= (|TSLL::data| var2) var1)) (= (|TSLL::next| var2) var0)) (not (= var7 var3))) (not (= var1 1))) (valid var5 var7)))) (inv_main_23 var5 var4 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 TSLL) (var3 HeapObject) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main_23 var7 var6 var5) (and (and (and (and (and (and (and (= nullAddr var4) (= (read var7 var5) var3)) (= (getTSLL var3) var2)) (= (|TSLL::data| var2) var1)) (= (|TSLL::next| var2) var0)) (not (= var5 var4))) (not (= var1 1))) (not (valid var7 var5))))) (inv_main_23 var7 var6 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main1003_2 var3 var2 var1) (= var0 var2))) (inv_main_12 var3 var0 var2))))
(check-sat)
