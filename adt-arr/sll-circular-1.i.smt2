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
(declare-datatypes ((HeapObject 0) (TSLL 0))
                   (((O_Int (getInt Int)) (O_UInt (getUInt Int)) (O_Addr (getAddr Addr)) (O_TSLL (getTSLL TSLL)) (defObj))
                   ((TSLL (next Addr) (data Int)))))
(declare-datatypes ((AllocResHeap 0) (Heap 0))
                   (((AllocResHeap   (newHeap Heap) (newAddr Addr)))
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
(declare-fun inv_main11 (Heap Addr Addr Int) Bool)
(declare-fun inv_main12 (Heap Addr Addr Int Addr) Bool)
(declare-fun inv_main13 (Heap Addr Addr Int) Bool)
(declare-fun inv_main16 (Heap Addr Addr Int) Bool)
(declare-fun inv_main2 (Heap) Bool)
(declare-fun inv_main26 (Heap Addr Addr Int) Bool)
(declare-fun inv_main29 (Heap Addr Addr Int) Bool)
(declare-fun inv_main3 (Heap Addr) Bool)
(declare-fun inv_main32 (Heap Addr Addr Int) Bool)
(declare-fun inv_main34 (Heap Addr Addr Int) Bool)
(declare-fun inv_main37 (Heap Addr Addr Int) Bool)
(declare-fun inv_main38 (Heap Addr Addr Int) Bool)
(declare-fun inv_main4 (Heap Addr) Bool)
(declare-fun inv_main40 (Heap Addr Addr Int) Bool)
(declare-fun inv_main42 (Heap Addr Addr Int) Bool)
(declare-fun inv_main44 (Heap Addr Addr Int Int) Bool)
(declare-fun inv_main45 (Heap Addr Addr Int Int) Bool)
(declare-fun inv_main50 (Heap Addr Addr Int) Bool)
(declare-fun inv_main55 (Heap Addr Addr Int) Bool)
(declare-fun inv_main8 (Heap Addr Addr Int) Bool)
(assert (inv_main2 emptyHeap))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Int) (var4 Int) (var5 Int) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main13 var8 var7 var6 var5) (and (not (= var4 2)) (and (not (= var4 1)) (and (not (= var3 0)) (and (is-O_TSLL (read var8 var6)) (and (and (and (= var2 (write var8 var6 (O_TSLL (TSLL var7 (data (getTSLL (read var8 var6))))))) (= var1 var7)) (= var0 var6)) (= var4 var5)))))))) (inv_main8 var2 var1 var0 var4))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Int) (var5 Int) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main16 var8 var7 var6 var5) (and (= var4 0) (and (and (not (= nullAddr var3)) (is-O_TSLL (read var8 var6))) (and (and (and (= var2 (write var8 var6 (O_TSLL (TSLL (next (getTSLL (read var8 var6))) var5)))) (= var1 var7)) (= var3 var6)) (= var0 var5)))))) (inv_main8 var2 var1 var3 var0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Addr) (var4 Heap)) (or (not (and (inv_main4 var4 var3) (and (and (= var2 0) (is-O_TSLL (read var4 var3))) (and (= var1 (write var4 var3 (O_TSLL (TSLL (next (getTSLL (read var4 var3))) 0)))) (= var0 var3))))) (inv_main8 var1 var0 var0 1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main8 var3 var2 var1 var0) (is-O_TSLL (read var3 var1)))) (inv_main29 (write var3 var1 (O_TSLL (TSLL (next (getTSLL (read var3 var1))) var0))) var2 var1 var0))))
(assert (forall ((var0 TSLL) (var1 Heap)) (or (not (inv_main2 var1)) (inv_main3 (newHeap (alloc var1 (O_TSLL var0))) (newAddr (alloc var1 (O_TSLL var0)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Int) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main37 var8 var7 var6 var5) (and (is-O_TSLL (read var8 var7)) (and (and (and (and (= var4 var8) (= var3 var7)) (= var2 var6)) (= var1 var5)) (= var0 (next (getTSLL (read var8 var7)))))))) (inv_main50 var4 var3 var0 var1))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Int) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main55 var8 var7 var6 var5) (and (is-O_TSLL (read var8 var6)) (and (and (and (and (= var4 var8) (= var3 var7)) (= var2 var6)) (= var1 var5)) (= var0 (next (getTSLL (read var8 var6)))))))) (inv_main50 (write var4 var3 defObj) var3 var0 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Int) (var6 Int) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main45 var9 var8 var7 var6 var5) (and (= var4 0) (and (and (is-O_TSLL (read var9 var7)) (is-O_TSLL (read var9 (next (getTSLL (read var9 var7)))))) (and (and (and (and (= var3 var9) (= var2 var8)) (= var1 var7)) (= var0 var6)) (or (and (<= 0 (+ (data (getTSLL (read var9 (next (getTSLL (read var9 var7)))))) (* (- 1) var5))) (= var4 1)) (and (not (<= 0 (+ (data (getTSLL (read var9 (next (getTSLL (read var9 var7)))))) (* (- 1) var5)))) (= var4 0)))))))) (inv_main42 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Int) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main29 var8 var7 var6 var5) (and (= nullAddr var4) (and (is-O_TSLL (read var8 var7)) (and (and (and (and (= var3 var8) (= var2 var7)) (= var1 var6)) (= var0 var5)) (= var4 (next (getTSLL (read var8 var7))))))))) (inv_main34 var3 var2 var4 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Int) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main32 var8 var7 var6 var5) (and (and (not (= var4 0)) (is-O_TSLL (read var8 var6))) (and (and (and (and (= var3 var8) (= var2 var7)) (= var1 var6)) (= var0 var5)) (= var4 (data (getTSLL (read var8 var6)))))))) (inv_main38 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Int) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main16 var7 var6 var5 var4) (and (and (= nullAddr var3) (is-O_TSLL (read var7 var5))) (and (and (and (= var2 (write var7 var5 (O_TSLL (TSLL (next (getTSLL (read var7 var5))) var4)))) (= var1 var6)) (= var3 var5)) (= var0 var4))))) (inv_main26 var2 var1 var3 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Int) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main11 var8 var7 var6 var5) (and (is-O_TSLL (read var8 var6)) (and (and (and (and (= var4 var8) (= var3 var7)) (= var2 var6)) (= var1 var5)) (= var0 (next (getTSLL (read var8 var6)))))))) (inv_main13 var4 var3 var0 var1))))
(assert (forall ((var0 TSLL) (var1 Int) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Int) (var6 Int) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main16 var9 var8 var7 var6) (and (not (= var5 0)) (and (and (not (= nullAddr var4)) (is-O_TSLL (read var9 var7))) (and (and (and (= var3 (write var9 var7 (O_TSLL (TSLL (next (getTSLL (read var9 var7))) var6)))) (= var2 var8)) (= var4 var7)) (= var1 var6)))))) (inv_main12 (newHeap (alloc var3 (O_TSLL var0))) var2 var4 var1 (newAddr (alloc var3 (O_TSLL var0)))))))
(assert (forall ((var0 TSLL) (var1 Addr) (var2 Heap) (var3 Int) (var4 Addr) (var5 Heap)) (or (not (and (inv_main4 var5 var4) (and (and (not (= var3 0)) (is-O_TSLL (read var5 var4))) (and (= var2 (write var5 var4 (O_TSLL (TSLL (next (getTSLL (read var5 var4))) 0)))) (= var1 var4))))) (inv_main12 (newHeap (alloc var2 (O_TSLL var0))) var1 var1 1 (newAddr (alloc var2 (O_TSLL var0)))))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main44 var4 var3 var2 var1 var0) (and (not (= var0 0)) (is-O_TSLL (read var4 var2))))) (inv_main45 var4 var3 var2 var1 (data (getTSLL (read var4 var2)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Int) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main32 var8 var7 var6 var5) (and (and (= var4 0) (is-O_TSLL (read var8 var6))) (and (and (and (and (= var3 var8) (= var2 var7)) (= var1 var6)) (= var0 var5)) (= var4 (data (getTSLL (read var8 var6)))))))) (inv_main37 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main38 var3 var2 var1 var0) (and (is-O_TSLL (read var3 var1)) (is-O_TSLL (read var3 (next (getTSLL (read var3 var1)))))))) (inv_main44 var3 var2 var1 var0 (data (getTSLL (read var3 (next (getTSLL (read var3 var1))))))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Int) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main13 var8 var7 var6 var5) (and (= var4 0) (and (is-O_TSLL (read var8 var6)) (and (and (and (= var3 (write var8 var6 (O_TSLL (TSLL var7 (data (getTSLL (read var8 var6))))))) (= var2 var7)) (= var1 var6)) (= var0 var5)))))) (inv_main16 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Int) (var4 Int) (var5 Int) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main13 var8 var7 var6 var5) (and (= var4 1) (and (not (= var3 0)) (and (is-O_TSLL (read var8 var6)) (and (and (and (= var2 (write var8 var6 (O_TSLL (TSLL var7 (data (getTSLL (read var8 var6))))))) (= var1 var7)) (= var0 var6)) (= var4 var5))))))) (inv_main16 var2 var1 var0 2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Int) (var4 Int) (var5 Int) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main13 var8 var7 var6 var5) (and (= var4 2) (and (not (= var4 1)) (and (not (= var3 0)) (and (is-O_TSLL (read var8 var6)) (and (and (and (= var2 (write var8 var6 (O_TSLL (TSLL var7 (data (getTSLL (read var8 var6))))))) (= var1 var7)) (= var0 var6)) (= var4 var5)))))))) (inv_main16 var2 var1 var0 3))))
(assert (forall ((var0 Addr) (var1 Heap)) (or (not (and (inv_main3 var1 var0) (is-O_TSLL (read var1 var0)))) (inv_main4 (write var1 var0 (O_TSLL (TSLL var0 (data (getTSLL (read var1 var0)))))) var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Int) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main50 var8 var7 var6 var5) (and (and (not (= var4 0)) (is-O_TSLL (read var8 var6))) (and (and (and (and (= var3 var8) (= var2 var7)) (= var1 var6)) (= var0 var5)) (= var4 (data (getTSLL (read var8 var6)))))))) (inv_main55 var3 var1 var1 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Int) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main40 var8 var7 var6 var5) (and (is-O_TSLL (read var8 var6)) (and (and (and (and (= var4 var8) (= var3 var7)) (= var2 var6)) (= var1 var5)) (= var0 (next (getTSLL (read var8 var6)))))))) (inv_main32 var4 var3 var0 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Int) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main29 var8 var7 var6 var5) (and (not (= nullAddr var4)) (and (is-O_TSLL (read var8 var7)) (and (and (and (and (= var3 var8) (= var2 var7)) (= var1 var6)) (= var0 var5)) (= var4 (next (getTSLL (read var8 var7))))))))) (inv_main32 var3 var2 var4 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main12 var4 var3 var2 var1 var0) (is-O_TSLL (read var4 var2)))) (inv_main11 (write var4 var2 (O_TSLL (TSLL var0 (data (getTSLL (read var4 var2)))))) var3 var2 var1))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main44 var4 var3 var2 var1 var0) (= var0 0))) (inv_main40 var4 var3 var2 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Int) (var6 Int) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main45 var9 var8 var7 var6 var5) (and (not (= var4 0)) (and (and (is-O_TSLL (read var9 var7)) (is-O_TSLL (read var9 (next (getTSLL (read var9 var7)))))) (and (and (and (and (= var3 var9) (= var2 var8)) (= var1 var7)) (= var0 var6)) (or (and (<= 0 (+ (data (getTSLL (read var9 (next (getTSLL (read var9 var7)))))) (* (- 1) var5))) (= var4 1)) (and (not (<= 0 (+ (data (getTSLL (read var9 (next (getTSLL (read var9 var7)))))) (* (- 1) var5)))) (= var4 0)))))))) (inv_main40 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main3 var1 var0) (not (is-O_TSLL (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main4 var1 var0) (not (is-O_TSLL (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main12 var4 var3 var2 var1 var0) (not (is-O_TSLL (read var4 var2)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main11 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var1)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main13 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var1)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main16 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var1)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (inv_main26 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main8 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var1)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main29 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var2)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (inv_main34 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main32 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var1)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main38 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var1)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main38 var3 var2 var1 var0) (and (is-O_TSLL (read var3 var1)) (not (is-O_TSLL (read var3 (next (getTSLL (read var3 var1)))))))))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main44 var4 var3 var2 var1 var0) (and (not (= var0 0)) (not (is-O_TSLL (read var4 var2))))))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main45 var4 var3 var2 var1 var0) (not (is-O_TSLL (read var4 var2)))))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main45 var4 var3 var2 var1 var0) (and (is-O_TSLL (read var4 var2)) (not (is-O_TSLL (read var4 (next (getTSLL (read var4 var2)))))))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (inv_main42 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main40 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var1)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main37 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var2)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main50 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var1)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main55 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var1)))))))
(check-sat)
