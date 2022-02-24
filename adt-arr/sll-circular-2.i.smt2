(set-info :source |
    Benchmark: C_VC
    Output by Princess (http://www.philipp.ruemmer.org/princess.shtml)
|)
(set-info :status unsat)
;===============================================================================
; Encoding of Heap sorts and operations
;-------------------------------------------------------------------------------
(define-sort Addr() Int)
(declare-datatypes ((HeapObject 0) (TSLL 0))
                   (((O_Int (getInt Int)) (O_Addr (getAddr Addr)) (O_TSLL (getTSLL TSLL)) (defObj))
                   ((TSLL (next Addr) (data Int)))))
(declare-datatypes ((AllocResHeap 0) (Heap 0))
                   (((AllocResHeap   (newHeap Heap) (newAddr Addr)))
                    ((HeapCtor (HeapSize Int)
                               (HeapContents (Array Addr HeapObject))))))
(define-fun nullAddr  () Addr 0)
(define-fun defHeapObject    () HeapObject defObj)
(define-fun valid     ((h Heap) (p Addr)) Bool
  (and (>= (HeapSize h) p) (> p 0)))
(declare-const allDefHeapObject (Array Addr HeapObject))
(define-fun emptyHeap () Heap (HeapCtor 0 allDefHeapObject))
(define-fun read ((h Heap) (p Addr)) HeapObject
  (ite (valid h p)
       (select (HeapContents h) p)
       defHeapObject))
(define-fun write ((h Heap) (p Addr) (o HeapObject)) Heap
  (ite (valid h p)
       (HeapCtor (HeapSize h) (store (HeapContents h) p o))
       h))
(define-fun alloc   ((h Heap) (o HeapObject)) AllocResHeap
  (AllocResHeap (HeapCtor (+ 1 (HeapSize h))
                    (store (HeapContents h) (+ 1 (HeapSize h)) o))
          (+ 1 (HeapSize h))))
(define-fun Heap-eq     ((h1 Heap) (h2 Heap)) Bool
  (forall ((p Addr))
          (and (= (valid h1 p) (valid h2 p))
               (= (read h1 p) (read h2 p)))))
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
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Int) (var8 Addr)) (or (not (and (inv_main50 var3 var1 var8 var7) (and (not (= var2 0)) (and (and (and (and (= var6 var3) (= var4 var1)) (= var5 var8)) (= var0 var7)) (= var2 (data (getTSLL (read var3 var8)))))))) (inv_main55 var6 var5 var5 var0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Addr)) (or (not (inv_main8 var1 var0 var3 var2)) (inv_main29 (write var1 var3 (O_TSLL (TSLL (next (getTSLL (read var1 var3))) var2))) var0 var3 var2))))
(assert (forall ((var0 Addr) (var1 Heap)) (or (not (inv_main3 var1 var0)) (inv_main4 (write var1 var0 (O_TSLL (TSLL var0 (data (getTSLL (read var1 var0)))))) var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Int) (var6 Int) (var7 Heap) (var8 Addr)) (or (not (and (inv_main13 var3 var1 var8 var6) (and (= var5 0) (and (and (and (= var7 (write var3 var8 (O_TSLL (TSLL var1 (data (getTSLL (read var3 var8))))))) (= var4 var1)) (= var2 var8)) (= var0 var6))))) (inv_main16 var7 var4 var2 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Int) (var6 Heap) (var7 Addr) (var8 Int)) (or (not (and (inv_main13 var3 var1 var7 var5) (and (= var0 1) (and (not (= var8 0)) (and (and (and (= var6 (write var3 var7 (O_TSLL (TSLL var1 (data (getTSLL (read var3 var7))))))) (= var4 var1)) (= var2 var7)) (= var0 var5)))))) (inv_main16 var6 var4 var2 2))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Int) (var6 Heap) (var7 Addr) (var8 Int)) (or (not (and (inv_main13 var3 var1 var7 var5) (and (= var0 2) (and (not (= var0 1)) (and (not (= var8 0)) (and (and (and (= var6 (write var3 var7 (O_TSLL (TSLL var1 (data (getTSLL (read var3 var7))))))) (= var4 var1)) (= var2 var7)) (= var0 var5))))))) (inv_main16 var6 var4 var2 3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Int) (var7 Addr) (var8 Int)) (or (not (and (inv_main29 var4 var1 var7 var6) (and (= nullAddr var5) (and (and (and (and (= var2 var4) (= var3 var1)) (= var0 var7)) (= var8 var6)) (= var5 (next (getTSLL (read var4 var1)))))))) (inv_main34 var2 var3 var5 var8))))
(assert (forall ((var0 Heap) (var1 TSLL)) (or (not (inv_main2 var0)) (inv_main3 (newHeap (alloc var0 (O_TSLL var1))) (newAddr (alloc var0 (O_TSLL var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Int) (var4 Addr)) (or (not (inv_main12 var2 var0 var4 var3 var1)) (inv_main11 (write var2 var4 (O_TSLL (TSLL var1 (data (getTSLL (read var2 var4)))))) var0 var4 var3))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Heap) (var4 Int) (var5 Int) (var6 Addr) (var7 Int) (var8 Int) (var9 Addr)) (or (not (and (inv_main45 var3 var0 var6 var4 var8) (and (not (= var5 0)) (and (and (and (and (= var1 var3) (= var9 var0)) (= var2 var6)) (= var7 var4)) (or (and (<= 0 (+ (+ var8 (* (- 1) (data (getTSLL (read var3 (next (getTSLL (read var3 var6)))))))) (- 1))) (= var5 1)) (and (not (<= 0 (+ (+ var8 (* (- 1) (data (getTSLL (read var3 (next (getTSLL (read var3 var6)))))))) (- 1)))) (= var5 0))))))) (inv_main40 var1 var9 var2 var7))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Heap) (var3 Int) (var4 Addr)) (or (not (and (inv_main44 var2 var0 var4 var3 var1) (not (= var1 0)))) (inv_main45 var2 var0 var4 var3 (data (getTSLL (read var2 var4)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Heap) (var3 Addr) (var4 Int) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main16 var2 var0 var5 var4) (and (= nullAddr var3) (and (and (and (= var7 (write var2 var5 (O_TSLL (TSLL (next (getTSLL (read var2 var5))) var4)))) (= var6 var0)) (= var3 var5)) (= var1 var4))))) (inv_main26 var7 var6 var3 var1))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Heap) (var3 Int) (var4 Addr)) (or (not (and (inv_main44 var2 var0 var4 var3 var1) (= var1 0))) (inv_main42 var2 var0 var4 var3))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Heap) (var4 Int) (var5 Int) (var6 Addr) (var7 Int) (var8 Int) (var9 Addr)) (or (not (and (inv_main45 var3 var0 var6 var4 var8) (and (= var5 0) (and (and (and (and (= var1 var3) (= var9 var0)) (= var2 var6)) (= var7 var4)) (or (and (<= 0 (+ (+ var8 (* (- 1) (data (getTSLL (read var3 (next (getTSLL (read var3 var6)))))))) (- 1))) (= var5 1)) (and (not (<= 0 (+ (+ var8 (* (- 1) (data (getTSLL (read var3 (next (getTSLL (read var3 var6)))))))) (- 1)))) (= var5 0))))))) (inv_main42 var1 var9 var2 var7))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Int) (var4 Heap) (var5 Int) (var6 Addr) (var7 Addr) (var8 Addr)) (or (not (and (inv_main32 var4 var1 var7 var5) (and (not (= var0 0)) (and (and (and (and (= var2 var4) (= var6 var1)) (= var8 var7)) (= var3 var5)) (= var0 (data (getTSLL (read var4 var7)))))))) (inv_main38 var2 var6 var8 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Heap) (var5 TSLL) (var6 Int) (var7 Int) (var8 Addr) (var9 Int)) (or (not (and (inv_main16 var3 var1 var8 var7) (and (not (= var9 0)) (and (not (= nullAddr var2)) (and (and (and (= var4 (write var3 var8 (O_TSLL (TSLL (next (getTSLL (read var3 var8))) var7)))) (= var0 var1)) (= var2 var8)) (= var6 var7)))))) (inv_main12 (newHeap (alloc var4 (O_TSLL var5))) var0 var2 var6 (newAddr (alloc var4 (O_TSLL var5)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Heap) (var3 TSLL) (var4 Heap) (var5 Addr)) (or (not (and (inv_main4 var2 var0) (and (not (= var1 0)) (and (= var4 (write var2 var0 (O_TSLL (TSLL (next (getTSLL (read var2 var0))) 0)))) (= var5 var0))))) (inv_main12 (newHeap (alloc var4 (O_TSLL var3))) var5 var5 1 (newAddr (alloc var4 (O_TSLL var3)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Int) (var6 Heap) (var7 Addr) (var8 Int)) (or (not (and (inv_main37 var3 var1 var7 var5) (and (and (and (and (= var6 var3) (= var2 var1)) (= var0 var7)) (= var8 var5)) (= var4 (next (getTSLL (read var3 var1))))))) (inv_main50 var6 var2 var4 var8))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Heap) (var6 Int) (var7 Addr) (var8 Int)) (or (not (and (inv_main55 var5 var2 var7 var6) (and (and (and (and (= var4 var5) (= var1 var2)) (= var0 var7)) (= var8 var6)) (= var3 (next (getTSLL (read var5 var7))))))) (inv_main50 (write var4 var1 defObj) var1 var3 var8))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Addr)) (or (not (inv_main38 var1 var0 var3 var2)) (inv_main44 var1 var0 var3 var2 (data (getTSLL (read var1 (next (getTSLL (read var1 var3))))))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Int) (var6 Heap) (var7 Addr) (var8 Int)) (or (not (and (inv_main13 var3 var1 var7 var5) (and (not (= var0 2)) (and (not (= var0 1)) (and (not (= var8 0)) (and (and (and (= var6 (write var3 var7 (O_TSLL (TSLL var1 (data (getTSLL (read var3 var7))))))) (= var4 var1)) (= var2 var7)) (= var0 var5))))))) (inv_main8 var6 var4 var2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Heap) (var5 Int) (var6 Int) (var7 Addr) (var8 Int)) (or (not (and (inv_main16 var3 var1 var7 var6) (and (= var8 0) (and (not (= nullAddr var2)) (and (and (and (= var4 (write var3 var7 (O_TSLL (TSLL (next (getTSLL (read var3 var7))) var6)))) (= var0 var1)) (= var2 var7)) (= var5 var6)))))) (inv_main8 var4 var0 var2 var5))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Heap) (var3 Addr) (var4 Int)) (or (not (and (inv_main4 var2 var0) (and (= var4 0) (and (= var1 (write var2 var0 (O_TSLL (TSLL (next (getTSLL (read var2 var0))) 0)))) (= var3 var0))))) (inv_main8 var1 var3 var3 1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap) (var5 Heap) (var6 Int) (var7 Int) (var8 Addr)) (or (not (and (inv_main32 var5 var1 var8 var7) (and (= var6 0) (and (and (and (and (= var4 var5) (= var2 var1)) (= var0 var8)) (= var3 var7)) (= var6 (data (getTSLL (read var5 var8)))))))) (inv_main37 var4 var2 var0 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap) (var5 Heap) (var6 Int) (var7 Addr) (var8 Addr)) (or (not (and (inv_main40 var4 var1 var8 var6) (and (and (and (and (= var5 var4) (= var0 var1)) (= var7 var8)) (= var3 var6)) (= var2 (next (getTSLL (read var4 var8))))))) (inv_main32 var5 var0 var2 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Int) (var7 Addr) (var8 Int)) (or (not (and (inv_main29 var4 var1 var7 var6) (and (not (= nullAddr var5)) (and (and (and (and (= var2 var4) (= var3 var1)) (= var0 var7)) (= var8 var6)) (= var5 (next (getTSLL (read var4 var1)))))))) (inv_main32 var2 var3 var5 var8))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Addr) (var5 Heap) (var6 Int) (var7 Addr) (var8 Heap)) (or (not (and (inv_main11 var5 var1 var7 var6) (and (and (and (and (= var8 var5) (= var0 var1)) (= var4 var7)) (= var3 var6)) (= var2 (next (getTSLL (read var5 var7))))))) (inv_main13 var8 var0 var2 var3))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main3 var1 var0) (not (is-O_TSLL (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main4 var1 var0) (not (is-O_TSLL (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Int) (var4 Addr)) (not (and (inv_main12 var2 var0 var4 var3 var1) (not (is-O_TSLL (read var2 var4)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Addr)) (not (and (inv_main11 var1 var0 var3 var2) (not (is-O_TSLL (read var1 var3)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Addr)) (not (and (inv_main13 var1 var0 var3 var2) (not (is-O_TSLL (read var1 var3)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Addr)) (not (and (inv_main16 var1 var0 var3 var2) (not (is-O_TSLL (read var1 var3)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Addr)) (not (inv_main26 var1 var0 var3 var2))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Addr)) (not (and (inv_main8 var1 var0 var3 var2) (not (is-O_TSLL (read var1 var3)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Addr)) (not (and (inv_main29 var1 var0 var3 var2) (not (is-O_TSLL (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Addr)) (not (inv_main34 var1 var0 var3 var2))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Addr)) (not (and (inv_main32 var1 var0 var3 var2) (not (is-O_TSLL (read var1 var3)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Addr)) (not (and (inv_main38 var1 var0 var3 var2) (not (is-O_TSLL (read var1 var3)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Addr)) (not (and (inv_main38 var1 var0 var3 var2) (not (is-O_TSLL (read var1 (next (getTSLL (read var1 var3))))))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Heap) (var3 Int) (var4 Addr)) (not (and (inv_main44 var2 var0 var4 var3 var1) (and (not (= var1 0)) (not (is-O_TSLL (read var2 var4))))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Addr) (var4 Int)) (not (and (inv_main45 var1 var0 var3 var2 var4) (not (is-O_TSLL (read var1 var3)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Addr) (var4 Int)) (not (and (inv_main45 var1 var0 var3 var2 var4) (not (is-O_TSLL (read var1 (next (getTSLL (read var1 var3))))))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Addr)) (not (inv_main42 var1 var0 var3 var2))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Addr)) (not (and (inv_main40 var1 var0 var3 var2) (not (is-O_TSLL (read var1 var3)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Addr)) (not (and (inv_main37 var1 var0 var3 var2) (not (is-O_TSLL (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Addr)) (not (and (inv_main50 var1 var0 var3 var2) (not (is-O_TSLL (read var1 var3)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Addr)) (not (and (inv_main55 var1 var0 var3 var2) (not (is-O_TSLL (read var1 var3)))))))
(check-sat)
