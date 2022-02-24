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
                   ((TSLL (next Addr) (prev Addr) (data Int)))))
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
(declare-fun inv_main11 (Heap Addr Addr) Bool)
(declare-fun inv_main12 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main13 (Heap Addr Addr) Bool)
(declare-fun inv_main14 (Heap Addr Addr) Bool)
(declare-fun inv_main16 (Heap Addr Addr) Bool)
(declare-fun inv_main2 (Heap) Bool)
(declare-fun inv_main21 (Heap Addr Addr) Bool)
(declare-fun inv_main23 (Heap Addr Addr) Bool)
(declare-fun inv_main24 (Heap Addr Addr) Bool)
(declare-fun inv_main26 (Heap Addr Addr) Bool)
(declare-fun inv_main27 (Heap Addr Addr) Bool)
(declare-fun inv_main3 (Heap Addr) Bool)
(declare-fun inv_main30 (Heap Addr Addr) Bool)
(declare-fun inv_main36 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main37 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main38 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main4 (Heap Addr) Bool)
(declare-fun inv_main40 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main42 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main44 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main45 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main46 (Heap Addr Addr) Bool)
(declare-fun inv_main47 (Heap Addr Addr) Bool)
(declare-fun inv_main48 (Heap Addr Addr) Bool)
(declare-fun inv_main5 (Heap Addr) Bool)
(declare-fun inv_main54 (Heap Addr Addr) Bool)
(declare-fun inv_main55 (Heap Addr Addr) Bool)
(declare-fun inv_main60 (Heap Addr Addr) Bool)
(declare-fun inv_main67 (Heap Addr Addr) Bool)
(declare-fun inv_main7 (Heap Addr Addr) Bool)
(assert (inv_main2 emptyHeap))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr)) (or (not (inv_main12 var2 var3 var1 var0)) (inv_main11 (write var2 var1 (O_TSLL (TSLL var0 (prev (getTSLL (read var2 var1))) (data (getTSLL (read var2 var1)))))) var3 var1))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr)) (or (not (inv_main11 var1 var2 var0)) (inv_main13 (write var1 (next (getTSLL (read var1 var0))) (O_TSLL (TSLL (next (getTSLL (read var1 (next (getTSLL (read var1 var0)))))) var0 (data (getTSLL (read var1 (next (getTSLL (read var1 var0))))))))) var2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Addr)) (or (not (and (inv_main36 var2 var5 var1 var3) (and (and (and (and (= var6 var2) (= var7 var5)) (= var0 var1)) (= var8 var3)) (= var4 (next (getTSLL (read var2 var1))))))) (inv_main38 var6 var7 var4 var8))))
(assert (forall ((var0 Heap) (var1 Addr)) (or (not (inv_main3 var0 var1)) (inv_main4 (write var0 var1 (O_TSLL (TSLL nullAddr (prev (getTSLL (read var0 var1))) (data (getTSLL (read var0 var1)))))) var1))))
(assert (forall ((var0 TSLL) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Int)) (or (not (and (inv_main7 var2 var3 var1) (not (= var4 0)))) (inv_main12 (newHeap (alloc var2 (O_TSLL var0))) var3 var1 (newAddr (alloc var2 (O_TSLL var0)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Heap) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr)) (or (not (and (inv_main67 var4 var6 var3) (and (and (not (= var8 nullAddr)) (and (and (and (= var2 var4) (= var5 var6)) (= var7 var3)) (= var9 (next (getTSLL (read var4 var3)))))) (and (and (= var1 (write var2 var5 defObj)) (= var0 var5)) (= var8 var9))))) (inv_main67 var1 var8 var8))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr)) (or (not (and (inv_main47 var2 var4 var1) (and (not (= var5 nullAddr)) (and (= var3 nullAddr) (and (and (and (= var0 var2) (= var5 var4)) (= var6 var1)) (= var3 (next (getTSLL (read var2 var1))))))))) (inv_main67 var0 var5 var5))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr)) (or (not (and (inv_main55 var2 var6 var1) (and (not (= var4 nullAddr)) (and (= var5 nullAddr) (and (and (and (= var3 var2) (= var4 var6)) (= var0 var1)) (= var5 (next (getTSLL (read var2 var1))))))))) (inv_main67 var3 var4 var4))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr)) (or (not (and (inv_main47 var2 var4 var1) (and (not (= var3 nullAddr)) (and (and (and (= var0 var2) (= var5 var4)) (= var6 var1)) (= var3 (next (getTSLL (read var2 var1)))))))) (inv_main54 var0 var5 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr)) (or (not (and (inv_main55 var2 var6 var1) (and (not (= var5 nullAddr)) (and (and (and (= var4 var2) (= var3 var6)) (= var0 var1)) (= var5 (next (getTSLL (read var2 var1)))))))) (inv_main54 var4 var3 var5))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr)) (or (not (inv_main16 var1 var2 var0)) (inv_main7 (write var1 var0 (O_TSLL (TSLL nullAddr (prev (getTSLL (read var1 var0))) (data (getTSLL (read var1 var0)))))) var2 var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Heap) (var3 Addr)) (or (not (and (inv_main5 var2 var3) (and (= var0 (write var2 var3 (O_TSLL (TSLL (next (getTSLL (read var2 var3))) (prev (getTSLL (read var2 var3))) 0)))) (= var1 var3)))) (inv_main7 var0 var1 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Addr)) (or (not (and (inv_main26 var3 var5 var2) (and (= var0 0) (and (not (= var4 nullAddr)) (and (and (and (= var6 var3) (= var7 var5)) (= var1 var2)) (= var4 (next (getTSLL (read var3 var2))))))))) (inv_main30 var6 var7 var1))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr)) (or (not (inv_main14 var1 var2 var0)) (inv_main16 (write var1 var0 (O_TSLL (TSLL (next (getTSLL (read var1 var0))) (prev (getTSLL (read var1 var0))) 0))) var2 var0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Addr)) (or (not (inv_main37 var1 var3 var0 var2 var4)) (inv_main36 (write var1 var0 (O_TSLL (TSLL var4 (prev (getTSLL (read var1 var0))) (data (getTSLL (read var1 var0)))))) var3 var0 var2))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr)) (or (not (inv_main23 var1 var2 var0)) (inv_main24 (write var1 var0 (O_TSLL (TSLL var2 (prev (getTSLL (read var1 var0))) (data (getTSLL (read var1 var0)))))) var2 var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Int) (var6 TSLL) (var7 Addr) (var8 Addr) (var9 Addr)) (or (not (and (inv_main7 var3 var7 var2) (and (and (and (and (= var0 (newHeap (alloc var3 (O_TSLL var6)))) (= var8 var7)) (= var1 var2)) (= var9 (newAddr (alloc var3 (O_TSLL var6))))) (and (not (= var5 0)) (= var4 0))))) (inv_main21 var0 var8 var9))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr)) (or (not (inv_main42 var1 var3 var0 var2)) (inv_main45 var1 var3 var0 var2 (prev (getTSLL (read var1 var2)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Int)) (or (not (and (inv_main54 var3 var4 var2) (and (= var6 1) (and (and (and (= var0 var3) (= var1 var4)) (= var5 var2)) (= var6 (data (getTSLL (read var3 var2)))))))) (inv_main55 var0 var1 var5))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main26 var2 var5 var1) (and (= var3 nullAddr) (and (and (and (= var6 var2) (= var0 var5)) (= var4 var1)) (= var3 (next (getTSLL (read var2 var1)))))))) (inv_main27 var6 var0 var4))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Int)) (or (not (and (inv_main26 var2 var4 var1) (and (not (= var7 0)) (and (not (= var3 nullAddr)) (and (and (and (= var5 var2) (= var6 var4)) (= var0 var1)) (= var3 (next (getTSLL (read var2 var1))))))))) (inv_main27 var5 var6 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main46 var3 var4 var2) (and (= var1 1) (and (and (and (= var6 var3) (= var0 var4)) (= var5 var2)) (= var1 (data (getTSLL (read var3 var2)))))))) (inv_main47 var6 var0 var5))))
(assert (forall ((var0 Heap) (var1 TSLL)) (or (not (inv_main2 var0)) (inv_main3 (newHeap (alloc var0 (O_TSLL var1))) (newAddr (alloc var0 (O_TSLL var1)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr)) (or (not (and (inv_main48 var2 var5 var1) (and (and (and (= var0 var2) (= var6 var5)) (= var3 var1)) (= var4 (next (getTSLL (read var2 var1))))))) (inv_main46 var0 var6 var4))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr)) (or (not (and (inv_main44 var1 var4 var0 var3) (and (and (= var2 (write var1 var3 (O_TSLL (TSLL (next (getTSLL (read var1 var3))) var0 (data (getTSLL (read var1 var3))))))) (= var6 var4)) (= var5 var0)))) (inv_main46 var2 var6 var6))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr)) (or (not (and (inv_main40 var3 var6 var2 var5) (and (= var7 nullAddr) (and (and (and (= var0 (write var3 var2 (O_TSLL (TSLL var5 (prev (getTSLL (read var3 var2))) (data (getTSLL (read var3 var2))))))) (= var1 var6)) (= var4 var2)) (= var7 var5))))) (inv_main46 var0 var1 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main24 var2 var4 var1) (and (and (= var5 (write var2 var1 (O_TSLL (TSLL (next (getTSLL (read var2 var1))) nullAddr (data (getTSLL (read var2 var1))))))) (= var0 var4)) (= var3 var1)))) (inv_main46 var5 var3 var3))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Addr)) (or (not (inv_main45 var1 var4 var0 var3 var2)) (inv_main44 (write var1 var0 (O_TSLL (TSLL (next (getTSLL (read var1 var0))) var2 (data (getTSLL (read var1 var0)))))) var4 var0 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Int) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main54 var2 var5 var1) (and (not (= var3 1)) (and (and (and (= var6 var2) (= var4 var5)) (= var0 var1)) (= var3 (data (getTSLL (read var2 var1)))))))) (inv_main60 var6 var4 var0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr)) (or (not (and (inv_main40 var4 var6 var3 var5) (and (not (= var0 nullAddr)) (and (and (and (= var1 (write var4 var3 (O_TSLL (TSLL var5 (prev (getTSLL (read var4 var3))) (data (getTSLL (read var4 var3))))))) (= var2 var6)) (= var7 var3)) (= var0 var5))))) (inv_main42 var1 var2 var7 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main13 var2 var3 var1) (and (and (and (= var6 var2) (= var0 var3)) (= var4 var1)) (= var5 (next (getTSLL (read var2 var1))))))) (inv_main14 var6 var0 var5))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr)) (or (not (inv_main21 var1 var2 var0)) (inv_main23 (write var1 var0 (O_TSLL (TSLL (next (getTSLL (read var1 var0))) (prev (getTSLL (read var1 var0))) 1))) var2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Heap) (var6 Addr)) (or (not (and (inv_main30 var4 var6 var3) (and (and (and (= var5 var4) (= var0 var6)) (= var2 var3)) (= var1 (next (getTSLL (read var4 var3))))))) (inv_main26 var5 var0 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Int) (var4 Addr)) (or (not (and (inv_main7 var2 var4 var1) (and (= var0 0) (= var3 0)))) (inv_main26 var2 var4 var4))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 TSLL) (var6 Heap) (var7 Addr)) (or (not (and (inv_main27 var2 var4 var1) (and (and (and (= var6 var2) (= var7 var4)) (= var3 var1)) (= var0 (next (getTSLL (read var2 var1))))))) (inv_main37 (newHeap (alloc var6 (O_TSLL var5))) var7 var3 var0 (newAddr (alloc var6 (O_TSLL var5)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Int) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr)) (or (not (and (inv_main46 var4 var5 var3) (and (not (= var2 1)) (and (and (and (= var0 var4) (= var1 var5)) (= var6 var3)) (= var2 (data (getTSLL (read var4 var3)))))))) (inv_main48 var0 var1 var6))))
(assert (forall ((var0 Heap) (var1 Addr)) (or (not (inv_main4 var0 var1)) (inv_main5 (write var0 var1 (O_TSLL (TSLL (next (getTSLL (read var0 var1))) nullAddr (data (getTSLL (read var0 var1)))))) var1))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr)) (or (not (inv_main38 var1 var3 var0 var2)) (inv_main40 (write var1 var0 (O_TSLL (TSLL (next (getTSLL (read var1 var0))) (prev (getTSLL (read var1 var0))) 1))) var3 var0 var2))))
(assert (forall ((var0 Heap) (var1 Addr)) (not (and (inv_main3 var0 var1) (not (is-O_TSLL (read var0 var1)))))))
(assert (forall ((var0 Heap) (var1 Addr)) (not (and (inv_main4 var0 var1) (not (is-O_TSLL (read var0 var1)))))))
(assert (forall ((var0 Heap) (var1 Addr)) (not (and (inv_main5 var0 var1) (not (is-O_TSLL (read var0 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr)) (not (and (inv_main12 var2 var3 var1 var0) (not (is-O_TSLL (read var2 var1)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr)) (not (and (inv_main11 var1 var2 var0) (not (is-O_TSLL (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr)) (not (and (inv_main11 var1 var2 var0) (not (is-O_TSLL (read var1 (next (getTSLL (read var1 var0))))))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr)) (not (and (inv_main13 var1 var2 var0) (not (is-O_TSLL (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr)) (not (and (inv_main14 var1 var2 var0) (not (is-O_TSLL (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr)) (not (and (inv_main16 var1 var2 var0) (not (is-O_TSLL (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr)) (not (and (inv_main21 var1 var2 var0) (not (is-O_TSLL (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr)) (not (and (inv_main23 var1 var2 var0) (not (is-O_TSLL (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr)) (not (and (inv_main24 var1 var2 var0) (not (is-O_TSLL (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr)) (not (and (inv_main26 var1 var2 var0) (not (is-O_TSLL (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr)) (not (and (inv_main30 var1 var2 var0) (not (is-O_TSLL (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr)) (not (and (inv_main27 var1 var2 var0) (not (is-O_TSLL (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Addr)) (not (and (inv_main37 var1 var3 var0 var2 var4) (not (is-O_TSLL (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr)) (not (and (inv_main36 var1 var3 var0 var2) (not (is-O_TSLL (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr)) (not (and (inv_main38 var1 var3 var0 var2) (not (is-O_TSLL (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr)) (not (and (inv_main40 var1 var3 var0 var2) (not (is-O_TSLL (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr)) (not (and (inv_main42 var1 var3 var0 var2) (not (is-O_TSLL (read var1 var2)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Addr)) (not (and (inv_main45 var1 var4 var0 var3 var2) (not (is-O_TSLL (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr)) (not (and (inv_main44 var1 var3 var0 var2) (not (is-O_TSLL (read var1 var2)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr)) (not (and (inv_main46 var1 var2 var0) (not (is-O_TSLL (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr)) (not (and (inv_main48 var1 var2 var0) (not (is-O_TSLL (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr)) (not (and (inv_main47 var1 var2 var0) (not (is-O_TSLL (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr)) (not (and (inv_main54 var1 var2 var0) (not (is-O_TSLL (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr)) (not (inv_main60 var1 var2 var0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr)) (not (and (inv_main55 var1 var2 var0) (not (is-O_TSLL (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr)) (not (and (inv_main67 var1 var2 var0) (not (is-O_TSLL (read var1 var0)))))))
(check-sat)
