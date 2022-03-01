(set-logic HORN)
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
(declare-fun inv_main10 (Heap Addr Addr) Bool)
(declare-fun inv_main11 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main12 (Heap Addr Addr) Bool)
(declare-fun inv_main14 (Heap Addr Addr) Bool)
(declare-fun inv_main19 (Heap Addr Addr) Bool)
(declare-fun inv_main2 (Heap) Bool)
(declare-fun inv_main21 (Heap Addr Addr) Bool)
(declare-fun inv_main23 (Heap Addr Addr) Bool)
(declare-fun inv_main24 (Heap Addr Addr) Bool)
(declare-fun inv_main26 (Heap Addr Addr) Bool)
(declare-fun inv_main3 (Heap Addr) Bool)
(declare-fun inv_main32 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main33 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main34 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main35 (Heap Addr Addr) Bool)
(declare-fun inv_main36 (Heap Addr Addr) Bool)
(declare-fun inv_main37 (Heap Addr Addr) Bool)
(declare-fun inv_main4 (Heap Addr) Bool)
(declare-fun inv_main43 (Heap Addr Addr) Bool)
(declare-fun inv_main44 (Heap Addr Addr) Bool)
(declare-fun inv_main49 (Heap Addr Addr) Bool)
(declare-fun inv_main56 (Heap Addr Addr) Bool)
(declare-fun inv_main6 (Heap Addr Addr) Bool)
(assert (inv_main2 emptyHeap))
(assert (forall ((var0 TSLL) (var1 Heap)) (or (not (inv_main2 var1)) (inv_main3 (newHeap (alloc var1 (O_TSLL var0))) (newAddr (alloc var1 (O_TSLL var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Int) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main35 var6 var5 var4) (and (and (= var3 1) (is-O_TSLL (read var6 var4))) (and (and (and (= var2 var6) (= var1 var5)) (= var0 var4)) (= var3 (data (getTSLL (read var6 var4)))))))) (inv_main36 var2 var1 var0))))
(assert (forall ((var0 TSLL) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main24 var7 var6 var5) (and (is-O_TSLL (read var7 var5)) (and (and (and (= var4 var7) (= var3 var6)) (= var2 var5)) (= var1 (next (getTSLL (read var7 var5)))))))) (inv_main33 (newHeap (alloc var4 (O_TSLL var0))) var3 var2 var1 (newAddr (alloc var4 (O_TSLL var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main26 var6 var5 var4) (and (is-O_TSLL (read var6 var4)) (and (and (and (= var3 var6) (= var2 var5)) (= var1 var4)) (= var0 (next (getTSLL (read var6 var4)))))))) (inv_main23 var3 var2 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main6 var4 var3 var2) (and (= var1 0) (= var0 0)))) (inv_main23 var4 var3 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main11 var3 var2 var1 var0) (is-O_TSLL (read var3 var1)))) (inv_main10 (write var3 var1 (O_TSLL (TSLL var0 (data (getTSLL (read var3 var1)))))) var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main32 var3 var2 var1 var0) (and (is-O_TSLL (read var3 var1)) (is-O_TSLL (read var3 (next (getTSLL (read var3 var1)))))))) (inv_main34 (write var3 (next (getTSLL (read var3 var1))) (O_TSLL (TSLL (next (getTSLL (read var3 (next (getTSLL (read var3 var1)))))) 1))) var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Int) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main43 var6 var5 var4) (and (and (= var3 1) (is-O_TSLL (read var6 var4))) (and (and (and (= var2 var6) (= var1 var5)) (= var0 var4)) (= var3 (data (getTSLL (read var6 var4)))))))) (inv_main44 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main56 var9 var8 var7) (and (and (not (= var6 nullAddr)) (and (is-O_TSLL (read var9 var7)) (and (and (and (= var5 var9) (= var4 var8)) (= var3 var7)) (= var2 (next (getTSLL (read var9 var7))))))) (and (and (= var1 (write var5 var4 defObj)) (= var0 var4)) (= var6 var2))))) (inv_main56 var1 var6 var6))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main36 var6 var5 var4) (and (not (= var3 nullAddr)) (and (= var2 nullAddr) (and (is-O_TSLL (read var6 var4)) (and (and (and (= var1 var6) (= var3 var5)) (= var0 var4)) (= var2 (next (getTSLL (read var6 var4)))))))))) (inv_main56 var1 var3 var3))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main44 var6 var5 var4) (and (not (= var3 nullAddr)) (and (= var2 nullAddr) (and (is-O_TSLL (read var6 var4)) (and (and (and (= var1 var6) (= var3 var5)) (= var0 var4)) (= var2 (next (getTSLL (read var6 var4)))))))))) (inv_main56 var1 var3 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (and (inv_main14 var2 var1 var0) (is-O_TSLL (read var2 var0)))) (inv_main6 (write var2 var0 (O_TSLL (TSLL nullAddr (data (getTSLL (read var2 var0)))))) var1 var0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Heap)) (or (not (and (inv_main4 var3 var2) (and (is-O_TSLL (read var3 var2)) (and (= var1 (write var3 var2 (O_TSLL (TSLL (next (getTSLL (read var3 var2))) 0)))) (= var0 var2))))) (inv_main6 var1 var0 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main10 var6 var5 var4) (and (is-O_TSLL (read var6 var4)) (and (and (and (= var3 var6) (= var2 var5)) (= var1 var4)) (= var0 (next (getTSLL (read var6 var4)))))))) (inv_main12 var3 var2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (and (inv_main12 var2 var1 var0) (is-O_TSLL (read var2 var0)))) (inv_main14 (write var2 var0 (O_TSLL (TSLL (next (getTSLL (read var2 var0))) 0))) var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main36 var6 var5 var4) (and (not (= var3 nullAddr)) (and (is-O_TSLL (read var6 var4)) (and (and (and (= var2 var6) (= var1 var5)) (= var0 var4)) (= var3 (next (getTSLL (read var6 var4))))))))) (inv_main43 var2 var1 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main44 var6 var5 var4) (and (not (= var3 nullAddr)) (and (is-O_TSLL (read var6 var4)) (and (and (and (= var2 var6) (= var1 var5)) (= var0 var4)) (= var3 (next (getTSLL (read var6 var4))))))))) (inv_main43 var2 var1 var3))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main23 var3 var2 var1) (and (= var0 0) (and (is-O_TSLL (read var3 var1)) (not (= (next (getTSLL (read var3 var1))) nullAddr)))))) (inv_main26 var3 var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Int) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main43 var6 var5 var4) (and (and (not (= var3 1)) (is-O_TSLL (read var6 var4))) (and (and (and (= var2 var6) (= var1 var5)) (= var0 var4)) (= var3 (data (getTSLL (read var6 var4)))))))) (inv_main49 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 TSLL) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main6 var9 var8 var7) (and (and (and (and (= var6 (newHeap (alloc var9 (O_TSLL var5)))) (= var4 var8)) (= var3 var7)) (= var2 (newAddr (alloc var9 (O_TSLL var5))))) (and (not (= var1 0)) (= var0 0))))) (inv_main19 var6 var4 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main37 var6 var5 var4) (and (is-O_TSLL (read var6 var4)) (and (and (and (= var3 var6) (= var2 var5)) (= var1 var4)) (= var0 (next (getTSLL (read var6 var4)))))))) (inv_main35 var3 var2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main34 var6 var5 var4 var3) (and (and (is-O_TSLL (read var6 var4)) (is-O_TSLL (read var6 (next (getTSLL (read var6 var4)))))) (and (and (= var2 (write var6 (next (getTSLL (read var6 var4))) (O_TSLL (TSLL var3 (data (getTSLL (read var6 (next (getTSLL (read var6 var4)))))))))) (= var1 var5)) (= var0 var4))))) (inv_main35 var2 var1 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main21 var5 var4 var3) (and (is-O_TSLL (read var5 var3)) (and (and (= var2 (write var5 var3 (O_TSLL (TSLL var4 (data (getTSLL (read var5 var3))))))) (= var1 var4)) (= var0 var3))))) (inv_main35 var2 var0 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (and (inv_main19 var2 var1 var0) (is-O_TSLL (read var2 var0)))) (inv_main21 (write var2 var0 (O_TSLL (TSLL (next (getTSLL (read var2 var0))) 1))) var1 var0))))
(assert (forall ((var0 TSLL) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main6 var4 var3 var2) (not (= var1 0)))) (inv_main11 (newHeap (alloc var4 (O_TSLL var0))) var3 var2 (newAddr (alloc var4 (O_TSLL var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (and (inv_main23 var2 var1 var0) (and (is-O_TSLL (read var2 var0)) (= (next (getTSLL (read var2 var0))) nullAddr)))) (inv_main24 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main23 var3 var2 var1) (and (not (= var0 0)) (and (is-O_TSLL (read var3 var1)) (not (= (next (getTSLL (read var3 var1))) nullAddr)))))) (inv_main24 var3 var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Int) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main35 var6 var5 var4) (and (and (not (= var3 1)) (is-O_TSLL (read var6 var4))) (and (and (and (= var2 var6) (= var1 var5)) (= var0 var4)) (= var3 (data (getTSLL (read var6 var4)))))))) (inv_main37 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Heap)) (or (not (and (inv_main3 var1 var0) (is-O_TSLL (read var1 var0)))) (inv_main4 (write var1 var0 (O_TSLL (TSLL nullAddr (data (getTSLL (read var1 var0)))))) var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main33 var4 var3 var2 var1 var0) (is-O_TSLL (read var4 var2)))) (inv_main32 (write var4 var2 (O_TSLL (TSLL var0 (data (getTSLL (read var4 var2)))))) var3 var2 var1))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main3 var1 var0) (not (is-O_TSLL (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main4 var1 var0) (not (is-O_TSLL (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main11 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main10 var2 var1 var0) (not (is-O_TSLL (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main12 var2 var1 var0) (not (is-O_TSLL (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main14 var2 var1 var0) (not (is-O_TSLL (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main19 var2 var1 var0) (not (is-O_TSLL (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main21 var2 var1 var0) (not (is-O_TSLL (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main23 var2 var1 var0) (not (is-O_TSLL (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main26 var2 var1 var0) (not (is-O_TSLL (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main24 var2 var1 var0) (not (is-O_TSLL (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main33 var4 var3 var2 var1 var0) (not (is-O_TSLL (read var4 var2)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main32 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main32 var3 var2 var1 var0) (and (is-O_TSLL (read var3 var1)) (not (is-O_TSLL (read var3 (next (getTSLL (read var3 var1)))))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main34 var3 var2 var1 var0) (not (is-O_TSLL (read var3 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main34 var3 var2 var1 var0) (and (is-O_TSLL (read var3 var1)) (not (is-O_TSLL (read var3 (next (getTSLL (read var3 var1)))))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main35 var2 var1 var0) (not (is-O_TSLL (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main37 var2 var1 var0) (not (is-O_TSLL (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main36 var2 var1 var0) (not (is-O_TSLL (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main43 var2 var1 var0) (not (is-O_TSLL (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (inv_main49 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main44 var2 var1 var0) (not (is-O_TSLL (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main56 var2 var1 var0) (not (is-O_TSLL (read var2 var0)))))))
(check-sat)
