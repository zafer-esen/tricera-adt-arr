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
(declare-fun inv_main101 (Heap Addr Addr Int) Bool)
(declare-fun inv_main105 (Heap Addr Addr Int) Bool)
(declare-fun inv_main108 (Heap Addr Addr Int) Bool)
(declare-fun inv_main111 (Heap Addr Addr Int) Bool)
(declare-fun inv_main113 (Heap Addr Addr Int) Bool)
(declare-fun inv_main12 (Heap Addr Addr Int) Bool)
(declare-fun inv_main121 (Heap Addr Addr Int) Bool)
(declare-fun inv_main13 (Heap Addr Addr Int Addr) Bool)
(declare-fun inv_main14 (Heap Addr Addr Int) Bool)
(declare-fun inv_main15 (Heap Addr Addr Int) Bool)
(declare-fun inv_main18 (Heap Addr Addr Int) Bool)
(declare-fun inv_main19 (Heap Addr Addr Int) Bool)
(declare-fun inv_main2 (Heap) Bool)
(declare-fun inv_main22 (Heap Addr Addr Int) Bool)
(declare-fun inv_main25 (Heap Addr Addr Int) Bool)
(declare-fun inv_main3 (Heap Addr) Bool)
(declare-fun inv_main30 (Heap Addr Addr Int) Bool)
(declare-fun inv_main34 (Heap Addr Addr Int) Bool)
(declare-fun inv_main39 (Heap Addr Addr Int) Bool)
(declare-fun inv_main4 (Heap Addr) Bool)
(declare-fun inv_main42 (Heap Addr Addr Int) Bool)
(declare-fun inv_main45 (Heap Addr Addr Int) Bool)
(declare-fun inv_main47 (Heap Addr Addr Int) Bool)
(declare-fun inv_main5 (Heap Addr) Bool)
(declare-fun inv_main51 (Heap Addr Addr Int) Bool)
(declare-fun inv_main55 (Heap Addr Addr Int) Bool)
(declare-fun inv_main58 (Heap Addr Addr Int) Bool)
(declare-fun inv_main60 (Heap Addr Addr Int) Bool)
(declare-fun inv_main63 (Heap Addr Addr Int) Bool)
(declare-fun inv_main65 (Heap Addr Addr Int) Bool)
(declare-fun inv_main70 (Heap Addr Addr Int) Bool)
(declare-fun inv_main74 (Heap Addr Addr Int) Bool)
(declare-fun inv_main77 (Heap Addr Addr Int) Bool)
(declare-fun inv_main79 (Heap Addr Addr Int) Bool)
(declare-fun inv_main8 (Heap Addr Addr Int) Bool)
(declare-fun inv_main82 (Heap Addr Addr Int) Bool)
(declare-fun inv_main84 (Heap Addr Addr Int) Bool)
(declare-fun inv_main88 (Heap Addr Addr Int) Bool)
(declare-fun inv_main90 (Heap Addr Addr Int) Bool)
(declare-fun inv_main94 (Heap Addr Addr Int) Bool)
(declare-fun inv_main96 (Heap Addr Addr Int) Bool)
(assert (inv_main2 emptyHeap))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Int)) (or (not (and (inv_main74 var2 var6 var5 var8) (and (and (and (and (= var4 var2) (= var7 var6)) (= var3 var5)) (= var0 var8)) (= var1 (next (getTSLL (read var2 var6))))))) (inv_main105 var4 var7 var1 var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Int) (var7 Int) (var8 Addr)) (or (not (and (inv_main111 var2 var5 var4 var7) (and (and (and (and (= var0 var2) (= var8 var5)) (= var3 var4)) (= var6 var7)) (= var1 (next (getTSLL (read var2 var4))))))) (inv_main105 var0 var8 var1 var6))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Int)) (or (not (inv_main12 var0 var2 var1 var3)) (inv_main14 (write var0 (next (getTSLL (read var0 var1))) (O_TSLL (TSLL (next (getTSLL (read var0 (next (getTSLL (read var0 var1)))))) var1 (data (getTSLL (read var0 (next (getTSLL (read var0 var1))))))))) var2 var1 var3))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Int)) (or (not (inv_main13 var1 var3 var2 var4 var0)) (inv_main12 (write var1 var2 (O_TSLL (TSLL var0 (prev (getTSLL (read var1 var2))) (data (getTSLL (read var1 var2)))))) var3 var2 var4))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Int) (var6 Heap) (var7 Addr) (var8 Addr)) (or (not (and (inv_main77 var0 var3 var2 var5) (and (not (= var7 nullAddr)) (and (and (and (and (= var6 var0) (= var8 var3)) (= var4 var2)) (= var1 var5)) (= var7 (next (getTSLL (read var0 var3)))))))) (inv_main82 var6 var8 var4 var1))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Int)) (or (not (and (inv_main42 var0 var2 var1 var3) (and (not (= var2 nullAddr)) (= var3 2)))) (inv_main58 var0 var2 var1 var3))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int)) (or (not (and (inv_main105 var0 var2 var1 var3) (and (not (= var4 0)) (not (= var1 nullAddr))))) (inv_main108 var0 var2 var1 var3))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Int) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Int) (var8 Heap)) (or (not (and (inv_main45 var1 var5 var4 var7) (and (= var0 nullAddr) (and (and (and (and (= var8 var1) (= var6 var5)) (= var2 var4)) (= var3 var7)) (= var0 (next (getTSLL (read var1 var5)))))))) (inv_main51 var8 var6 var2 var3))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Int) (var4 TSLL) (var5 Int)) (or (not (and (inv_main8 var0 var2 var1 var3) (not (= var5 0)))) (inv_main13 (newHeap (alloc var0 (O_TSLL var4))) var2 var1 var3 (newAddr (alloc var0 (O_TSLL var4)))))))
(assert (forall ((var0 Int) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Int)) (or (not (and (inv_main8 var1 var3 var2 var4) (and (= var3 nullAddr) (and (= var4 1) (and (not (= var3 nullAddr)) (= var0 0)))))) (inv_main47 var1 var3 var2 var4))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Int)) (or (not (and (inv_main55 var0 var2 var1 var3) (not (= var3 3)))) (inv_main74 var0 var2 var1 var3))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Heap) (var3 Int) (var4 Addr) (var5 Addr) (var6 Int) (var7 Int) (var8 Addr)) (or (not (and (inv_main94 var2 var5 var4 var6) (and (not (= var7 3)) (and (and (and (and (= var1 var2) (= var8 var5)) (= var0 var4)) (= var3 var6)) (= var7 (data (getTSLL (read var2 (next (getTSLL (read var2 (next (getTSLL (read var2 (next (getTSLL (read var2 var5))))))))))))))))) (inv_main74 var1 var8 var0 var3))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Int)) (or (not (and (inv_main55 var0 var2 var1 var3) (and (= var2 nullAddr) (= var3 3)))) (inv_main79 var0 var2 var1 var3))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Int)) (or (not (and (inv_main55 var0 var2 var1 var3) (and (not (= var2 nullAddr)) (= var3 3)))) (inv_main77 var0 var2 var1 var3))))
(assert (forall ((var0 Heap) (var1 Addr)) (or (not (inv_main4 var0 var1)) (inv_main5 (write var0 var1 (O_TSLL (TSLL (next (getTSLL (read var0 var1))) nullAddr (data (getTSLL (read var0 var1)))))) var1))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Int) (var8 Int)) (or (not (and (inv_main77 var3 var5 var4 var7) (and (= var6 nullAddr) (and (and (and (and (= var0 var3) (= var1 var5)) (= var2 var4)) (= var8 var7)) (= var6 (next (getTSLL (read var3 var5)))))))) (inv_main84 var0 var1 var2 var8))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Int) (var7 Int) (var8 Addr)) (or (not (and (inv_main58 var0 var4 var3 var7) (and (= var8 nullAddr) (and (and (and (and (= var5 var0) (= var2 var4)) (= var1 var3)) (= var6 var7)) (= var8 (next (getTSLL (read var0 var4)))))))) (inv_main65 var5 var2 var1 var6))))
(assert (forall ((var0 Int) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Int) (var6 Int) (var7 Addr) (var8 Heap)) (or (not (and (inv_main94 var1 var3 var2 var5) (and (= var6 3) (and (and (and (and (= var8 var1) (= var7 var3)) (= var4 var2)) (= var0 var5)) (= var6 (data (getTSLL (read var1 (next (getTSLL (read var1 (next (getTSLL (read var1 (next (getTSLL (read var1 var3))))))))))))))))) (inv_main101 var8 var7 var4 var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Int)) (or (not (and (inv_main18 var0 var2 var1 var3) (= var2 nullAddr))) (inv_main30 var0 var2 var1 var3))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Int)) (or (not (and (inv_main108 var0 var2 var1 var3) (= var3 0))) (inv_main111 var0 var2 var1 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Int) (var6 Heap) (var7 Int) (var8 Int) (var9 Int) (var10 Heap) (var11 Addr) (var12 Heap) (var13 Addr)) (or (not (and (inv_main108 var10 var3 var11 var5) (and (and (not (= var4 0)) (and (not (= var5 0)) (and (and (and (and (= var6 var10) (= var1 var3)) (= var0 var11)) (= var9 var5)) (= var7 (data (getTSLL (read var10 var11))))))) (and (and (and (and (= var12 var6) (= var2 var1)) (= var13 var0)) (= var8 var9)) (or (and (<= 0 (+ var7 (- 1))) (= var4 1)) (and (not (<= 0 (+ var7 (- 1)))) (= var4 0))))))) (inv_main111 var12 var2 var13 var8))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Int) (var8 Int)) (or (not (and (inv_main88 var2 var4 var3 var7) (and (= var0 nullAddr) (and (and (and (and (= var6 var2) (= var5 var4)) (= var1 var3)) (= var8 var7)) (= var0 (next (getTSLL (read var2 (next (getTSLL (read var2 (next (getTSLL (read var2 var4)))))))))))))) (inv_main96 var6 var5 var1 var8))))
(assert (forall ((var0 Heap) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Int) (var6 Addr) (var7 Int) (var8 Addr)) (or (not (and (inv_main63 var1 var3 var2 var5) (and (= var6 nullAddr) (and (and (and (and (= var0 var1) (= var4 var3)) (= var8 var2)) (= var7 var5)) (= var6 (next (getTSLL (read var1 (next (getTSLL (read var1 var3))))))))))) (inv_main70 var0 var4 var8 var7))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Int)) (or (not (and (inv_main105 var0 var2 var1 var3) (and (not (= var2 nullAddr)) (= var1 nullAddr)))) (inv_main121 var0 var2 var2 var3))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int)) (or (not (and (inv_main105 var0 var2 var1 var4) (and (not (= var2 nullAddr)) (and (= var3 0) (not (= var1 nullAddr)))))) (inv_main121 var0 var2 var2 var4))))
(assert (forall ((var0 Heap) (var1 Heap) (var2 Heap) (var3 Int) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Int) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Int)) (or (not (and (inv_main121 var0 var5 var4 var8) (and (and (not (= var9 nullAddr)) (and (and (and (and (= var2 var0) (= var11 var5)) (= var7 var4)) (= var3 var8)) (= var6 (next (getTSLL (read var0 var5)))))) (and (and (and (= var1 (write var2 var7 defObj)) (= var9 var6)) (= var10 var7)) (= var12 var3))))) (inv_main121 var1 var9 var9 var12))))
(assert (forall ((var0 Int) (var1 Heap) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Int)) (or (not (and (inv_main15 var1 var5 var4 var7) (and (= var0 0) (and (and (and (= var3 (write var1 var4 (O_TSLL (TSLL nullAddr (prev (getTSLL (read var1 var4))) (data (getTSLL (read var1 var4))))))) (= var2 var5)) (= var6 var4)) (= var0 var7))))) (inv_main19 var3 var2 var6 var0))))
(assert (forall ((var0 Int) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Int)) (or (not (and (inv_main8 var1 var3 var2 var4) (and (not (= var3 nullAddr)) (and (= var4 1) (and (not (= var3 nullAddr)) (= var0 0)))))) (inv_main45 var1 var3 var2 var4))))
(assert (forall ((var0 Int) (var1 Heap) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Int) (var8 Addr)) (or (not (and (inv_main82 var2 var5 var4 var7) (and (not (= var6 nullAddr)) (and (and (and (and (= var1 var2) (= var3 var5)) (= var8 var4)) (= var0 var7)) (= var6 (next (getTSLL (read var2 (next (getTSLL (read var2 var5))))))))))) (inv_main88 var1 var3 var8 var0))))
(assert (forall ((var0 Int) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Int)) (or (not (and (inv_main8 var1 var3 var2 var4) (and (= var3 nullAddr) (= var0 0)))) (inv_main39 var1 var3 var2 var4))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Int)) (or (not (and (inv_main42 var0 var2 var1 var3) (and (= var2 nullAddr) (= var3 2)))) (inv_main60 var0 var2 var1 var3))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Int)) (or (not (and (inv_main18 var0 var2 var1 var3) (and (= var1 nullAddr) (not (= var2 nullAddr))))) (inv_main34 var0 var2 var1 var3))))
(assert (forall ((var0 Int) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Int)) (or (not (and (inv_main8 var1 var3 var2 var4) (and (not (= var4 1)) (and (not (= var3 nullAddr)) (= var0 0))))) (inv_main42 var1 var3 var2 var4))))
(assert (forall ((var0 Heap) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Int) (var6 Addr) (var7 Int) (var8 Addr)) (or (not (and (inv_main45 var0 var3 var2 var7) (and (not (= var4 nullAddr)) (and (and (and (and (= var1 var0) (= var6 var3)) (= var8 var2)) (= var5 var7)) (= var4 (next (getTSLL (read var0 var3)))))))) (inv_main42 var1 var6 var8 var5))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Int) (var6 Addr) (var7 Int) (var8 Addr)) (or (not (and (inv_main14 var0 var4 var3 var5) (and (and (and (and (= var2 var0) (= var1 var4)) (= var6 var3)) (= var7 var5)) (= var8 (next (getTSLL (read var0 var3))))))) (inv_main15 var2 var1 var8 var7))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Int)) (or (not (and (inv_main18 var0 var2 var1 var3) (and (not (= var1 nullAddr)) (not (= var2 nullAddr))))) (inv_main8 var0 var2 var1 var3))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Heap) (var3 Addr)) (or (not (and (inv_main5 var1 var3) (and (= var2 (write var1 var3 (O_TSLL (TSLL (next (getTSLL (read var1 var3))) (prev (getTSLL (read var1 var3))) 0)))) (= var0 var3)))) (inv_main8 var2 var0 var0 0))))
(assert (forall ((var0 Int) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Int) (var8 Addr)) (or (not (and (inv_main58 var1 var4 var3 var7) (and (not (= var2 nullAddr)) (and (and (and (and (= var6 var1) (= var8 var4)) (= var5 var3)) (= var0 var7)) (= var2 (next (getTSLL (read var1 var4)))))))) (inv_main63 var6 var8 var5 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Int) (var6 Heap) (var7 Addr)) (or (not (and (inv_main15 var2 var4 var3 var5) (and (= var0 1) (and (not (= var0 0)) (and (and (and (= var6 (write var2 var3 (O_TSLL (TSLL nullAddr (prev (getTSLL (read var2 var3))) (data (getTSLL (read var2 var3))))))) (= var7 var4)) (= var1 var3)) (= var0 var5)))))) (inv_main22 var6 var7 var1 var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Int)) (or (not (and (inv_main42 var0 var2 var1 var3) (not (= var3 2)))) (inv_main55 var0 var2 var1 var3))))
(assert (forall ((var0 Int) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Int) (var7 Addr) (var8 Heap)) (or (not (and (inv_main63 var1 var4 var3 var6) (and (not (= var5 nullAddr)) (and (and (and (and (= var8 var1) (= var2 var4)) (= var7 var3)) (= var0 var6)) (= var5 (next (getTSLL (read var1 (next (getTSLL (read var1 var4))))))))))) (inv_main55 var8 var2 var7 var0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Int) (var7 Int) (var8 Addr)) (or (not (and (inv_main88 var3 var5 var4 var7) (and (not (= var0 nullAddr)) (and (and (and (and (= var1 var3) (= var2 var5)) (= var8 var4)) (= var6 var7)) (= var0 (next (getTSLL (read var3 (next (getTSLL (read var3 (next (getTSLL (read var3 var5)))))))))))))) (inv_main94 var1 var2 var8 var6))))
(assert (forall ((var0 TSLL) (var1 Heap)) (or (not (inv_main2 var1)) (inv_main3 (newHeap (alloc var1 (O_TSLL var0))) (newAddr (alloc var1 (O_TSLL var0)))))))
(assert (forall ((var0 Heap) (var1 Addr)) (or (not (inv_main3 var0 var1)) (inv_main4 (write var0 var1 (O_TSLL (TSLL nullAddr (prev (getTSLL (read var0 var1))) (data (getTSLL (read var0 var1)))))) var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Int) (var6 Heap) (var7 Addr)) (or (not (and (inv_main15 var2 var4 var3 var5) (and (<= 0 (+ var0 (- 2))) (and (not (= var0 1)) (and (not (= var0 0)) (and (and (and (= var6 (write var2 var3 (O_TSLL (TSLL nullAddr (prev (getTSLL (read var2 var3))) (data (getTSLL (read var2 var3))))))) (= var7 var4)) (= var1 var3)) (= var0 var5))))))) (inv_main25 var6 var7 var1 var0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Int) (var7 Int) (var8 Addr)) (or (not (and (inv_main82 var2 var4 var3 var6) (and (= var0 nullAddr) (and (and (and (and (= var1 var2) (= var5 var4)) (= var8 var3)) (= var7 var6)) (= var0 (next (getTSLL (read var2 (next (getTSLL (read var2 var4))))))))))) (inv_main90 var1 var5 var8 var7))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Int) (var6 Int) (var7 Addr)) (or (not (and (inv_main19 var1 var3 var2 var6) (and (and (and (= var4 (write var1 var2 (O_TSLL (TSLL (next (getTSLL (read var1 var2))) (prev (getTSLL (read var1 var2))) 1)))) (= var7 var3)) (= var0 var2)) (= var5 var6)))) (inv_main18 var4 var7 var0 1))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Int) (var6 Int) (var7 Heap)) (or (not (and (inv_main22 var1 var4 var3 var5) (and (and (and (= var7 (write var1 var3 (O_TSLL (TSLL (next (getTSLL (read var1 var3))) (prev (getTSLL (read var1 var3))) 2)))) (= var2 var4)) (= var0 var3)) (= var6 var5)))) (inv_main18 var7 var2 var0 2))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Int) (var6 Heap) (var7 Addr)) (or (not (and (inv_main15 var2 var4 var3 var5) (and (not (<= 0 (+ var0 (- 2)))) (and (not (= var0 1)) (and (not (= var0 0)) (and (and (and (= var6 (write var2 var3 (O_TSLL (TSLL nullAddr (prev (getTSLL (read var2 var3))) (data (getTSLL (read var2 var3))))))) (= var7 var4)) (= var1 var3)) (= var0 var5))))))) (inv_main18 var6 var7 var1 var0))))
(assert (forall ((var0 Heap) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Int) (var5 Addr) (var6 Addr) (var7 Int)) (or (not (and (inv_main25 var1 var3 var2 var4) (and (and (and (= var0 (write var1 var2 (O_TSLL (TSLL (next (getTSLL (read var1 var2))) (prev (getTSLL (read var1 var2))) 3)))) (= var6 var3)) (= var5 var2)) (= var7 var4)))) (inv_main18 var0 var6 var5 3))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Int) (var5 Int) (var6 Heap) (var7 Int) (var8 Int) (var9 Heap) (var10 Heap) (var11 Addr) (var12 Addr) (var13 Addr)) (or (not (and (inv_main108 var9 var3 var11 var5) (and (and (= var1 0) (and (not (= var5 0)) (and (and (and (and (= var6 var9) (= var2 var3)) (= var0 var11)) (= var8 var5)) (= var7 (data (getTSLL (read var9 var11))))))) (and (and (and (and (= var10 var6) (= var13 var2)) (= var12 var0)) (= var4 var8)) (or (and (<= 0 (+ var7 (- 1))) (= var1 1)) (and (not (<= 0 (+ var7 (- 1)))) (= var1 0))))))) (inv_main113 var10 var13 var12 var4))))
(assert (forall ((var0 Heap) (var1 Addr)) (not (and (inv_main3 var0 var1) (not (is-O_TSLL (read var0 var1)))))))
(assert (forall ((var0 Heap) (var1 Addr)) (not (and (inv_main4 var0 var1) (not (is-O_TSLL (read var0 var1)))))))
(assert (forall ((var0 Heap) (var1 Addr)) (not (and (inv_main5 var0 var1) (not (is-O_TSLL (read var0 var1)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Int)) (not (and (inv_main13 var1 var3 var2 var4 var0) (not (is-O_TSLL (read var1 var2)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Int)) (not (and (inv_main12 var0 var2 var1 var3) (not (is-O_TSLL (read var0 var1)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Int)) (not (and (inv_main12 var0 var2 var1 var3) (not (is-O_TSLL (read var0 (next (getTSLL (read var0 var1))))))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Int)) (not (and (inv_main14 var0 var2 var1 var3) (not (is-O_TSLL (read var0 var1)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Int)) (not (and (inv_main15 var0 var2 var1 var3) (not (is-O_TSLL (read var0 var1)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Int)) (not (and (inv_main19 var0 var2 var1 var3) (not (is-O_TSLL (read var0 var1)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Int)) (not (and (inv_main22 var0 var2 var1 var3) (not (is-O_TSLL (read var0 var1)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Int)) (not (and (inv_main25 var0 var2 var1 var3) (not (is-O_TSLL (read var0 var1)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Int)) (not (inv_main30 var0 var2 var1 var3))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Int)) (not (inv_main34 var0 var2 var1 var3))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Int)) (not (inv_main39 var0 var2 var1 var3))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Int)) (not (inv_main47 var0 var2 var1 var3))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Int)) (not (and (inv_main45 var0 var2 var1 var3) (not (is-O_TSLL (read var0 var2)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Int)) (not (inv_main51 var0 var2 var1 var3))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Int)) (not (inv_main60 var0 var2 var1 var3))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Int)) (not (and (inv_main58 var0 var2 var1 var3) (not (is-O_TSLL (read var0 var2)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Int)) (not (inv_main65 var0 var2 var1 var3))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Int)) (not (and (inv_main63 var0 var2 var1 var3) (not (is-O_TSLL (read var0 var2)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Int)) (not (and (inv_main63 var0 var2 var1 var3) (not (is-O_TSLL (read var0 (next (getTSLL (read var0 var2))))))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Int)) (not (inv_main70 var0 var2 var1 var3))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Int)) (not (inv_main79 var0 var2 var1 var3))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Int)) (not (and (inv_main77 var0 var2 var1 var3) (not (is-O_TSLL (read var0 var2)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Int)) (not (inv_main84 var0 var2 var1 var3))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Int)) (not (and (inv_main82 var0 var2 var1 var3) (not (is-O_TSLL (read var0 var2)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Int)) (not (and (inv_main82 var0 var2 var1 var3) (not (is-O_TSLL (read var0 (next (getTSLL (read var0 var2))))))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Int)) (not (inv_main90 var0 var2 var1 var3))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Int)) (not (and (inv_main88 var0 var2 var1 var3) (not (is-O_TSLL (read var0 var2)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Int)) (not (and (inv_main88 var0 var2 var1 var3) (not (is-O_TSLL (read var0 (next (getTSLL (read var0 var2))))))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Int)) (not (and (inv_main88 var0 var2 var1 var3) (not (is-O_TSLL (read var0 (next (getTSLL (read var0 (next (getTSLL (read var0 var2)))))))))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Int)) (not (inv_main96 var0 var2 var1 var3))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Int)) (not (and (inv_main94 var0 var2 var1 var3) (not (is-O_TSLL (read var0 var2)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Int)) (not (and (inv_main94 var0 var2 var1 var3) (not (is-O_TSLL (read var0 (next (getTSLL (read var0 var2))))))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Int)) (not (and (inv_main94 var0 var2 var1 var3) (not (is-O_TSLL (read var0 (next (getTSLL (read var0 (next (getTSLL (read var0 var2)))))))))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Int)) (not (and (inv_main94 var0 var2 var1 var3) (not (is-O_TSLL (read var0 (next (getTSLL (read var0 (next (getTSLL (read var0 (next (getTSLL (read var0 var2))))))))))))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Int)) (not (inv_main101 var0 var2 var1 var3))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Int)) (not (and (inv_main74 var0 var2 var1 var3) (not (is-O_TSLL (read var0 var2)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Int)) (not (and (inv_main108 var0 var2 var1 var3) (and (not (= var3 0)) (not (is-O_TSLL (read var0 var1))))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Int)) (not (inv_main113 var0 var2 var1 var3))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Int)) (not (and (inv_main111 var0 var2 var1 var3) (not (is-O_TSLL (read var0 var1)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Int)) (not (and (inv_main121 var0 var2 var1 var3) (not (is-O_TSLL (read var0 var2)))))))
(check-sat)
