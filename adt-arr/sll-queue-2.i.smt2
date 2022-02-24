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
(declare-fun inv_main103 (Heap Addr Addr Int) Bool)
(declare-fun inv_main106 (Heap Addr Addr Int) Bool)
(declare-fun inv_main109 (Heap Addr Addr Int) Bool)
(declare-fun inv_main11 (Heap Addr Addr Int) Bool)
(declare-fun inv_main111 (Heap Addr Addr Int) Bool)
(declare-fun inv_main119 (Heap Addr Addr Int) Bool)
(declare-fun inv_main12 (Heap Addr Addr Int Addr) Bool)
(declare-fun inv_main13 (Heap Addr Addr Int) Bool)
(declare-fun inv_main16 (Heap Addr Addr Int) Bool)
(declare-fun inv_main17 (Heap Addr Addr Int) Bool)
(declare-fun inv_main2 (Heap) Bool)
(declare-fun inv_main20 (Heap Addr Addr Int) Bool)
(declare-fun inv_main23 (Heap Addr Addr Int) Bool)
(declare-fun inv_main28 (Heap Addr Addr Int) Bool)
(declare-fun inv_main3 (Heap Addr) Bool)
(declare-fun inv_main32 (Heap Addr Addr Int) Bool)
(declare-fun inv_main37 (Heap Addr Addr Int) Bool)
(declare-fun inv_main4 (Heap Addr) Bool)
(declare-fun inv_main40 (Heap Addr Addr Int) Bool)
(declare-fun inv_main43 (Heap Addr Addr Int) Bool)
(declare-fun inv_main45 (Heap Addr Addr Int) Bool)
(declare-fun inv_main49 (Heap Addr Addr Int) Bool)
(declare-fun inv_main53 (Heap Addr Addr Int) Bool)
(declare-fun inv_main56 (Heap Addr Addr Int) Bool)
(declare-fun inv_main58 (Heap Addr Addr Int) Bool)
(declare-fun inv_main61 (Heap Addr Addr Int) Bool)
(declare-fun inv_main63 (Heap Addr Addr Int) Bool)
(declare-fun inv_main68 (Heap Addr Addr Int) Bool)
(declare-fun inv_main7 (Heap Addr Addr Int) Bool)
(declare-fun inv_main72 (Heap Addr Addr Int) Bool)
(declare-fun inv_main75 (Heap Addr Addr Int) Bool)
(declare-fun inv_main77 (Heap Addr Addr Int) Bool)
(declare-fun inv_main80 (Heap Addr Addr Int) Bool)
(declare-fun inv_main82 (Heap Addr Addr Int) Bool)
(declare-fun inv_main86 (Heap Addr Addr Int) Bool)
(declare-fun inv_main88 (Heap Addr Addr Int) Bool)
(declare-fun inv_main92 (Heap Addr Addr Int) Bool)
(declare-fun inv_main94 (Heap Addr Addr Int) Bool)
(declare-fun inv_main99 (Heap Addr Addr Int) Bool)
(assert (inv_main2 emptyHeap))
(assert (forall ((var0 Heap) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Int) (var6 Int) (var7 Heap) (var8 Int) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Int) (var13 Heap)) (or (not (and (inv_main106 var7 var4 var2 var12) (and (and (= var6 0) (and (not (= var12 0)) (and (and (and (and (= var13 var7) (= var9 var4)) (= var11 var2)) (= var8 var12)) (= var1 (data (getTSLL (read var7 var2))))))) (and (and (and (and (= var0 var13) (= var3 var9)) (= var10 var11)) (= var5 var8)) (or (and (<= 0 (+ var1 (- 1))) (= var6 1)) (and (not (<= 0 (+ var1 (- 1)))) (= var6 0))))))) (inv_main111 var0 var3 var10 var5))))
(assert (forall ((var0 Addr) (var1 Heap)) (or (not (inv_main3 var1 var0)) (inv_main4 (write var1 var0 (O_TSLL (TSLL nullAddr (data (getTSLL (read var1 var0)))))) var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Int) (var5 Heap) (var6 Heap) (var7 Addr)) (or (not (and (inv_main13 var6 var3 var0 var4) (and (= var2 0) (and (and (and (= var5 (write var6 var0 (O_TSLL (TSLL nullAddr (data (getTSLL (read var6 var0))))))) (= var7 var3)) (= var1 var0)) (= var2 var4))))) (inv_main17 var5 var7 var1 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap)) (or (not (and (inv_main53 var3 var1 var0 var2) (not (= var2 3)))) (inv_main72 var3 var1 var0 var2))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Addr) (var3 Addr) (var4 Int) (var5 Int) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main92 var8 var3 var2 var5) (and (not (= var1 3)) (and (and (and (and (= var0 var8) (= var7 var3)) (= var6 var2)) (= var4 var5)) (= var1 (data (getTSLL (read var8 (next (getTSLL (read var8 (next (getTSLL (read var8 (next (getTSLL (read var8 var3))))))))))))))))) (inv_main72 var0 var7 var6 var4))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap)) (or (not (and (inv_main40 var3 var1 var0 var2) (and (= var1 nullAddr) (= var2 2)))) (inv_main58 var3 var1 var0 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Addr) (var6 Int) (var7 Heap)) (or (not (and (inv_main17 var7 var2 var0 var4) (and (and (and (= var3 (write var7 var0 (O_TSLL (TSLL (next (getTSLL (read var7 var0))) 1)))) (= var1 var2)) (= var5 var0)) (= var6 var4)))) (inv_main16 var3 var1 var5 1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Int) (var6 Heap) (var7 Int)) (or (not (and (inv_main20 var6 var2 var1 var5) (and (and (and (= var3 (write var6 var1 (O_TSLL (TSLL (next (getTSLL (read var6 var1))) 2)))) (= var0 var2)) (= var4 var1)) (= var7 var5)))) (inv_main16 var3 var0 var4 2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Addr) (var5 Int) (var6 Heap) (var7 Heap)) (or (not (and (inv_main13 var6 var1 var0 var5) (and (not (<= 0 (+ var3 (- 2)))) (and (not (= var3 1)) (and (not (= var3 0)) (and (and (and (= var7 (write var6 var0 (O_TSLL (TSLL nullAddr (data (getTSLL (read var6 var0))))))) (= var4 var1)) (= var2 var0)) (= var3 var5))))))) (inv_main16 var7 var4 var2 var3))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Int) (var4 Addr) (var5 Int) (var6 Heap) (var7 Addr)) (or (not (and (inv_main23 var6 var2 var1 var5) (and (and (and (= var0 (write var6 var1 (O_TSLL (TSLL (next (getTSLL (read var6 var1))) 3)))) (= var4 var2)) (= var7 var1)) (= var3 var5)))) (inv_main16 var0 var4 var7 3))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Int) (var7 Int) (var8 Heap)) (or (not (and (inv_main56 var8 var2 var1 var6) (and (= var4 nullAddr) (and (and (and (and (= var0 var8) (= var3 var2)) (= var5 var1)) (= var7 var6)) (= var4 (next (getTSLL (read var8 var2)))))))) (inv_main63 var0 var3 var5 var7))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap)) (or (not (and (inv_main103 var3 var1 var0 var2) (and (not (= var1 nullAddr)) (= var0 nullAddr)))) (inv_main119 var3 var1 var1 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Heap)) (or (not (and (inv_main103 var4 var1 var0 var2) (and (not (= var1 nullAddr)) (and (= var3 0) (not (= var0 nullAddr)))))) (inv_main119 var4 var1 var1 var2))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Int) (var8 Heap) (var9 Int) (var10 Heap) (var11 Addr) (var12 Addr)) (or (not (and (inv_main119 var10 var4 var2 var7) (and (and (not (= var11 nullAddr)) (and (and (and (and (= var3 var10) (= var5 var4)) (= var0 var2)) (= var1 var7)) (= var12 (next (getTSLL (read var10 var4)))))) (and (and (and (= var8 (write var3 var0 defObj)) (= var11 var12)) (= var6 var0)) (= var9 var1))))) (inv_main119 var8 var11 var11 var9))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Addr) (var5 Int) (var6 Heap) (var7 Heap)) (or (not (and (inv_main13 var6 var1 var0 var5) (and (= var3 1) (and (not (= var3 0)) (and (and (and (= var7 (write var6 var0 (O_TSLL (TSLL nullAddr (data (getTSLL (read var6 var0))))))) (= var4 var1)) (= var2 var0)) (= var3 var5)))))) (inv_main20 var7 var4 var2 var3))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Int) (var7 Addr) (var8 Heap)) (or (not (and (inv_main86 var8 var2 var0 var6) (and (not (= var7 nullAddr)) (and (and (and (and (= var4 var8) (= var5 var2)) (= var3 var0)) (= var1 var6)) (= var7 (next (getTSLL (read var8 (next (getTSLL (read var8 (next (getTSLL (read var8 var2)))))))))))))) (inv_main92 var4 var5 var3 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap)) (or (not (and (inv_main40 var3 var1 var0 var2) (not (= var2 2)))) (inv_main53 var3 var1 var0 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Int) (var6 Heap) (var7 Addr) (var8 Int)) (or (not (and (inv_main61 var6 var1 var0 var5) (and (not (= var7 nullAddr)) (and (and (and (and (= var3 var6) (= var2 var1)) (= var4 var0)) (= var8 var5)) (= var7 (next (getTSLL (read var6 (next (getTSLL (read var6 var1))))))))))) (inv_main53 var3 var2 var4 var8))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap)) (or (not (inv_main12 var4 var1 var0 var3 var2)) (inv_main11 (write var4 var0 (O_TSLL (TSLL var2 (data (getTSLL (read var4 var0)))))) var1 var0 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap)) (or (not (and (inv_main106 var3 var1 var0 var2) (= var2 0))) (inv_main109 var3 var1 var0 var2))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap) (var5 Int) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap) (var10 Int) (var11 Heap) (var12 Int) (var13 Addr)) (or (not (and (inv_main106 var4 var2 var1 var10) (and (and (not (= var3 0)) (and (not (= var10 0)) (and (and (and (and (= var11 var4) (= var7 var2)) (= var8 var1)) (= var5 var10)) (= var0 (data (getTSLL (read var4 var1))))))) (and (and (and (and (= var9 var11) (= var6 var7)) (= var13 var8)) (= var12 var5)) (or (and (<= 0 (+ var0 (- 1))) (= var3 1)) (and (not (<= 0 (+ var0 (- 1)))) (= var3 0))))))) (inv_main109 var9 var6 var13 var12))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Addr) (var5 Int) (var6 Heap) (var7 Addr) (var8 Heap)) (or (not (and (inv_main61 var6 var2 var1 var5) (and (= var0 nullAddr) (and (and (and (and (= var8 var6) (= var4 var2)) (= var7 var1)) (= var3 var5)) (= var0 (next (getTSLL (read var6 (next (getTSLL (read var6 var2))))))))))) (inv_main68 var8 var4 var7 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Int) (var6 Int) (var7 Int) (var8 Heap)) (or (not (and (inv_main92 var8 var4 var1 var6) (and (= var5 3) (and (and (and (and (= var3 var8) (= var0 var4)) (= var2 var1)) (= var7 var6)) (= var5 (data (getTSLL (read var8 (next (getTSLL (read var8 (next (getTSLL (read var8 (next (getTSLL (read var8 var4))))))))))))))))) (inv_main99 var3 var0 var2 var7))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Int) (var6 Int) (var7 Heap) (var8 Heap)) (or (not (and (inv_main86 var7 var3 var2 var5) (and (= var0 nullAddr) (and (and (and (and (= var8 var7) (= var1 var3)) (= var4 var2)) (= var6 var5)) (= var0 (next (getTSLL (read var7 (next (getTSLL (read var7 (next (getTSLL (read var7 var3)))))))))))))) (inv_main94 var8 var1 var4 var6))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap)) (or (not (and (inv_main16 var3 var1 var0 var2) (= var1 nullAddr))) (inv_main28 var3 var1 var0 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Int) (var8 Heap)) (or (not (and (inv_main56 var8 var1 var0 var7) (and (not (= var6 nullAddr)) (and (and (and (and (= var4 var8) (= var5 var1)) (= var3 var0)) (= var2 var7)) (= var6 (next (getTSLL (read var8 var1)))))))) (inv_main61 var4 var5 var3 var2))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Int) (var4 Heap)) (or (not (and (inv_main103 var4 var2 var0 var3) (and (not (= var1 0)) (not (= var0 nullAddr))))) (inv_main106 var4 var2 var0 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap)) (or (not (and (inv_main40 var3 var1 var0 var2) (and (not (= var1 nullAddr)) (= var2 2)))) (inv_main56 var3 var1 var0 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Int) (var7 Heap) (var8 Int)) (or (not (and (inv_main43 var7 var2 var0 var6) (and (= var5 nullAddr) (and (and (and (and (= var4 var7) (= var3 var2)) (= var1 var0)) (= var8 var6)) (= var5 (next (getTSLL (read var7 var2)))))))) (inv_main49 var4 var3 var1 var8))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Addr) (var5 Int) (var6 Heap) (var7 Heap)) (or (not (and (inv_main13 var6 var1 var0 var5) (and (<= 0 (+ var3 (- 2))) (and (not (= var3 1)) (and (not (= var3 0)) (and (and (and (= var7 (write var6 var0 (O_TSLL (TSLL nullAddr (data (getTSLL (read var6 var0))))))) (= var4 var1)) (= var2 var0)) (= var3 var5))))))) (inv_main23 var7 var4 var2 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap)) (or (not (and (inv_main53 var3 var1 var0 var2) (and (not (= var1 nullAddr)) (= var2 3)))) (inv_main75 var3 var1 var0 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap) (var6 Heap) (var7 Int) (var8 Addr)) (or (not (and (inv_main75 var6 var1 var0 var4) (and (= var2 nullAddr) (and (and (and (and (= var5 var6) (= var8 var1)) (= var3 var0)) (= var7 var4)) (= var2 (next (getTSLL (read var6 var1)))))))) (inv_main82 var5 var8 var3 var7))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Heap)) (or (not (and (inv_main7 var4 var1 var0 var2) (and (not (= var1 nullAddr)) (and (= var2 1) (and (not (= var1 nullAddr)) (= var3 0)))))) (inv_main43 var4 var1 var0 var2))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Int) (var6 Addr) (var7 Heap) (var8 Heap)) (or (not (and (inv_main72 var8 var2 var0 var5) (and (and (and (and (= var7 var8) (= var3 var2)) (= var4 var0)) (= var1 var5)) (= var6 (next (getTSLL (read var8 var2))))))) (inv_main103 var7 var3 var6 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Int) (var7 Addr) (var8 Heap)) (or (not (and (inv_main109 var8 var3 var0 var6) (and (and (and (and (= var5 var8) (= var7 var3)) (= var4 var0)) (= var2 var6)) (= var1 (next (getTSLL (read var8 var0))))))) (inv_main103 var5 var7 var1 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Heap)) (or (not (and (inv_main7 var4 var1 var0 var2) (and (not (= var2 1)) (and (not (= var1 nullAddr)) (= var3 0))))) (inv_main40 var4 var1 var0 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Int) (var6 Addr) (var7 Heap) (var8 Heap)) (or (not (and (inv_main43 var7 var1 var0 var5) (and (not (= var3 nullAddr)) (and (and (and (and (= var8 var7) (= var6 var1)) (= var4 var0)) (= var2 var5)) (= var3 (next (getTSLL (read var7 var1)))))))) (inv_main40 var8 var6 var4 var2))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 TSLL) (var4 Int) (var5 Heap)) (or (not (and (inv_main7 var5 var2 var0 var4) (not (= var1 0)))) (inv_main12 (newHeap (alloc var5 (O_TSLL var3))) var2 var0 var4 (newAddr (alloc var5 (O_TSLL var3)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Heap)) (or (not (and (inv_main7 var4 var1 var0 var2) (and (= var1 nullAddr) (and (= var2 1) (and (not (= var1 nullAddr)) (= var3 0)))))) (inv_main45 var4 var1 var0 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap) (var6 Int) (var7 Heap) (var8 Addr)) (or (not (and (inv_main75 var7 var3 var1 var6) (and (not (= var8 nullAddr)) (and (and (and (and (= var5 var7) (= var0 var3)) (= var2 var1)) (= var4 var6)) (= var8 (next (getTSLL (read var7 var3)))))))) (inv_main80 var5 var0 var2 var4))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap)) (or (not (and (inv_main16 var3 var1 var0 var2) (and (not (= var0 nullAddr)) (not (= var1 nullAddr))))) (inv_main7 var3 var1 var0 var2))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Heap)) (or (not (and (inv_main4 var3 var0) (and (= var1 (write var3 var0 (O_TSLL (TSLL (next (getTSLL (read var3 var0))) 0)))) (= var2 var0)))) (inv_main7 var1 var2 var2 0))))
(assert (forall ((var0 TSLL) (var1 Heap)) (or (not (inv_main2 var1)) (inv_main3 (newHeap (alloc var1 (O_TSLL var0))) (newAddr (alloc var1 (O_TSLL var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap)) (or (not (and (inv_main53 var3 var1 var0 var2) (and (= var1 nullAddr) (= var2 3)))) (inv_main77 var3 var1 var0 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Heap)) (or (not (and (inv_main7 var4 var1 var0 var2) (and (= var1 nullAddr) (= var3 0)))) (inv_main37 var4 var1 var0 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap)) (or (not (and (inv_main16 var3 var1 var0 var2) (and (= var0 nullAddr) (not (= var1 nullAddr))))) (inv_main32 var3 var1 var0 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap) (var6 Addr) (var7 Heap) (var8 Int)) (or (not (and (inv_main80 var7 var1 var0 var4) (and (not (= var6 nullAddr)) (and (and (and (and (= var5 var7) (= var2 var1)) (= var3 var0)) (= var8 var4)) (= var6 (next (getTSLL (read var7 (next (getTSLL (read var7 var1))))))))))) (inv_main86 var5 var2 var3 var8))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Int) (var7 Heap) (var8 Addr)) (or (not (and (inv_main11 var7 var2 var0 var6) (and (and (and (and (= var3 var7) (= var5 var2)) (= var4 var0)) (= var1 var6)) (= var8 (next (getTSLL (read var7 var0))))))) (inv_main13 var3 var5 var8 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap) (var5 Int) (var6 Addr) (var7 Heap) (var8 Addr)) (or (not (and (inv_main80 var7 var1 var0 var5) (and (= var2 nullAddr) (and (and (and (and (= var4 var7) (= var6 var1)) (= var8 var0)) (= var3 var5)) (= var2 (next (getTSLL (read var7 (next (getTSLL (read var7 var1))))))))))) (inv_main88 var4 var6 var8 var3))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main3 var1 var0) (not (is-O_TSLL (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main4 var1 var0) (not (is-O_TSLL (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap)) (not (and (inv_main12 var4 var1 var0 var3 var2) (not (is-O_TSLL (read var4 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap)) (not (and (inv_main11 var3 var1 var0 var2) (not (is-O_TSLL (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap)) (not (and (inv_main13 var3 var1 var0 var2) (not (is-O_TSLL (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap)) (not (and (inv_main17 var3 var1 var0 var2) (not (is-O_TSLL (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap)) (not (and (inv_main20 var3 var1 var0 var2) (not (is-O_TSLL (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap)) (not (and (inv_main23 var3 var1 var0 var2) (not (is-O_TSLL (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap)) (not (inv_main28 var3 var1 var0 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap)) (not (inv_main32 var3 var1 var0 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap)) (not (inv_main37 var3 var1 var0 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap)) (not (inv_main45 var3 var1 var0 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap)) (not (and (inv_main43 var3 var1 var0 var2) (not (is-O_TSLL (read var3 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap)) (not (inv_main49 var3 var1 var0 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap)) (not (inv_main58 var3 var1 var0 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap)) (not (and (inv_main56 var3 var1 var0 var2) (not (is-O_TSLL (read var3 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap)) (not (inv_main63 var3 var1 var0 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap)) (not (and (inv_main61 var3 var1 var0 var2) (not (is-O_TSLL (read var3 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap)) (not (and (inv_main61 var3 var1 var0 var2) (not (is-O_TSLL (read var3 (next (getTSLL (read var3 var1))))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap)) (not (inv_main68 var3 var1 var0 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap)) (not (inv_main77 var3 var1 var0 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap)) (not (and (inv_main75 var3 var1 var0 var2) (not (is-O_TSLL (read var3 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap)) (not (inv_main82 var3 var1 var0 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap)) (not (and (inv_main80 var3 var1 var0 var2) (not (is-O_TSLL (read var3 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap)) (not (and (inv_main80 var3 var1 var0 var2) (not (is-O_TSLL (read var3 (next (getTSLL (read var3 var1))))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap)) (not (inv_main88 var3 var1 var0 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap)) (not (and (inv_main86 var3 var1 var0 var2) (not (is-O_TSLL (read var3 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap)) (not (and (inv_main86 var3 var1 var0 var2) (not (is-O_TSLL (read var3 (next (getTSLL (read var3 var1))))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap)) (not (and (inv_main86 var3 var1 var0 var2) (not (is-O_TSLL (read var3 (next (getTSLL (read var3 (next (getTSLL (read var3 var1)))))))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap)) (not (inv_main94 var3 var1 var0 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap)) (not (and (inv_main92 var3 var1 var0 var2) (not (is-O_TSLL (read var3 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap)) (not (and (inv_main92 var3 var1 var0 var2) (not (is-O_TSLL (read var3 (next (getTSLL (read var3 var1))))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap)) (not (and (inv_main92 var3 var1 var0 var2) (not (is-O_TSLL (read var3 (next (getTSLL (read var3 (next (getTSLL (read var3 var1)))))))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap)) (not (and (inv_main92 var3 var1 var0 var2) (not (is-O_TSLL (read var3 (next (getTSLL (read var3 (next (getTSLL (read var3 (next (getTSLL (read var3 var1))))))))))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap)) (not (inv_main99 var3 var1 var0 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap)) (not (and (inv_main72 var3 var1 var0 var2) (not (is-O_TSLL (read var3 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap)) (not (and (inv_main106 var3 var1 var0 var2) (and (not (= var2 0)) (not (is-O_TSLL (read var3 var0))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap)) (not (inv_main111 var3 var1 var0 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap)) (not (and (inv_main109 var3 var1 var0 var2) (not (is-O_TSLL (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap)) (not (and (inv_main119 var3 var1 var0 var2) (not (is-O_TSLL (read var3 var1)))))))
(check-sat)
