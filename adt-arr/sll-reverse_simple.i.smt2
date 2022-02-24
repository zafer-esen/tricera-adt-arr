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
(declare-fun inv_main10 (Heap Addr Addr) Bool)
(declare-fun inv_main11 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main12 (Heap Addr Addr) Bool)
(declare-fun inv_main14 (Heap Addr Addr) Bool)
(declare-fun inv_main15 (Heap Addr Addr) Bool)
(declare-fun inv_main2 (Heap) Bool)
(declare-fun inv_main21 (Heap Addr Addr) Bool)
(declare-fun inv_main23 (Heap Addr Addr) Bool)
(declare-fun inv_main27 (Heap Addr Addr) Bool)
(declare-fun inv_main29 (Heap Addr Addr) Bool)
(declare-fun inv_main3 (Heap Addr) Bool)
(declare-fun inv_main32 (Heap Addr Addr) Bool)
(declare-fun inv_main35 (Heap Addr Addr) Bool)
(declare-fun inv_main37 (Heap Addr Addr) Bool)
(declare-fun inv_main38 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main39 (Heap Addr Addr) Bool)
(declare-fun inv_main4 (Heap Addr) Bool)
(declare-fun inv_main41 (Heap Addr Addr) Bool)
(declare-fun inv_main45 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main46 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main50 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main52 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main56 (Heap Addr Addr Addr Int Int) Bool)
(declare-fun inv_main59 (Heap Addr Addr Addr Int Int) Bool)
(declare-fun inv_main61 (Heap Addr Addr Addr Int Int) Bool)
(declare-fun inv_main64 (Heap Addr Addr Addr Int Int) Bool)
(declare-fun inv_main65 (Heap Addr Addr Addr Int Int) Bool)
(declare-fun inv_main73 (Heap Addr Addr Addr) Bool)
(assert (inv_main2 emptyHeap))
(assert (forall ((var0 Heap) (var1 Addr)) (or (not (inv_main3 var0 var1)) (inv_main4 (write var0 var1 (O_TSLL (TSLL nullAddr (data (getTSLL (read var0 var1)))))) var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Int) (var7 Int) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Int) (var12 Addr)) (or (not (and (inv_main64 var5 var10 var9 var4 var11 var7) (and (and (and (and (and (and (= var8 var5) (= var1 var10)) (= var0 var9)) (= var12 var4)) (= var2 var11)) (= var6 var7)) (= var3 (next (getTSLL (read var5 var9))))))) (inv_main50 var8 var1 var3 var12))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main46 var5 var7 var6 var4 var3) (and (= var2 nullAddr) (and (and (and (and (= var9 (write var5 var6 (O_TSLL (TSLL var4 (data (getTSLL (read var5 var6))))))) (= var1 var7)) (= var0 var6)) (= var8 var4)) (= var2 var3))))) (inv_main50 var9 var0 var0 var0))))
(assert (forall ((var0 Heap) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr)) (or (not (and (inv_main41 var1 var7 var6) (and (and (= var9 nullAddr) (and (and (and (= var0 var5) (= var9 var2)) (= var3 var8)) (= var4 nullAddr))) (and (and (= var5 (write var1 var6 (O_TSLL (TSLL (next (getTSLL (read var1 var6))) 2)))) (= var2 var7)) (= var8 var6))))) (inv_main50 var0 var4 var4 var4))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Heap) (var9 Addr)) (or (not (and (inv_main35 var5 var7 var6) (and (and (= var9 nullAddr) (and (and (and (= var0 var8) (= var9 var4)) (= var3 var2)) (= var1 nullAddr))) (and (and (= var8 (write var5 (next (getTSLL (read var5 var6))) (O_TSLL (TSLL (next (getTSLL (read var5 (next (getTSLL (read var5 var6)))))) 2)))) (= var4 var7)) (= var2 var6))))) (inv_main50 var0 var1 var1 var1))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Int) (var7 Addr)) (or (not (and (inv_main15 var0 var4 var3) (and (= var5 nullAddr) (and (not (= var6 0)) (and (not (= var7 nullAddr)) (and (and (and (= var2 var0) (= var1 var4)) (= var5 var3)) (= var7 (next (getTSLL (read var0 var3)))))))))) (inv_main23 var2 var1 var5))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Int) (var7 Addr)) (or (not (and (inv_main15 var0 var4 var3) (and (not (= var5 nullAddr)) (and (not (= var6 0)) (and (not (= var7 nullAddr)) (and (and (and (= var2 var0) (= var1 var4)) (= var5 var3)) (= var7 (next (getTSLL (read var0 var3)))))))))) (inv_main21 var2 var1 var5))))
(assert (forall ((var0 Heap) (var1 TSLL)) (or (not (inv_main2 var0)) (inv_main3 (newHeap (alloc var0 (O_TSLL var1))) (newAddr (alloc var0 (O_TSLL var1)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Int) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Int) (var10 Int) (var11 Addr) (var12 Int)) (or (not (and (inv_main65 var3 var8 var7 var2 var9 var5) (and (and (and (and (and (and (= var0 var3) (= var4 var8)) (= var6 var7)) (= var11 var2)) (= var10 var9)) (= var12 var5)) (= var1 (next (getTSLL (read var3 var7))))))) (inv_main64 var0 var4 var1 var11 var10 var12))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Heap) (var4 Int) (var5 Int) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Int) (var10 Int) (var11 Int) (var12 Addr)) (or (not (and (inv_main59 var3 var8 var7 var2 var11 var4) (and (not (= var9 2)) (and (and (and (and (and (and (= var1 var3) (= var6 var8)) (= var12 var7)) (= var0 var2)) (= var10 var11)) (= var5 var4)) (= var9 (data (getTSLL (read var3 var7)))))))) (inv_main64 var1 var6 var12 var0 var10 var5))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr)) (or (not (inv_main27 var0 var2 var1)) (inv_main32 (write var0 var1 (O_TSLL (TSLL (next (getTSLL (read var0 var1))) 1))) var2 var1))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr)) (or (not (and (inv_main15 var1 var3 var2) (and (= var4 nullAddr) (and (= var0 nullAddr) (and (and (and (= var5 var1) (= var6 var3)) (= var4 var2)) (= var0 (next (getTSLL (read var1 var2))))))))) (inv_main29 var5 var6 var4))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Int) (var7 Addr)) (or (not (and (inv_main15 var0 var4 var3) (and (= var5 nullAddr) (and (= var6 0) (and (not (= var7 nullAddr)) (and (and (and (= var2 var0) (= var1 var4)) (= var5 var3)) (= var7 (next (getTSLL (read var0 var3)))))))))) (inv_main29 var2 var1 var5))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Int) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Int) (var11 Heap) (var12 Addr)) (or (not (and (inv_main56 var5 var8 var7 var4 var10 var6) (and (or (not (= var2 2)) (= var1 1)) (and (and (and (and (and (and (= var11 var5) (= var9 var8)) (= var12 var7)) (= var3 var4)) (= var2 var10)) (= var0 var6)) (= var1 (data (getTSLL (read var5 (next (getTSLL (read var5 var7))))))))))) (inv_main59 var11 var9 var12 var3 var2 var1))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Int) (var6 Addr) (var7 Heap) (var8 Addr)) (or (not (and (inv_main52 var1 var3 var2 var0) (and (and (not (= var5 2)) (not (= var5 2))) (and (and (and (and (= var7 var1) (= var4 var3)) (= var8 var2)) (= var6 var0)) (= var5 (data (getTSLL (read var1 var2)))))))) (inv_main59 var7 var4 var8 var6 var5 0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Int) (var6 Addr) (var7 Addr) (var8 Int) (var9 Addr) (var10 Int) (var11 Heap) (var12 Int)) (or (not (and (inv_main59 var3 var7 var6 var2 var8 var4) (and (= var12 2) (and (and (and (and (and (and (= var11 var3) (= var9 var7)) (= var0 var6)) (= var1 var2)) (= var5 var8)) (= var10 var4)) (= var12 (data (getTSLL (read var3 var6)))))))) (inv_main65 var11 var9 var0 var1 var5 var10))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Heap) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr)) (or (not (and (inv_main52 var3 var6 var5 var2) (and (= var1 2) (and (and (and (and (= var4 var3) (= var8 var6)) (= var0 var5)) (= var7 var2)) (= var1 (data (getTSLL (read var3 var5)))))))) (inv_main56 var4 var8 var0 var7 var1 0))))
(assert (forall ((var0 TSLL) (var1 Heap) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main14 var1 var5 var4) (and (not (= var2 0)) (and (and (= var7 (write var1 var4 (O_TSLL (TSLL (next (getTSLL (read var1 var4))) 0)))) (= var3 var5)) (= var6 var4))))) (inv_main11 (newHeap (alloc var7 (O_TSLL var0))) var3 var6 (newAddr (alloc var7 (O_TSLL var0)))))))
(assert (forall ((var0 Int) (var1 Heap) (var2 Addr) (var3 Addr) (var4 TSLL) (var5 Heap)) (or (not (and (inv_main4 var1 var2) (and (not (= var0 0)) (and (= var5 (write var1 var2 (O_TSLL (TSLL (next (getTSLL (read var1 var2))) 0)))) (= var3 var2))))) (inv_main11 (newHeap (alloc var5 (O_TSLL var4))) var3 var3 (newAddr (alloc var5 (O_TSLL var4)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr)) (or (not (and (inv_main50 var1 var3 var2 var0) (and (not (= var3 nullAddr)) (= var2 nullAddr)))) (inv_main73 var1 var3 var3 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Heap) (var12 Addr)) (or (not (and (inv_main73 var3 var8 var7 var2) (and (and (not (= var1 nullAddr)) (and (and (and (and (= var4 var3) (= var6 var8)) (= var10 var7)) (= var5 var2)) (= var0 (next (getTSLL (read var3 var7)))))) (and (and (and (= var11 (write var4 var6 defObj)) (= var12 var6)) (= var1 var0)) (= var9 var5))))) (inv_main73 var11 var1 var1 var9))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr)) (or (not (inv_main45 var1 var3 var2 var0)) (inv_main46 var1 var3 var2 var0 (next (getTSLL (read var1 var2)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main10 var0 var4 var3) (and (and (and (= var6 var0) (= var5 var4)) (= var2 var3)) (= var1 (next (getTSLL (read var0 var3))))))) (inv_main12 var6 var5 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main46 var5 var7 var6 var4 var3) (and (not (= var2 nullAddr)) (and (and (and (and (= var9 (write var5 var6 (O_TSLL (TSLL var4 (data (getTSLL (read var5 var6))))))) (= var1 var7)) (= var0 var6)) (= var8 var4)) (= var2 var3))))) (inv_main45 var9 var1 var2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Heap) (var9 Addr)) (or (not (and (inv_main41 var5 var7 var6) (and (and (not (= var3 nullAddr)) (and (and (and (= var8 var4) (= var3 var2)) (= var0 var9)) (= var1 nullAddr))) (and (and (= var4 (write var5 var6 (O_TSLL (TSLL (next (getTSLL (read var5 var6))) 2)))) (= var2 var7)) (= var9 var6))))) (inv_main45 var8 var3 var3 var1))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Heap) (var9 Addr)) (or (not (and (inv_main35 var1 var4 var3) (and (and (not (= var5 nullAddr)) (and (and (and (= var8 var7) (= var5 var2)) (= var6 var0)) (= var9 nullAddr))) (and (and (= var7 (write var1 (next (getTSLL (read var1 var3))) (O_TSLL (TSLL (next (getTSLL (read var1 (next (getTSLL (read var1 var3)))))) 2)))) (= var2 var4)) (= var0 var3))))) (inv_main45 var8 var5 var5 var9))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr)) (or (not (inv_main39 var0 var2 var1)) (inv_main41 (write var0 var1 (O_TSLL (TSLL nullAddr (data (getTSLL (read var0 var1)))))) var2 var1))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr)) (or (not (and (inv_main37 var2 var4 var3) (and (and (and (= var0 var2) (= var1 var4)) (= var5 var3)) (= var6 (next (getTSLL (read var2 var3))))))) (inv_main39 var0 var1 var6))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 TSLL) (var5 Addr) (var6 Heap) (var7 Addr)) (or (not (and (inv_main32 var0 var3 var2) (and (= var1 nullAddr) (and (and (and (= var6 var0) (= var5 var3)) (= var7 var2)) (= var1 (next (getTSLL (read var0 var2)))))))) (inv_main38 (newHeap (alloc var6 (O_TSLL var4))) var5 var7 (newAddr (alloc var6 (O_TSLL var4)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr)) (or (not (inv_main12 var0 var2 var1)) (inv_main14 (write var0 var1 (O_TSLL (TSLL nullAddr (data (getTSLL (read var0 var1)))))) var2 var1))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr)) (or (not (inv_main11 var1 var3 var2 var0)) (inv_main10 (write var1 var2 (O_TSLL (TSLL var0 (data (getTSLL (read var1 var2)))))) var3 var2))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Int) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Int) (var11 Heap) (var12 Addr)) (or (not (and (inv_main56 var5 var8 var7 var4 var10 var6) (and (and (= var2 2) (not (= var1 1))) (and (and (and (and (and (and (= var11 var5) (= var9 var8)) (= var12 var7)) (= var3 var4)) (= var2 var10)) (= var0 var6)) (= var1 (data (getTSLL (read var5 (next (getTSLL (read var5 var7))))))))))) (inv_main61 var11 var9 var12 var3 var2 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr)) (or (not (and (inv_main52 var2 var6 var5 var1) (and (and (= var0 2) (not (= var0 2))) (and (and (and (and (= var3 var2) (= var8 var6)) (= var7 var5)) (= var4 var1)) (= var0 (data (getTSLL (read var2 var5)))))))) (inv_main61 var3 var8 var7 var4 var0 0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main32 var2 var5 var4) (and (not (= var0 nullAddr)) (and (and (and (= var6 var2) (= var1 var5)) (= var3 var4)) (= var0 (next (getTSLL (read var2 var4)))))))) (inv_main35 var6 var1 var3))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr)) (or (not (and (inv_main21 var2 var4 var3) (and (and (and (= var1 var2) (= var0 var4)) (= var6 var3)) (= var5 (next (getTSLL (read var2 var3))))))) (inv_main15 var1 var0 var5))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Int) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main14 var2 var5 var4) (and (= var3 0) (and (and (= var6 (write var2 var4 (O_TSLL (TSLL (next (getTSLL (read var2 var4))) 0)))) (= var1 var5)) (= var0 var4))))) (inv_main15 var6 var1 var1))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Heap) (var4 Int)) (or (not (and (inv_main4 var1 var2) (and (= var4 0) (and (= var3 (write var1 var2 (O_TSLL (TSLL (next (getTSLL (read var1 var2))) 0)))) (= var0 var2))))) (inv_main15 var3 var0 var0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr)) (or (not (and (inv_main15 var1 var3 var2) (and (not (= var4 nullAddr)) (and (= var0 nullAddr) (and (and (and (= var5 var1) (= var6 var3)) (= var4 var2)) (= var0 (next (getTSLL (read var1 var2))))))))) (inv_main27 var5 var6 var4))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Int) (var7 Addr)) (or (not (and (inv_main15 var0 var4 var3) (and (not (= var5 nullAddr)) (and (= var6 0) (and (not (= var7 nullAddr)) (and (and (and (= var2 var0) (= var1 var4)) (= var5 var3)) (= var7 (next (getTSLL (read var0 var3)))))))))) (inv_main27 var2 var1 var5))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr)) (or (not (and (inv_main50 var1 var3 var2 var0) (not (= var2 nullAddr)))) (inv_main52 var1 var3 var2 var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr)) (or (not (inv_main38 var0 var2 var1 var3)) (inv_main37 (write var0 var1 (O_TSLL (TSLL var3 (data (getTSLL (read var0 var1)))))) var2 var1))))
(assert (forall ((var0 Heap) (var1 Addr)) (not (and (inv_main3 var0 var1) (not (is-O_TSLL (read var0 var1)))))))
(assert (forall ((var0 Heap) (var1 Addr)) (not (and (inv_main4 var0 var1) (not (is-O_TSLL (read var0 var1)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr)) (not (and (inv_main11 var1 var3 var2 var0) (not (is-O_TSLL (read var1 var2)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr)) (not (and (inv_main10 var0 var2 var1) (not (is-O_TSLL (read var0 var1)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr)) (not (and (inv_main12 var0 var2 var1) (not (is-O_TSLL (read var0 var1)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr)) (not (and (inv_main14 var0 var2 var1) (not (is-O_TSLL (read var0 var1)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr)) (not (and (inv_main15 var0 var2 var1) (not (is-O_TSLL (read var0 var1)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr)) (not (inv_main23 var0 var2 var1))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr)) (not (and (inv_main21 var0 var2 var1) (not (is-O_TSLL (read var0 var1)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr)) (not (inv_main29 var0 var2 var1))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr)) (not (and (inv_main27 var0 var2 var1) (not (is-O_TSLL (read var0 var1)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr)) (not (and (inv_main32 var0 var2 var1) (not (is-O_TSLL (read var0 var1)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr)) (not (and (inv_main38 var0 var2 var1 var3) (not (is-O_TSLL (read var0 var1)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr)) (not (and (inv_main37 var0 var2 var1) (not (is-O_TSLL (read var0 var1)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr)) (not (and (inv_main39 var0 var2 var1) (not (is-O_TSLL (read var0 var1)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr)) (not (and (inv_main41 var0 var2 var1) (not (is-O_TSLL (read var0 var1)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr)) (not (and (inv_main35 var0 var2 var1) (not (is-O_TSLL (read var0 var1)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr)) (not (and (inv_main35 var0 var2 var1) (not (is-O_TSLL (read var0 (next (getTSLL (read var0 var1))))))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr)) (not (and (inv_main45 var1 var3 var2 var0) (not (is-O_TSLL (read var1 var2)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr)) (not (and (inv_main46 var2 var4 var3 var1 var0) (not (is-O_TSLL (read var2 var3)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr)) (not (and (inv_main52 var1 var3 var2 var0) (not (is-O_TSLL (read var1 var2)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Addr) (var4 Addr) (var5 Int)) (not (and (inv_main56 var1 var4 var3 var0 var5 var2) (not (is-O_TSLL (read var1 var3)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Addr) (var4 Addr) (var5 Int)) (not (and (inv_main56 var1 var4 var3 var0 var5 var2) (not (is-O_TSLL (read var1 (next (getTSLL (read var1 var3))))))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Addr) (var4 Addr) (var5 Int)) (not (inv_main61 var1 var4 var3 var0 var5 var2))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Addr) (var4 Addr) (var5 Int)) (not (and (inv_main59 var1 var4 var3 var0 var5 var2) (not (is-O_TSLL (read var1 var3)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Addr) (var4 Addr) (var5 Int)) (not (and (inv_main65 var1 var4 var3 var0 var5 var2) (not (is-O_TSLL (read var1 var3)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Addr) (var4 Addr) (var5 Int)) (not (and (inv_main64 var1 var4 var3 var0 var5 var2) (not (is-O_TSLL (read var1 var3)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr)) (not (and (inv_main73 var1 var3 var2 var0) (not (is-O_TSLL (read var1 var2)))))))
(check-sat)
