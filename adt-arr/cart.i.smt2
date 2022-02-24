(set-info :source |
    Benchmark: C_VC
    Output by Princess (http://www.philipp.ruemmer.org/princess.shtml)
|)
(set-info :status sat)
;===============================================================================
; Encoding of Heap sorts and operations
;-------------------------------------------------------------------------------
(define-sort Addr() Int)
(declare-datatypes ((HeapObject 0) (node 0))
                   (((O_Int (getInt Int)) (O_Addr (getAddr Addr)) (O_node (getnode node)) (defObj))
                   ((node (next Addr) (stock Int) (order Int)))))
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
(declare-fun inv_main12 (Heap Addr Int Addr) Bool)
(declare-fun inv_main13 (Heap Addr Int Addr) Bool)
(declare-fun inv_main14 (Heap Addr Int Addr) Bool)
(declare-fun inv_main16 (Heap Addr Addr) Bool)
(declare-fun inv_main2 (Heap) Bool)
(declare-fun inv_main20 (Heap Addr Addr Int) Bool)
(declare-fun inv_main21 (Heap Addr Addr Int) Bool)
(declare-fun inv_main26 (Heap Addr Addr Int) Bool)
(declare-fun inv_main27 (Heap Addr Addr Int) Bool)
(declare-fun inv_main28 (Heap Addr Addr Int Int) Bool)
(declare-fun inv_main3 (Heap Addr) Bool)
(declare-fun inv_main31 (Heap Addr Addr) Bool)
(declare-fun inv_main32 (Heap Addr Addr) Bool)
(declare-fun inv_main33 (Heap Addr Addr) Bool)
(declare-fun inv_main35 (Heap Addr Addr Int) Bool)
(assert (inv_main2 emptyHeap))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Addr)) (or (not (inv_main26 var2 var1 var3 var0)) (inv_main28 var2 var1 var3 var0 (stock (getnode (read var2 var3)))))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Heap) (var4 Int) (var5 Addr) (var6 Int) (var7 Heap) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Int) (var13 Addr)) (or (not (and (inv_main20 var3 var10 var5 var6) (and (and (= var0 0) (and (not (<= 0 (+ (* (- 1) var6) (- 1)))) (and (and (and (and (= var8 var3) (= var9 var10)) (= var2 var5)) (= var4 var6)) (= var1 (stock (getnode (read var3 var5))))))) (and (and (and (and (= var7 var8) (= var13 var9)) (= var11 var2)) (= var12 var4)) (or (and (<= 0 (+ (+ var4 (* (- 1) var1)) (- 1))) (= var0 1)) (and (not (<= 0 (+ (+ var4 (* (- 1) var1)) (- 1)))) (= var0 0))))))) (inv_main21 var7 var13 var11 var12))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Addr)) (or (not (and (inv_main16 var2 var1 var3) (not (= var3 nullAddr)))) (inv_main20 var2 var1 var3 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Heap) (var4 Addr)) (or (not (inv_main28 var3 var2 var4 var0 var1)) (inv_main27 (write var3 var4 (O_node (node (next (getnode (read var3 var4))) var1 (order (getnode (read var3 var4)))))) var2 var4 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Addr)) (or (not (and (inv_main27 var7 var6 var8 var2) (and (and (and (and (= var3 var7) (= var1 var6)) (= var5 var8)) (= var4 var2)) (= var0 (next (getnode (read var7 var8))))))) (inv_main16 var3 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Addr)) (or (not (and (inv_main20 var2 var1 var3 var0) (<= 0 (+ (* (- 1) var0) (- 1))))) (inv_main16 var2 var1 var3))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Int) (var3 Addr) (var4 Int) (var5 Heap) (var6 Addr) (var7 Int) (var8 Addr) (var9 Addr) (var10 Int) (var11 Heap) (var12 Addr) (var13 Addr)) (or (not (and (inv_main20 var5 var13 var8 var10) (and (and (not (= var4 0)) (and (not (<= 0 (+ (* (- 1) var10) (- 1)))) (and (and (and (and (= var11 var5) (= var12 var13)) (= var3 var8)) (= var7 var10)) (= var2 (stock (getnode (read var5 var8))))))) (and (and (and (and (= var0 var11) (= var9 var12)) (= var6 var3)) (= var1 var7)) (or (and (<= 0 (+ (+ var7 (* (- 1) var2)) (- 1))) (= var4 1)) (and (not (<= 0 (+ (+ var7 (* (- 1) var2)) (- 1)))) (= var4 0))))))) (inv_main16 var0 var9 var6))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int)) (or (not (and (inv_main3 var1 var0) (= var2 0))) (inv_main16 var1 var0 var0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr)) (or (not (inv_main31 var1 var0 var2)) (inv_main35 var1 var0 var2 (order (getnode (read var1 var2)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Heap) (var5 Addr) (var6 Addr)) (or (not (and (inv_main32 var4 var1 var5) (and (not (= var2 nullAddr)) (and (and (and (= var3 var4) (= var0 var1)) (= var6 var5)) (= var2 (next (getnode (read var4 var5)))))))) (inv_main31 var3 var0 var2))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr)) (or (not (and (inv_main16 var1 var0 var2) (and (not (= var0 nullAddr)) (= var2 nullAddr)))) (inv_main31 var1 var0 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Addr)) (or (not (inv_main21 var2 var1 var3 var0)) (inv_main26 (write var2 var3 (O_node (node (next (getnode (read var2 var3))) (stock (getnode (read var2 var3))) var0))) var1 var3 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Heap) (var3 Addr)) (or (not (inv_main12 var2 var0 var1 var3)) (inv_main13 (write var2 var3 (O_node (node (next (getnode (read var2 var3))) var1 (order (getnode (read var2 var3)))))) var0 var1 var3))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Heap) (var3 Addr)) (or (not (inv_main13 var2 var0 var1 var3)) (inv_main14 (write var2 var3 (O_node (node (next (getnode (read var2 var3))) (stock (getnode (read var2 var3))) 0))) var0 var1 var3))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Int)) (or (not (and (inv_main35 var1 var0 var2 var3) (<= 0 (+ (+ var3 (* (- 1) (stock (getnode (read var1 var2))))) (- 1))))) (inv_main33 var1 var0 var2))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Heap) (var4 node)) (or (not (and (inv_main3 var3 var0) (and (not (<= 0 (+ (* (- 1) var2) (- 1)))) (not (= var1 0))))) (inv_main12 (newHeap (alloc var3 (O_node var4))) var0 var2 (newAddr (alloc var3 (O_node var4)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr)) (or (not (inv_main33 var1 var0 var2)) (inv_main32 var1 var0 var2))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Int)) (or (not (and (inv_main35 var1 var0 var2 var3) (not (<= 0 (+ (+ var3 (* (- 1) (stock (getnode (read var1 var2))))) (- 1)))))) (inv_main32 var1 var0 var2))))
(assert (forall ((var0 Heap)) (or (not (inv_main2 var0)) (inv_main3 var0 nullAddr))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Heap) (var5 Addr) (var6 Heap) (var7 Addr)) (or (not (and (inv_main14 var4 var1 var2 var7) (and (and (and (= var6 (write var4 var7 (O_node (node var1 (stock (getnode (read var4 var7))) (order (getnode (read var4 var7))))))) (= var0 var1)) (= var3 var2)) (= var5 var7)))) (inv_main3 var6 var5))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Heap) (var3 Int)) (or (not (and (inv_main3 var2 var0) (and (<= 0 (+ (* (- 1) var3) (- 1))) (not (= var1 0))))) (inv_main3 var2 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Heap) (var3 Addr)) (not (and (inv_main12 var2 var0 var1 var3) (not (is-O_node (read var2 var3)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Heap) (var3 Addr)) (not (and (inv_main13 var2 var0 var1 var3) (not (is-O_node (read var2 var3)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Heap) (var3 Addr)) (not (and (inv_main14 var2 var0 var1 var3) (not (is-O_node (read var2 var3)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Addr)) (not (and (inv_main20 var2 var1 var3 var0) (and (not (<= 0 (+ (* (- 1) var0) (- 1)))) (not (is-O_node (read var2 var3))))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Addr)) (not (and (inv_main21 var2 var1 var3 var0) (not (is-O_node (read var2 var3)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Addr)) (not (and (inv_main26 var2 var1 var3 var0) (not (is-O_node (read var2 var3)))))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Heap) (var4 Addr)) (not (and (inv_main28 var3 var2 var4 var0 var1) (not (is-O_node (read var3 var4)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Addr)) (not (and (inv_main27 var2 var1 var3 var0) (not (is-O_node (read var2 var3)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr)) (not (and (inv_main31 var1 var0 var2) (not (is-O_node (read var1 var2)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Int)) (not (and (inv_main35 var1 var0 var2 var3) (not (is-O_node (read var1 var2)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr)) (not (inv_main33 var1 var0 var2))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr)) (not (and (inv_main32 var1 var0 var2) (not (is-O_node (read var1 var2)))))))
(check-sat)
