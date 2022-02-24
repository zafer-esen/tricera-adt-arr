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
(declare-datatypes ((HeapObject 0) (node 0))
                   (((O_Int (getInt Int)) (O_Addr (getAddr Addr)) (O_node (getnode node)) (defObj))
                   ((node (expected_list Int) (value Int) (next Addr)))))
(declare-datatypes ((AllocResHeap 0) (Heap 0))
                   (((AllocResHeap   (newHeap Heap) (newAddr Addr)))
                    ((HeapCtor (HeapSize Int)
                               (HeapContents (Array Addr HeapObject))))))
(define-fun nullAddr  () Addr 0)
(define-fun defHeapObject    () HeapObject defObj)
(define-fun valid     ((h Heap) (p Addr)) Bool
  (and (>= (HeapSize h) p) (> p 0)))
(define-fun emptyHeap () Heap (
  HeapCtor 0 (( as const (Array Addr HeapObject)) defHeapObject)))
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

;===============================================================================
(declare-fun inv_main17 (Heap Addr Int Int Int Int Addr) Bool)
(declare-fun inv_main18 (Heap Addr Int Int Int Int Addr) Bool)
(declare-fun inv_main19 (Heap Addr Int Int Int Int Addr) Bool)
(declare-fun inv_main2 (Heap) Bool)
(declare-fun inv_main24 (Heap Addr Int Int Int Int Addr) Bool)
(declare-fun inv_main25 (Heap Addr Int Int Int Int Addr) Bool)
(declare-fun inv_main26 (Heap Addr Int Int Int Int Addr) Bool)
(declare-fun inv_main32 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main33 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main36 (Heap Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main37 (Heap Addr Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main41 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main42 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main43 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main47 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main48 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main49 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main6 (Heap Addr) Bool)
(assert (inv_main2 emptyHeap))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Heap) (var4 Int) (var5 Int) (var6 Addr)) (or (not (inv_main24 var3 var2 var1 var5 var4 var0 var6)) (inv_main25 (write var3 var6 (O_node (node (expected_list (getnode (read var3 var6))) (value (getnode (read var3 var6))) var2))) var2 var1 var5 var4 var0 var6))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Addr)) (or (not (and (inv_main32 var1 var0 var3 var2 var4) (and (not (= var2 nullAddr)) (= var3 nullAddr)))) (inv_main47 var1 var0 var3 var2 var4))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main48 var4 var2 var7 var6 var8) (and (not (= var1 nullAddr)) (and (and (and (and (and (= var10 var4) (= var9 var2)) (= var0 var7)) (= var5 var6)) (= var3 var8)) (= var1 (next (getnode (read var4 var6)))))))) (inv_main47 var10 var9 var0 var1 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Addr)) (or (not (and (inv_main33 var4 var1 var9 var8 var10) (and (<= 0 var3) (and (and (and (and (and (= var7 var4) (= var6 var1)) (= var2 var9)) (= var5 var8)) (= var0 var10)) (= var3 (value (getnode (read var4 var10)))))))) (inv_main36 var7 var6 var2 var5 var0 var5))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr)) (or (not (and (inv_main33 var1 var0 var9 var8 var10) (and (not (<= 0 var2)) (and (and (and (and (and (= var6 var1) (= var7 var0)) (= var5 var9)) (= var4 var8)) (= var3 var10)) (= var2 (value (getnode (read var1 var10)))))))) (inv_main36 var6 var7 var5 var4 var3 var5))))
(assert (forall ((var0 Int) (var1 node) (var2 Int) (var3 Addr) (var4 Heap)) (or (not (and (inv_main6 var4 var3) (and (not (<= 0 (+ (* (- 1) var2) (- 1)))) (not (= var0 0))))) (inv_main24 (newHeap (alloc var4 (O_node var1))) var3 var2 1 var2 1 (newAddr (alloc var4 (O_node var1)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Addr)) (or (not (inv_main43 var1 var0 var3 var2 var4)) (inv_main42 var1 var0 var3 var2 var4))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Int) (var10 Addr)) (or (not (and (inv_main41 var4 var2 var7 var6 var8) (and (= var9 (- 1)) (and (and (and (and (and (= var0 var4) (= var3 var2)) (= var1 var7)) (= var5 var6)) (= var10 var8)) (= var9 (expected_list (getnode (read var4 var7)))))))) (inv_main42 var0 var3 var1 var5 var10))))
(assert (forall ((var0 Heap) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr)) (or (not (and (inv_main37 var1 var8 var12 var11 var13 var6 var7) (and (not (= var10 nullAddr)) (and (and (and (and (and (and (= var0 (write var1 var13 (O_node (node (expected_list (getnode (read var1 var13))) (value (getnode (read var1 var13))) var6)))) (= var2 var8)) (= var3 var12)) (= var5 var11)) (= var4 var13)) (= var9 var6)) (= var10 var7))))) (inv_main33 var0 var2 var3 var5 var10))))
(assert (forall ((var0 Heap) (var1 Heap) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Addr)) (or (not (and (inv_main6 var6 var5) (and (and (and (not (= var7 nullAddr)) (and (and (and (= var1 var0) (= var7 var8)) (= var4 var9)) (= var3 nullAddr))) (and (and (= var0 var6) (= var8 var5)) (= var9 nullAddr))) (= var2 0)))) (inv_main33 var1 var7 var4 var3 var7))))
(assert (forall ((var0 Int) (var1 Heap) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Int) (var7 Addr) (var8 Int) (var9 Addr) (var10 Int) (var11 Int) (var12 Int) (var13 Int)) (or (not (and (inv_main19 var5 var4 var2 var13 var12 var11 var9) (and (and (and (and (and (and (= var1 (write var5 var9 (O_node (node var11 (value (getnode (read var5 var9))) (next (getnode (read var5 var9))))))) (= var7 var4)) (= var6 var2)) (= var0 var13)) (= var8 var12)) (= var10 var11)) (= var3 var9)))) (inv_main6 var1 var3))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Int) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Int) (var9 Int) (var10 Heap) (var11 Int) (var12 Int) (var13 Int)) (or (not (and (inv_main26 var5 var4 var3 var12 var11 var0 var7) (and (and (and (and (and (and (= var10 (write var5 var7 (O_node (node var0 (value (getnode (read var5 var7))) (next (getnode (read var5 var7))))))) (= var2 var4)) (= var1 var3)) (= var9 var12)) (= var13 var11)) (= var8 var0)) (= var6 var7)))) (inv_main6 var10 var6))))
(assert (forall ((var0 Heap)) (or (not (inv_main2 var0)) (inv_main6 var0 nullAddr))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Int) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr)) (or (not (and (inv_main47 var4 var3 var8 var7 var9) (and (not (= var6 1)) (and (and (and (and (and (= var0 var4) (= var1 var3)) (= var2 var8)) (= var10 var7)) (= var5 var9)) (= var6 (expected_list (getnode (read var4 var7)))))))) (inv_main49 var0 var1 var2 var10 var5))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Addr)) (or (not (and (inv_main32 var1 var0 var3 var2 var4) (not (= var3 nullAddr)))) (inv_main41 var1 var0 var3 var2 var4))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Int) (var4 node)) (or (not (and (inv_main6 var2 var1) (and (<= 0 (+ (* (- 1) var3) (- 1))) (not (= var0 0))))) (inv_main17 (newHeap (alloc var2 (O_node var4))) var1 var3 1 var3 (- 1) (newAddr (alloc var2 (O_node var4)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Heap) (var3 Int) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr)) (or (not (and (inv_main41 var2 var0 var7 var6 var8) (and (not (= var3 (- 1))) (and (and (and (and (and (= var1 var2) (= var4 var0)) (= var10 var7)) (= var5 var6)) (= var9 var8)) (= var3 (expected_list (getnode (read var2 var7)))))))) (inv_main43 var1 var4 var10 var5 var9))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr)) (or (not (inv_main36 var2 var1 var4 var3 var5 var0)) (inv_main37 var2 var1 var4 var3 var5 var0 (next (getnode (read var2 var5)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Addr)) (or (not (inv_main49 var1 var0 var3 var2 var4)) (inv_main48 var1 var0 var3 var2 var4))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Int) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main47 var3 var1 var7 var6 var8) (and (= var5 1) (and (and (and (and (and (= var10 var3) (= var4 var1)) (= var2 var7)) (= var9 var6)) (= var0 var8)) (= var5 (expected_list (getnode (read var3 var6)))))))) (inv_main48 var10 var4 var2 var9 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Heap) (var4 Int) (var5 Int) (var6 Int)) (or (not (inv_main18 var3 var2 var1 var6 var5 var4 var0)) (inv_main19 (write var3 var0 (O_node (node (expected_list (getnode (read var3 var0))) var5 (next (getnode (read var3 var0)))))) var2 var1 var6 var5 var4 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Heap) (var4 Int) (var5 Int) (var6 Int)) (or (not (inv_main17 var3 var2 var1 var6 var5 var4 var0)) (inv_main18 (write var3 var0 (O_node (node (expected_list (getnode (read var3 var0))) (value (getnode (read var3 var0))) var2))) var2 var1 var6 var5 var4 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Heap) (var4 Int) (var5 Int) (var6 Addr)) (or (not (inv_main25 var3 var2 var1 var5 var4 var0 var6)) (inv_main26 (write var3 var6 (O_node (node (expected_list (getnode (read var3 var6))) var4 (next (getnode (read var3 var6)))))) var2 var1 var5 var4 var0 var6))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap) (var9 Addr) (var10 Addr)) (or (not (and (inv_main42 var3 var1 var6 var5 var7) (and (and (and (and (and (= var8 var3) (= var10 var1)) (= var4 var6)) (= var9 var5)) (= var0 var7)) (= var2 (next (getnode (read var3 var6))))))) (inv_main32 var8 var10 var2 var9 var0))))
(assert (forall ((var0 Heap) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr)) (or (not (and (inv_main37 var1 var8 var12 var11 var13 var6 var7) (and (= var10 nullAddr) (and (and (and (and (and (and (= var0 (write var1 var13 (O_node (node (expected_list (getnode (read var1 var13))) (value (getnode (read var1 var13))) var6)))) (= var2 var8)) (= var3 var12)) (= var5 var11)) (= var4 var13)) (= var9 var6)) (= var10 var7))))) (inv_main32 var0 var2 var3 var5 var10))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Heap) (var7 Heap) (var8 Addr) (var9 Addr)) (or (not (and (inv_main6 var4 var3) (and (and (and (= var2 nullAddr) (and (and (and (= var7 var6) (= var2 var8)) (= var9 var5)) (= var1 nullAddr))) (and (and (= var6 var4) (= var8 var3)) (= var5 nullAddr))) (= var0 0)))) (inv_main32 var7 var2 var9 var1 var2))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Heap) (var4 Int) (var5 Int) (var6 Int)) (not (and (inv_main17 var3 var2 var1 var6 var5 var4 var0) (not (is-O_node (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Heap) (var4 Int) (var5 Int) (var6 Int)) (not (and (inv_main18 var3 var2 var1 var6 var5 var4 var0) (not (is-O_node (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Heap) (var4 Int) (var5 Int) (var6 Int)) (not (and (inv_main19 var3 var2 var1 var6 var5 var4 var0) (not (is-O_node (read var3 var0)))))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Heap) (var4 Int) (var5 Int) (var6 Addr)) (not (and (inv_main24 var3 var2 var1 var5 var4 var0 var6) (not (is-O_node (read var3 var6)))))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Heap) (var4 Int) (var5 Int) (var6 Addr)) (not (and (inv_main25 var3 var2 var1 var5 var4 var0 var6) (not (is-O_node (read var3 var6)))))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Heap) (var4 Int) (var5 Int) (var6 Addr)) (not (and (inv_main26 var3 var2 var1 var5 var4 var0 var6) (not (is-O_node (read var3 var6)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Addr)) (not (and (inv_main33 var1 var0 var3 var2 var4) (not (is-O_node (read var1 var4)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr)) (not (and (inv_main36 var2 var1 var4 var3 var5 var0) (not (is-O_node (read var2 var5)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr)) (not (and (inv_main37 var3 var2 var5 var4 var6 var0 var1) (not (is-O_node (read var3 var6)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Addr)) (not (and (inv_main41 var1 var0 var3 var2 var4) (not (is-O_node (read var1 var3)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Addr)) (not (inv_main43 var1 var0 var3 var2 var4))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Addr)) (not (and (inv_main42 var1 var0 var3 var2 var4) (not (is-O_node (read var1 var3)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Addr)) (not (and (inv_main47 var1 var0 var3 var2 var4) (not (is-O_node (read var1 var2)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Addr)) (not (inv_main49 var1 var0 var3 var2 var4))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Addr)) (not (and (inv_main48 var1 var0 var3 var2 var4) (not (is-O_node (read var1 var2)))))))
(check-sat)
