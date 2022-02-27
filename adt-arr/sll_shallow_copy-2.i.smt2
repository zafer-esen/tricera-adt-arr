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
(declare-datatypes ((HeapObject 0) (node 0))
                   (((O_Int (getInt Int)) (O_Addr (getAddr Addr)) (O_node (getnode node)) (defObj))
                   ((node (next Addr)))))
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
(declare-fun inv_main0 (Heap Int) Bool)
(declare-fun inv_main10 (Heap Addr Int) Bool)
(declare-fun inv_main14 (Heap Addr) Bool)
(declare-fun inv_main16 (Heap Addr Addr) Bool)
(declare-fun inv_main2 (Heap) Bool)
(declare-fun inv_main22 (Heap Addr Addr Int) Bool)
(declare-fun inv_main26 (Heap Addr node) Bool)
(assert (inv_main2 emptyHeap))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap)) (or (not (inv_main10 var2 var1 var0)) (inv_main10 var2 var1 var0))))
(assert (forall ((var0 Heap) (var1 node) (var2 Addr) (var3 Heap)) (or (not (and (inv_main2 var3) (and (= nullAddr var2) (and (= var0 (newHeap (alloc var3 (O_node var1)))) (= var2 (newAddr (alloc var3 (O_node var1)))))))) (inv_main10 var0 var2 1))))
(assert (forall ((var0 Heap) (var1 Addr)) (or (not (inv_main14 var0 var1)) (inv_main26 var0 var1 (getnode (read var0 (next (getnode (read var0 var1)))))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr)) (or (not (inv_main16 var0 var2 var1)) (inv_main14 (write var0 var2 (O_node (node var1))) var2))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Addr)) (or (not (inv_main22 var2 var3 var1 var0)) (inv_main22 var2 var3 var1 var0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 node) (var4 Addr) (var5 Heap) (var6 node) (var7 Heap)) (or (not (and (inv_main2 var7) (and (and (= nullAddr var0) (and (and (= var1 (newHeap (alloc var5 (O_node var6)))) (= var4 var2)) (= var0 (newAddr (alloc var5 (O_node var6)))))) (and (not (= nullAddr var2)) (and (= var5 (newHeap (alloc var7 (O_node var3)))) (= var2 (newAddr (alloc var7 (O_node var3))))))))) (inv_main22 var1 var4 var0 1))))
(assert (forall ((var0 node) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Heap)) (or (not (and (inv_main26 var2 var3 var0) (and (and (= var5 (write var2 var3 (O_node var0))) (= var1 var3)) (and (= var6 (write var5 var1 defObj)) (= var4 var1))))) (inv_main0 var6 0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Heap) (var4 node) (var5 Addr) (var6 Heap) (var7 node)) (or (not (and (inv_main2 var1) (and (and (not (= nullAddr var5)) (and (and (= var3 (newHeap (alloc var6 (O_node var7)))) (= var0 var2)) (= var5 (newAddr (alloc var6 (O_node var7)))))) (and (not (= nullAddr var2)) (and (= var6 (newHeap (alloc var1 (O_node var4)))) (= var2 (newAddr (alloc var1 (O_node var4))))))))) (inv_main16 var3 var0 var5))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr)) (not (and (inv_main16 var0 var2 var1) (not (is-O_node (read var0 var2)))))))
(assert (forall ((var0 Heap) (var1 Addr)) (not (and (inv_main14 var0 var1) (not (is-O_node (read var0 var1)))))))
(assert (forall ((var0 Heap) (var1 Addr)) (not (and (inv_main14 var0 var1) (not (is-O_node (read var0 (next (getnode (read var0 var1))))))))))
(assert (forall ((var0 node) (var1 Heap) (var2 Addr)) (not (and (inv_main26 var1 var2 var0) (not (is-O_node (read var1 var2)))))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Addr)) (not (and (inv_main0 var0 var1) (not (= (read var0 var2) defObj))))))
(check-sat)
