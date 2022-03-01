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
                   (((O_Int (getInt Int)) (O_UInt (getUInt Int)) (O_Addr (getAddr Addr)) (O_node (getnode node)) (defObj))
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
(declare-fun inv_main11 (Heap Addr Int) Bool)
(declare-fun inv_main18 (Heap Addr) Bool)
(declare-fun inv_main2 (Heap) Bool)
(declare-fun inv_main20 (Heap Addr Addr) Bool)
(declare-fun inv_main27 (Heap Addr Addr Int) Bool)
(declare-fun inv_main34 (Heap Addr node) Bool)
(assert (inv_main2 emptyHeap))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap)) (or (not (inv_main11 var2 var1 var0)) (inv_main11 var2 var1 var0))))
(assert (forall ((var0 node) (var1 Heap) (var2 Addr) (var3 Heap)) (or (not (and (inv_main2 var3) (and (= nullAddr var2) (and (= var1 (newHeap (alloc var3 (O_node var0)))) (= var2 (newAddr (alloc var3 (O_node var0)))))))) (inv_main11 var1 var2 1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (and (inv_main20 var2 var1 var0) (is-O_node (read var2 var1)))) (inv_main18 (write var2 var1 (O_node (node var0))) var1))))
(assert (forall ((var0 node) (var1 Addr) (var2 Addr) (var3 node) (var4 Heap) (var5 Heap) (var6 Addr) (var7 Heap)) (or (not (and (inv_main2 var7) (and (and (not (= nullAddr var6)) (and (and (= var5 (newHeap (alloc var4 (O_node var3)))) (= var2 var1)) (= var6 (newAddr (alloc var4 (O_node var3)))))) (and (not (= nullAddr var1)) (and (= var4 (newHeap (alloc var7 (O_node var0)))) (= var1 (newAddr (alloc var7 (O_node var0))))))))) (inv_main20 var5 var2 var6))))
(assert (forall ((var0 Addr) (var1 Heap)) (or (not (and (inv_main18 var1 var0) (and (is-O_node (read var1 var0)) (is-O_node (read var1 (next (getnode (read var1 var0)))))))) (inv_main34 var1 var0 (getnode (read var1 (next (getnode (read var1 var0)))))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Heap) (var4 node) (var5 Addr) (var6 Heap)) (or (not (and (inv_main34 var6 var5 var4) (and (and (is-O_node (read var6 var5)) (and (= var3 (write var6 var5 (O_node var4))) (= var2 var5))) (and (= var1 (write var3 var2 defObj)) (= var0 var2))))) (inv_main0 var1 0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (inv_main27 var3 var2 var1 var0)) (inv_main27 var3 var2 var1 var0))))
(assert (forall ((var0 node) (var1 Addr) (var2 Addr) (var3 node) (var4 Heap) (var5 Heap) (var6 Addr) (var7 Heap)) (or (not (and (inv_main2 var7) (and (and (= nullAddr var6) (and (and (= var5 (newHeap (alloc var4 (O_node var3)))) (= var2 var1)) (= var6 (newAddr (alloc var4 (O_node var3)))))) (and (not (= nullAddr var1)) (and (= var4 (newHeap (alloc var7 (O_node var0)))) (= var1 (newAddr (alloc var7 (O_node var0))))))))) (inv_main27 var5 var2 var6 1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main20 var2 var1 var0) (not (is-O_node (read var2 var1)))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main18 var1 var0) (not (is-O_node (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main18 var1 var0) (and (is-O_node (read var1 var0)) (not (is-O_node (read var1 (next (getnode (read var1 var0)))))))))))
(assert (forall ((var0 node) (var1 Addr) (var2 Heap)) (not (and (inv_main34 var2 var1 var0) (not (is-O_node (read var2 var1)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Heap)) (not (and (inv_main0 var2 var1) (not (= (read var2 var0) defObj))))))
(check-sat)
