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
                   ((node (left Addr) (right Addr) (parent Addr) (value Int)))))
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
(declare-fun inv_main13 (Heap Addr Addr) Bool)
(declare-fun inv_main16 (Heap Addr Addr) Bool)
(declare-fun inv_main19 (Heap Addr Addr) Bool)
(declare-fun inv_main2 (Heap) Bool)
(declare-fun inv_main22 (Heap Addr Addr Int) Bool)
(declare-fun inv_main24 (Heap Addr Addr) Bool)
(declare-fun inv_main25 (Heap Addr Addr) Bool)
(declare-fun inv_main30 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main31 (Heap Addr Addr) Bool)
(declare-fun inv_main34 (Heap Addr Addr) Bool)
(declare-fun inv_main35 (Heap Addr Addr) Bool)
(declare-fun inv_main36 (Heap Addr Addr) Bool)
(declare-fun inv_main37 (Heap Addr Addr) Bool)
(declare-fun inv_main51 (Heap Addr Addr) Bool)
(declare-fun inv_main55 (Heap Addr Addr) Bool)
(declare-fun inv_main56 (Heap Addr Addr) Bool)
(declare-fun inv_main57 (Heap Addr Addr) Bool)
(declare-fun inv_main63 (Heap Addr Addr) Bool)
(declare-fun inv_main67 (Heap Addr Addr) Bool)
(declare-fun inv_main7 (Heap Addr Addr) Bool)
(declare-fun inv_main71 (Heap Addr Addr) Bool)
(declare-fun inv_main82 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main83 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main89 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main90 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main91 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main94 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main96 (Heap Addr Addr Addr) Bool)
(assert (inv_main2 emptyHeap))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Heap)) (or (not (and (inv_main30 var6 var3 var2 var0) (and (not (= var1 nullAddr)) (and (and (= var5 (write var6 var2 (O_node (node var0 (right (getnode (read var6 var2))) (parent (getnode (read var6 var2))) (value (getnode (read var6 var2))))))) (= var4 var3)) (= var1 var2))))) (inv_main31 var5 var4 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Addr)) (or (not (and (inv_main82 var6 var4 var2 var8) (and (not (= var1 nullAddr)) (and (and (and (and (= var3 var6) (= var7 var4)) (= var0 var2)) (= var5 var8)) (= var1 (right (getnode (read var6 var2)))))))) (inv_main83 var3 var7 var0 var5))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 node) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main7 var5 var2 var1) (and (not (= var7 nullAddr)) (and (and (and (and (= var8 (newHeap (alloc var5 (O_node var4)))) (= var0 var2)) (= var6 var1)) (= var7 (newAddr (alloc var5 (O_node var4))))) (not (= var3 0)))))) (inv_main13 var8 var0 var7))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (and (inv_main24 var2 var1 var0) (and (= var1 nullAddr) (and (not (= var1 nullAddr)) (= var0 nullAddr))))) (inv_main51 var2 var1 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (inv_main31 var2 var1 var0)) (inv_main34 (write var2 (left (getnode (read var2 var0))) (O_node (node nullAddr (right (getnode (read var2 (left (getnode (read var2 var0)))))) (parent (getnode (read var2 (left (getnode (read var2 var0)))))) (value (getnode (read var2 (left (getnode (read var2 var0))))))))) var1 var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Int) (var6 Heap) (var7 Int)) (or (not (and (inv_main22 var6 var4 var3 var7) (and (and (and (= var0 (write var6 var3 (O_node (node (left (getnode (read var6 var3))) (right (getnode (read var6 var3))) (parent (getnode (read var6 var3))) var7)))) (= var1 var4)) (= var2 var3)) (= var5 var7)))) (inv_main7 var0 var2 var2))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Heap)) (or (not (and (inv_main2 var1) (and (= var2 var1) (= var0 nullAddr)))) (inv_main7 var2 var0 nullAddr))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Heap) (var6 Addr)) (or (not (and (inv_main67 var5 var1 var0) (and (not (= var6 nullAddr)) (and (and (and (= var3 var5) (= var4 var1)) (= var2 var0)) (= var6 (parent (getnode (read var5 var0)))))))) (inv_main55 var3 var4 var6))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (and (inv_main24 var2 var1 var0) (and (and (not (= var1 nullAddr)) (not (= var1 nullAddr))) (and (not (= var1 nullAddr)) (= var0 nullAddr))))) (inv_main55 var2 var1 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr)) (or (not (and (inv_main90 var2 var1 var0 var3) (not (= (right (getnode (read var2 var0))) nullAddr)))) (inv_main94 var2 var1 var0 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Int) (var5 Heap) (var6 Addr)) (or (not (and (inv_main57 var5 var3 var0) (and (not (= var4 42)) (and (and (and (= var2 var5) (= var6 var3)) (= var1 var0)) (= var4 (value (getnode (read var5 (left (getnode (read var5 var0))))))))))) (inv_main63 var2 var6 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr)) (or (not (and (inv_main89 var2 var1 var0 var3) (not (= (left (getnode (read var2 var0))) nullAddr)))) (inv_main91 var2 var1 var0 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr)) (or (not (inv_main91 var2 var1 var0 var3)) (inv_main90 (write var2 (left (getnode (read var2 var0))) defObj) var1 var0 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr)) (or (not (and (inv_main89 var2 var1 var0 var3) (= (left (getnode (read var2 var0))) nullAddr))) (inv_main90 var2 var1 var0 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Addr)) (or (not (and (inv_main96 var7 var2 var0 var8) (and (not (= var3 nullAddr)) (and (and (and (and (= var4 var7) (= var5 var2)) (= var6 var0)) (= var1 var8)) (= var3 (parent (getnode (read var7 var0)))))))) (inv_main89 var4 var5 var3 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Heap) (var7 Addr) (var8 Addr)) (or (not (and (inv_main82 var5 var3 var1 var8) (and (not (= var2 nullAddr)) (and (= var0 nullAddr) (and (and (and (and (= var6 var5) (= var4 var3)) (= var2 var1)) (= var7 var8)) (= var0 (right (getnode (read var5 var1))))))))) (inv_main89 var6 var4 var2 var7))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (and (inv_main55 var2 var1 var0) (= (left (getnode (read var2 var0))) nullAddr))) (inv_main56 var2 var1 var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Int)) (or (not (and (inv_main57 var5 var4 var1) (and (= var6 42) (and (and (and (= var0 var5) (= var2 var4)) (= var3 var1)) (= var6 (value (getnode (read var5 (left (getnode (read var5 var1))))))))))) (inv_main56 var0 var2 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (and (inv_main56 var2 var1 var0) (= (value (getnode (read var2 var0))) 0))) (inv_main71 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (inv_main35 var2 var1 var0)) (inv_main36 (write var2 (left (getnode (read var2 var0))) (O_node (node (left (getnode (read var2 (left (getnode (read var2 var0)))))) (right (getnode (read var2 (left (getnode (read var2 var0)))))) (parent (getnode (read var2 (left (getnode (read var2 var0)))))) 42))) var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (inv_main13 var2 var1 var0)) (inv_main16 (write var2 var0 (O_node (node nullAddr (right (getnode (read var2 var0))) (parent (getnode (read var2 var0))) (value (getnode (read var2 var0)))))) var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr)) (or (not (and (inv_main94 var5 var4 var3 var7) (and (and (and (= var2 (write var5 (right (getnode (read var5 var3))) defObj)) (= var0 var4)) (= var1 var3)) (= var6 var7)))) (inv_main96 var2 var0 var1 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr)) (or (not (and (inv_main90 var2 var1 var0 var3) (= (right (getnode (read var2 var0))) nullAddr))) (inv_main96 var2 var1 var0 var0))))
(assert (forall ((var0 node) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main24 var3 var2 var1) (not (= var1 nullAddr)))) (inv_main30 (newHeap (alloc var3 (O_node var0))) var2 var1 (newAddr (alloc var3 (O_node var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (and (inv_main55 var2 var1 var0) (not (= (left (getnode (read var2 var0))) nullAddr)))) (inv_main57 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main7 var3 var2 var1) (and (not (= var1 nullAddr)) (= var0 0)))) (inv_main25 var3 var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (and (inv_main56 var2 var1 var0) (not (= (value (getnode (read var2 var0))) 0)))) (inv_main67 var2 var1 var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Addr)) (or (not (and (inv_main83 var6 var3 var1 var8) (and (and (and (and (= var0 var6) (= var2 var3)) (= var4 var1)) (= var7 var8)) (= var5 (right (getnode (read var6 var1))))))) (inv_main82 var0 var2 var5 var7))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Heap) (var9 Addr) (var10 Heap)) (or (not (and (inv_main67 var8 var3 var0) (and (and (and (and (= var10 var5) (= var1 var7)) (= var2 var7)) (= var6 nullAddr)) (and (= var9 nullAddr) (and (and (and (= var5 var8) (= var7 var3)) (= var4 var0)) (= var9 (parent (getnode (read var8 var0))))))))) (inv_main82 var10 var1 var2 var6))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr)) (or (not (and (inv_main24 var5 var3 var2) (and (and (and (and (= var0 var5) (= var1 var3)) (= var6 var3)) (= var4 nullAddr)) (and (and (= var3 nullAddr) (not (= var3 nullAddr))) (and (not (= var3 nullAddr)) (= var2 nullAddr)))))) (inv_main82 var0 var1 var6 var4))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (inv_main36 var2 var1 var0)) (inv_main37 (write var2 (left (getnode (read var2 var0))) (O_node (node (left (getnode (read var2 (left (getnode (read var2 var0)))))) (right (getnode (read var2 (left (getnode (read var2 var0)))))) var0 (value (getnode (read var2 (left (getnode (read var2 var0))))))))) var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (inv_main25 var2 var1 var0)) (inv_main24 (write var2 var0 (O_node (node (left (getnode (read var2 var0))) (right (getnode (read var2 var0))) nullAddr (value (getnode (read var2 var0)))))) var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main37 var2 var1 var0) (and (and (and (= var6 var2) (= var4 var1)) (= var5 var0)) (= var3 (right (getnode (read var2 var0))))))) (inv_main24 var6 var4 var3))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main7 var3 var2 var1) (and (= var1 nullAddr) (= var0 0)))) (inv_main24 var3 var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (inv_main34 var2 var1 var0)) (inv_main35 (write var2 (left (getnode (read var2 var0))) (O_node (node (left (getnode (read var2 (left (getnode (read var2 var0)))))) nullAddr (parent (getnode (read var2 (left (getnode (read var2 var0)))))) (value (getnode (read var2 (left (getnode (read var2 var0))))))))) var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Heap)) (or (not (and (inv_main16 var4 var3 var2) (and (not (= var1 nullAddr)) (and (and (= var5 (write var4 var2 (O_node (node (left (getnode (read var4 var2))) var3 (parent (getnode (read var4 var2))) (value (getnode (read var4 var2))))))) (= var1 var3)) (= var0 var2))))) (inv_main19 var5 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main19 var6 var4 var3) (and (and (= var2 (write var6 var4 (O_node (node (left (getnode (read var6 var4))) (right (getnode (read var6 var4))) var3 (value (getnode (read var6 var4))))))) (= var1 var4)) (= var5 var3)))) (inv_main22 var2 var1 var5 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Int)) (or (not (and (inv_main16 var5 var4 var3) (and (= var1 nullAddr) (and (and (= var2 (write var5 var3 (O_node (node (left (getnode (read var5 var3))) var4 (parent (getnode (read var5 var3))) (value (getnode (read var5 var3))))))) (= var1 var4)) (= var0 var3))))) (inv_main22 var2 var1 var0 var6))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main13 var2 var1 var0) (not (is-O_node (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main16 var2 var1 var0) (not (is-O_node (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main19 var2 var1 var0) (not (is-O_node (read var2 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Int)) (not (and (inv_main22 var2 var1 var0 var3) (not (is-O_node (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main25 var2 var1 var0) (not (is-O_node (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main30 var3 var2 var1 var0) (not (is-O_node (read var3 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main31 var2 var1 var0) (not (is-O_node (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main31 var2 var1 var0) (not (is-O_node (read var2 (left (getnode (read var2 var0))))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main34 var2 var1 var0) (not (is-O_node (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main34 var2 var1 var0) (not (is-O_node (read var2 (left (getnode (read var2 var0))))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main35 var2 var1 var0) (not (is-O_node (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main35 var2 var1 var0) (not (is-O_node (read var2 (left (getnode (read var2 var0))))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main36 var2 var1 var0) (not (is-O_node (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main36 var2 var1 var0) (not (is-O_node (read var2 (left (getnode (read var2 var0))))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main37 var2 var1 var0) (not (is-O_node (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (inv_main51 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main55 var2 var1 var0) (not (is-O_node (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main57 var2 var1 var0) (not (is-O_node (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main57 var2 var1 var0) (not (is-O_node (read var2 (left (getnode (read var2 var0))))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (inv_main63 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main56 var2 var1 var0) (not (is-O_node (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (inv_main71 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main67 var2 var1 var0) (not (is-O_node (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr)) (not (and (inv_main82 var2 var1 var0 var3) (not (is-O_node (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr)) (not (and (inv_main83 var2 var1 var0 var3) (not (is-O_node (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr)) (not (and (inv_main89 var2 var1 var0 var3) (not (is-O_node (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr)) (not (and (inv_main91 var2 var1 var0 var3) (not (is-O_node (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr)) (not (and (inv_main90 var2 var1 var0 var3) (not (is-O_node (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr)) (not (and (inv_main94 var2 var1 var0 var3) (not (is-O_node (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr)) (not (and (inv_main96 var2 var1 var0 var3) (not (is-O_node (read var2 var0)))))))
(check-sat)
