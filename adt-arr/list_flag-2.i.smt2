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
                   ((node (h Int) (n Addr)))))
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
(declare-fun inv_main11 (Heap Int Addr Addr Addr Int) Bool)
(declare-fun inv_main14 (Heap Int Addr Addr Addr) Bool)
(declare-fun inv_main15 (Heap Int Addr Addr Addr) Bool)
(declare-fun inv_main19 (Heap Int Addr Addr Addr) Bool)
(declare-fun inv_main2 (Heap) Bool)
(declare-fun inv_main20 (Heap Int Addr Addr Addr) Bool)
(declare-fun inv_main23 (Heap Int Addr Addr Addr) Bool)
(declare-fun inv_main26 (Heap Int Addr Addr Addr Int) Bool)
(declare-fun inv_main29 (Heap Int Addr Addr Addr) Bool)
(declare-fun inv_main33 (Heap Int Addr Addr Addr) Bool)
(declare-fun inv_main34 (Heap Int Addr Addr Addr) Bool)
(declare-fun inv_main35 (Heap Int Addr Addr Addr) Bool)
(declare-fun inv_main36 (Heap Int Addr Addr Addr) Bool)
(declare-fun inv_main39 (Heap Int Addr Addr Addr) Bool)
(declare-fun inv_main42 (Heap Int Addr Addr Addr) Bool)
(assert (inv_main2 emptyHeap))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Int)) (or (not (inv_main23 var1 var4 var3 var0 var2)) (inv_main29 (write var1 var3 (O_node (node (h (getnode (read var1 var3))) var2))) var4 var3 var0 var2))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Int) (var9 Addr) (var10 Int)) (or (not (and (inv_main35 var3 var8 var7 var2 var6) (and (= var4 2) (and (and (and (and (and (= var0 var3) (= var10 var8)) (= var5 var7)) (= var9 var2)) (= var1 var6)) (= var4 (h (getnode (read var3 var7)))))))) (inv_main39 var0 var10 var5 var9 var1))))
(assert (forall ((var0 Int) (var1 node) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Int) (var10 Heap) (var11 Addr) (var12 Int) (var13 Addr) (var14 Heap) (var15 Addr) (var16 Addr)) (or (not (and (inv_main19 var3 var12 var6 var11 var5) (and (and (not (= var13 nullAddr)) (and (and (and (and (and (= var10 (newHeap (alloc var14 (O_node var1)))) (= var0 var9)) (= var2 var7)) (= var16 var4)) (= var8 var15)) (= var13 (newAddr (alloc var14 (O_node var1)))))) (and (and (and (and (= var14 (write var3 var6 (O_node (node 1 (n (getnode (read var3 var6))))))) (= var9 var12)) (= var7 var6)) (= var4 var11)) (= var15 var5))))) (inv_main23 var10 var0 var2 var16 var13))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 node) (var8 Addr) (var9 Int) (var10 Heap) (var11 Addr) (var12 Addr) (var13 Int) (var14 Addr) (var15 Addr) (var16 Int)) (or (not (and (inv_main20 var3 var13 var5 var12 var4) (and (and (not (= var14 nullAddr)) (and (and (and (and (and (= var10 (newHeap (alloc var0 (O_node var7)))) (= var9 var16)) (= var2 var8)) (= var15 var6)) (= var11 var1)) (= var14 (newAddr (alloc var0 (O_node var7)))))) (and (and (and (and (= var0 (write var3 var5 (O_node (node 2 (n (getnode (read var3 var5))))))) (= var16 var13)) (= var8 var5)) (= var6 var12)) (= var1 var4))))) (inv_main23 var10 var9 var2 var15 var14))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Addr) (var4 Addr) (var5 Int)) (or (not (and (inv_main14 var1 var5 var4 var0 var3) (= var2 0))) (inv_main15 var1 var5 var4 var0 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Int) (var9 Int) (var10 Addr)) (or (not (and (inv_main29 var3 var8 var7 var1 var6) (and (and (and (and (and (= var2 var3) (= var9 var8)) (= var5 var7)) (= var4 var1)) (= var0 var6)) (= var10 (n (getnode (read var3 var7))))))) (inv_main14 var2 var9 var10 var4 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 node) (var4 Heap) (var5 Heap) (var6 Addr) (var7 Int) (var8 Int) (var9 Int) (var10 Int) (var11 Int)) (or (not (and (inv_main2 var5) (and (not (= var0 nullAddr)) (and (and (and (and (and (= var4 (newHeap (alloc var5 (O_node var3)))) (= var8 var2)) (= var11 var9)) (= var10 var7)) (= var6 var1)) (= var0 (newAddr (alloc var5 (O_node var3)))))))) (inv_main14 var4 var8 var0 var0 var6))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Int) (var7 Addr) (var8 Addr) (var9 Int) (var10 Addr)) (or (not (and (inv_main39 var4 var9 var8 var3 var7) (and (and (and (and (and (= var2 var4) (= var6 var9)) (= var5 var8)) (= var0 var3)) (= var1 var7)) (= var10 (n (getnode (read var4 var8))))))) (inv_main35 var2 var6 var10 var0 var1))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Int) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Int)) (or (not (and (inv_main15 var1 var4 var3 var0 var2) (and (= var9 0) (and (and (and (and (= var6 (write var1 var3 (O_node (node 3 (n (getnode (read var1 var3))))))) (= var9 var4)) (= var5 var3)) (= var7 var0)) (= var8 var2))))) (inv_main35 var6 var9 var7 var7 var8))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Int) (var8 Addr) (var9 Addr) (var10 Int)) (or (not (and (inv_main34 var3 var7 var6 var1 var5) (and (not (= var2 1)) (and (and (and (and (and (= var4 var3) (= var10 var7)) (= var9 var6)) (= var8 var1)) (= var0 var5)) (= var2 (h (getnode (read var3 var6)))))))) (inv_main33 var4 var10 var9 var8 var0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr) (var7 Int) (var8 Addr) (var9 Int) (var10 Addr)) (or (not (and (inv_main35 var1 var7 var6 var0 var5) (and (not (= var4 2)) (and (and (and (and (and (= var3 var1) (= var9 var7)) (= var8 var6)) (= var10 var0)) (= var2 var5)) (= var4 (h (getnode (read var1 var6)))))))) (inv_main33 var3 var9 var8 var10 var2))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Addr) (var4 Addr) (var5 Int)) (or (not (inv_main11 var1 var5 var4 var0 var3 var2)) (inv_main11 var1 var5 var4 var0 var3 var2))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Int) (var5 Int) (var6 Heap) (var7 Addr) (var8 Int) (var9 Addr) (var10 node) (var11 Int)) (or (not (and (inv_main2 var1) (and (= var7 nullAddr) (and (and (and (and (and (= var6 (newHeap (alloc var1 (O_node var10)))) (= var5 var8)) (= var0 var2)) (= var4 var11)) (= var3 var9)) (= var7 (newAddr (alloc var1 (O_node var10)))))))) (inv_main11 var6 var5 var0 var7 var3 1))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Int) (var9 Addr) (var10 Int)) (or (not (and (inv_main34 var5 var8 var7 var2 var6) (and (= var10 1) (and (and (and (and (and (= var3 var5) (= var1 var8)) (= var4 var7)) (= var9 var2)) (= var0 var6)) (= var10 (h (getnode (read var5 var7)))))))) (inv_main36 var3 var1 var4 var9 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Int) (var8 Int) (var9 Addr) (var10 Addr)) (or (not (and (inv_main36 var2 var7 var6 var0 var5) (and (and (and (and (and (= var4 var2) (= var8 var7)) (= var10 var6)) (= var1 var0)) (= var3 var5)) (= var9 (n (getnode (read var2 var6))))))) (inv_main34 var4 var8 var9 var1 var3))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Int) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Int)) (or (not (and (inv_main15 var1 var4 var3 var0 var2) (and (not (= var9 0)) (and (and (and (and (= var6 (write var1 var3 (O_node (node 3 (n (getnode (read var1 var3))))))) (= var9 var4)) (= var5 var3)) (= var7 var0)) (= var8 var2))))) (inv_main34 var6 var9 var7 var7 var8))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Addr) (var4 Addr) (var5 Int)) (or (not (and (inv_main14 var1 var5 var4 var0 var3) (and (= var5 0) (not (= var2 0))))) (inv_main20 var1 var5 var4 var0 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr) (var7 Int) (var8 Heap) (var9 Addr) (var10 Int)) (or (not (and (inv_main33 var3 var7 var6 var2 var5) (and (not (= var4 3)) (and (and (and (and (and (= var8 var3) (= var10 var7)) (= var1 var6)) (= var0 var2)) (= var9 var5)) (= var4 (h (getnode (read var3 var6)))))))) (inv_main42 var8 var10 var1 var0 var9))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Addr) (var4 Addr) (var5 Int)) (or (not (and (inv_main14 var1 var5 var4 var0 var3) (and (not (= var5 0)) (not (= var2 0))))) (inv_main19 var1 var5 var4 var0 var3))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Int) (var5 Int)) (or (not (inv_main26 var1 var4 var3 var0 var2 var5)) (inv_main26 var1 var4 var3 var0 var2 var5))))
(assert (forall ((var0 Int) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap) (var9 Addr) (var10 Addr) (var11 node) (var12 Addr) (var13 Addr) (var14 Int) (var15 Int) (var16 Heap)) (or (not (and (inv_main19 var1 var14 var3 var10 var2) (and (and (= var7 nullAddr) (and (and (and (and (and (= var8 (newHeap (alloc var16 (O_node var11)))) (= var0 var15)) (= var9 var6)) (= var4 var12)) (= var13 var5)) (= var7 (newAddr (alloc var16 (O_node var11)))))) (and (and (and (and (= var16 (write var1 var3 (O_node (node 1 (n (getnode (read var1 var3))))))) (= var15 var14)) (= var6 var3)) (= var12 var10)) (= var5 var2))))) (inv_main26 var8 var0 var9 var4 var7 1))))
(assert (forall ((var0 node) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Int) (var8 Heap) (var9 Int) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Int) (var14 Addr) (var15 Addr) (var16 Addr)) (or (not (and (inv_main20 var1 var13 var4 var12 var3) (and (and (= var2 nullAddr) (and (and (and (and (and (= var8 (newHeap (alloc var6 (O_node var0)))) (= var7 var9)) (= var10 var15)) (= var11 var5)) (= var16 var14)) (= var2 (newAddr (alloc var6 (O_node var0)))))) (and (and (and (and (= var6 (write var1 var4 (O_node (node 2 (n (getnode (read var1 var4))))))) (= var9 var13)) (= var15 var4)) (= var5 var12)) (= var14 var3))))) (inv_main26 var8 var7 var10 var11 var2 1))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Int)) (not (and (inv_main19 var1 var4 var3 var0 var2) (not (is-O_node (read var1 var3)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Int)) (not (and (inv_main20 var1 var4 var3 var0 var2) (not (is-O_node (read var1 var3)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Int)) (not (and (inv_main23 var1 var4 var3 var0 var2) (not (is-O_node (read var1 var3)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Int)) (not (and (inv_main29 var1 var4 var3 var0 var2) (not (is-O_node (read var1 var3)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Int)) (not (and (inv_main15 var1 var4 var3 var0 var2) (not (is-O_node (read var1 var3)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Int)) (not (and (inv_main34 var1 var4 var3 var0 var2) (not (is-O_node (read var1 var3)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Int)) (not (and (inv_main36 var1 var4 var3 var0 var2) (not (is-O_node (read var1 var3)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Int)) (not (and (inv_main35 var1 var4 var3 var0 var2) (not (is-O_node (read var1 var3)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Int)) (not (and (inv_main39 var1 var4 var3 var0 var2) (not (is-O_node (read var1 var3)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Int)) (not (and (inv_main33 var1 var4 var3 var0 var2) (not (is-O_node (read var1 var3)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Int)) (not (inv_main42 var1 var4 var3 var0 var2))))
(check-sat)
