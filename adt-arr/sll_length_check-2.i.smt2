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
(declare-fun inv_main11 (Heap Int Int Addr) Bool)
(declare-fun inv_main15 (Heap Int Int Addr Addr) Bool)
(declare-fun inv_main18 (Heap Int Int Addr Addr Int) Bool)
(declare-fun inv_main3 (Heap Int) Bool)
(declare-fun inv_main33 (Heap Int Addr Addr Int) Bool)
(declare-fun inv_main39 (Heap Int Addr Addr) Bool)
(declare-fun inv_main42 (Heap Int Addr) Bool)
(assert (forall ((var0 Heap)) (or (not (= var0 emptyHeap)) (inv_main3 var0 2))))
(assert (forall ((var0 Int) (var1 Heap) (var2 Int) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Heap)) (or (not (and (inv_main39 var3 var0 var12 var8) (and (not (= var6 nullAddr)) (and (and (and (and (and (= var13 var3) (= var4 var0)) (= var10 var12)) (= var7 var8)) (= var11 (next (getnode (read var3 var8))))) (and (and (and (and (= var1 (write var13 var7 defObj)) (= var2 var4)) (= var9 var10)) (= var5 var7)) (= var6 var11)))))) (inv_main39 var1 var2 var9 var6))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Int) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Int) (var10 Addr)) (or (not (and (inv_main33 var4 var1 var10 var8 var5) (and (not (= var2 nullAddr)) (and (= var0 var9) (and (= var6 nullAddr) (and (and (and (and (and (= var7 var4) (= var0 var1)) (= var2 var10)) (= var3 var8)) (= var9 var5)) (= var6 (next (getnode (read var4 var8)))))))))) (inv_main39 var7 var0 var2 var2))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Heap)) (or (not (and (inv_main11 var3 var0 var2 var1) (and (not (= var1 nullAddr)) (and (and (= var0 0) (= var1 nullAddr)) (not (<= 0 (+ var2 (- 1)))))))) (inv_main39 var3 var0 var1 var1))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Int) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Int) (var10 Addr)) (or (not (and (inv_main33 var4 var1 var10 var8 var5) (and (not (= var0 var9)) (and (= var6 nullAddr) (and (and (and (and (and (= var7 var4) (= var0 var1)) (= var2 var10)) (= var3 var8)) (= var9 var5)) (= var6 (next (getnode (read var4 var8))))))))) (inv_main42 var7 var0 var2))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Heap)) (or (not (and (inv_main11 var3 var0 var2 var1) (and (and (not (= var0 0)) (= var1 nullAddr)) (not (<= 0 (+ var2 (- 1))))))) (inv_main42 var3 var0 var1))))
(assert (forall ((var0 Int) (var1 Int) (var2 Heap)) (or (not (and (inv_main3 var2 var0) (and (not (= var1 0)) (<= 0 (+ (+ 32 (* (- 1) var0)) (- 1)))))) (inv_main3 var2 (+ var0 1)))))
(assert (forall ((var0 node) (var1 Int) (var2 Addr) (var3 Int) (var4 Heap) (var5 Int) (var6 Addr) (var7 Int) (var8 Addr) (var9 Heap)) (or (not (and (inv_main11 var4 var1 var3 var2) (and (and (not (= nullAddr var6)) (and (and (and (and (= var9 (newHeap (alloc var4 (O_node var0)))) (= var7 var1)) (= var5 var3)) (= var8 var2)) (= var6 (newAddr (alloc var4 (O_node var0)))))) (<= 0 (+ var3 (- 1)))))) (inv_main15 var9 var7 var5 var8 var6))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Int) (var6 Addr) (var7 Int) (var8 Addr) (var9 Heap) (var10 Addr)) (or (not (and (inv_main33 var4 var1 var10 var8 var5) (and (not (= var6 nullAddr)) (and (and (and (and (and (= var9 var4) (= var0 var1)) (= var2 var10)) (= var3 var8)) (= var7 var5)) (= var6 (next (getnode (read var4 var8)))))))) (inv_main33 var9 var0 var2 var6 (+ var7 1)))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Heap)) (or (not (and (inv_main11 var3 var0 var2 var1) (and (not (= var1 nullAddr)) (not (<= 0 (+ var2 (- 1))))))) (inv_main33 var3 var0 var1 var1 1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap) (var5 Heap) (var6 Addr) (var7 Int) (var8 Addr) (var9 Int)) (or (not (and (inv_main15 var4 var0 var3 var1 var8) (and (and (and (and (= var5 (write var4 var8 (O_node (node var1)))) (= var7 var0)) (= var9 var3)) (= var6 var1)) (= var2 var8)))) (inv_main11 var5 var7 (+ var9 (- 1)) var2))))
(assert (forall ((var0 Int) (var1 Heap)) (or (not (and (inv_main3 var1 var0) (not (<= 0 (+ (+ 32 (* (- 1) var0)) (- 1)))))) (inv_main11 var1 var0 var0 nullAddr))))
(assert (forall ((var0 Int) (var1 Int) (var2 Heap)) (or (not (and (inv_main3 var2 var0) (and (= var1 0) (<= 0 (+ (+ 32 (* (- 1) var0)) (- 1)))))) (inv_main11 var2 var0 var0 nullAddr))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Heap) (var4 Addr) (var5 Int)) (or (not (inv_main18 var3 var0 var2 var1 var4 var5)) (inv_main18 var3 var0 var2 var1 var4 var5))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 node) (var4 Int) (var5 Heap) (var6 Heap) (var7 Int) (var8 Addr) (var9 Int)) (or (not (and (inv_main11 var5 var0 var4 var2) (and (and (= nullAddr var1) (and (and (and (and (= var6 (newHeap (alloc var5 (O_node var3)))) (= var7 var0)) (= var9 var4)) (= var8 var2)) (= var1 (newAddr (alloc var5 (O_node var3)))))) (<= 0 (+ var4 (- 1)))))) (inv_main18 var6 var7 var9 var8 var1 1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Heap) (var4 Addr)) (not (and (inv_main15 var3 var0 var2 var1 var4) (not (is-O_node (read var3 var4)))))))
(assert (forall ((var0 Int) (var1 Heap) (var2 Int) (var3 Addr) (var4 Addr)) (not (and (inv_main33 var1 var0 var4 var3 var2) (not (is-O_node (read var1 var3)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Addr)) (not (and (inv_main39 var2 var0 var3 var1) (not (is-O_node (read var2 var1)))))))
(assert (forall ((var0 Int) (var1 Heap) (var2 Addr)) (not (inv_main42 var1 var0 var2))))
(check-sat)
