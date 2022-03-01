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
(declare-fun inv_main11 (Heap Int Int Addr) Bool)
(declare-fun inv_main15 (Heap Int Int Addr Addr) Bool)
(declare-fun inv_main18 (Heap Int Int Addr Addr Int) Bool)
(declare-fun inv_main3 (Heap Int) Bool)
(declare-fun inv_main33 (Heap Int Addr Addr Int) Bool)
(declare-fun inv_main39 (Heap Int Addr Addr) Bool)
(declare-fun inv_main42 (Heap Int Addr) Bool)
(assert (forall ((var0 Heap)) (or (not (= var0 emptyHeap)) (inv_main3 var0 2))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap) (var5 Addr) (var6 Int) (var7 Addr) (var8 Addr) (var9 Int) (var10 Heap)) (or (not (and (inv_main33 var10 var9 var8 var7 var6) (and (not (= var5 nullAddr)) (and (is-O_node (read var10 var7)) (and (and (and (and (and (= var4 var10) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var0 var6)) (= var5 (next (getnode (read var10 var7))))))))) (inv_main33 var4 var3 var2 var5 (+ var0 1)))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Heap)) (or (not (and (inv_main11 var3 var2 var1 var0) (and (not (= var0 nullAddr)) (not (<= 0 (+ var1 (- 1))))))) (inv_main33 var3 var2 var0 var0 1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Int) (var8 Int) (var9 Heap)) (or (not (and (inv_main15 var9 var8 var7 var6 var5) (and (is-O_node (read var9 var5)) (and (and (and (and (= var4 (write var9 var5 (O_node (node var6)))) (= var3 var8)) (= var2 var7)) (= var1 var6)) (= var0 var5))))) (inv_main11 var4 var3 (+ var2 (- 1)) var0))))
(assert (forall ((var0 Int) (var1 Heap)) (or (not (and (inv_main3 var1 var0) (not (<= 0 (+ (+ 32 (* (- 1) var0)) (- 1)))))) (inv_main11 var1 var0 var0 nullAddr))))
(assert (forall ((var0 Int) (var1 Int) (var2 Heap)) (or (not (and (inv_main3 var2 var1) (and (= var0 0) (<= 0 (+ (+ 32 (* (- 1) var1)) (- 1)))))) (inv_main11 var2 var1 var1 nullAddr))))
(assert (forall ((var0 Int) (var1 Int) (var2 Heap)) (or (not (and (inv_main3 var2 var1) (and (not (= var0 0)) (<= 0 (+ (+ 32 (* (- 1) var1)) (- 1)))))) (inv_main3 var2 (+ var1 1)))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Heap)) (or (not (inv_main18 var5 var4 var3 var2 var1 var0)) (inv_main18 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 node) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Int) (var8 Int) (var9 Heap)) (or (not (and (inv_main11 var9 var8 var7 var6) (and (and (= nullAddr var5) (and (and (and (and (= var4 (newHeap (alloc var9 (O_node var3)))) (= var2 var8)) (= var1 var7)) (= var0 var6)) (= var5 (newAddr (alloc var9 (O_node var3)))))) (<= 0 (+ var7 (- 1)))))) (inv_main18 var4 var2 var1 var0 var5 1))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 node) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Int) (var8 Int) (var9 Heap)) (or (not (and (inv_main11 var9 var8 var7 var6) (and (and (not (= nullAddr var5)) (and (and (and (and (= var4 (newHeap (alloc var9 (O_node var3)))) (= var2 var8)) (= var1 var7)) (= var0 var6)) (= var5 (newAddr (alloc var9 (O_node var3)))))) (<= 0 (+ var7 (- 1)))))) (inv_main15 var4 var2 var1 var0 var5))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Int) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Int) (var13 Heap)) (or (not (and (inv_main39 var13 var12 var11 var10) (and (not (= var9 nullAddr)) (and (and (is-O_node (read var13 var10)) (and (and (and (and (= var8 var13) (= var7 var12)) (= var6 var11)) (= var5 var10)) (= var4 (next (getnode (read var13 var10)))))) (and (and (and (and (= var3 (write var8 var5 defObj)) (= var2 var7)) (= var1 var6)) (= var0 var5)) (= var9 var4)))))) (inv_main39 var3 var2 var1 var9))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Int) (var4 Int) (var5 Addr) (var6 Int) (var7 Addr) (var8 Addr) (var9 Int) (var10 Heap)) (or (not (and (inv_main33 var10 var9 var8 var7 var6) (and (not (= var5 nullAddr)) (and (= var4 var3) (and (= var2 nullAddr) (and (is-O_node (read var10 var7)) (and (and (and (and (and (= var1 var10) (= var4 var9)) (= var5 var8)) (= var0 var7)) (= var3 var6)) (= var2 (next (getnode (read var10 var7))))))))))) (inv_main39 var1 var4 var5 var5))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Heap)) (or (not (and (inv_main11 var3 var2 var1 var0) (and (not (= var0 nullAddr)) (and (and (= var2 0) (= var0 nullAddr)) (not (<= 0 (+ var1 (- 1)))))))) (inv_main39 var3 var2 var0 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Int) (var5 Int) (var6 Int) (var7 Addr) (var8 Addr) (var9 Int) (var10 Heap)) (or (not (and (inv_main33 var10 var9 var8 var7 var6) (and (not (= var5 var4)) (and (= var3 nullAddr) (and (is-O_node (read var10 var7)) (and (and (and (and (and (= var2 var10) (= var5 var9)) (= var1 var8)) (= var0 var7)) (= var4 var6)) (= var3 (next (getnode (read var10 var7)))))))))) (inv_main42 var2 var5 var1))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Heap)) (or (not (and (inv_main11 var3 var2 var1 var0) (and (and (not (= var2 0)) (= var0 nullAddr)) (not (<= 0 (+ var1 (- 1))))))) (inv_main42 var3 var2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Heap)) (not (and (inv_main15 var4 var3 var2 var1 var0) (not (is-O_node (read var4 var0)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap)) (not (and (inv_main33 var4 var3 var2 var1 var0) (not (is-O_node (read var4 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap)) (not (and (inv_main39 var3 var2 var1 var0) (not (is-O_node (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Heap)) (not (inv_main42 var2 var1 var0))))
(check-sat)
