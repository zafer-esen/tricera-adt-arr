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
(declare-datatypes ((HeapObject 0) (item 0))
                   (((O_Int (getInt Int)) (O_Addr (getAddr Addr)) (O_item (getitem item)) (defObj))
                   ((item (next Addr) (data Addr)))))
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
(declare-fun inv_main10 (Heap Addr Int Addr) Bool)
(declare-fun inv_main12 (Heap Addr Int Addr Addr) Bool)
(declare-fun inv_main14 (Heap Addr) Bool)
(declare-fun inv_main15 (Heap Addr) Bool)
(declare-fun inv_main2 (Heap) Bool)
(declare-fun inv_main20 (Heap Addr) Bool)
(declare-fun inv_main9 (Heap Addr Int Addr) Bool)
(assert (inv_main2 emptyHeap))
(assert (forall ((var0 Addr) (var1 Heap)) (or (not (and (inv_main14 var1 var0) (= var0 nullAddr))) (inv_main0 var1 0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main10 var3 var1 var0 var2) (not (= (next (getitem (read var3 var2))) nullAddr)))) (inv_main12 var3 var1 var0 var2 (data (getitem (read var3 (next (getitem (read var3 var2))))))))))
(assert (forall ((var0 Int) (var1 item) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main10 var4 var2 var0 var3) (= (next (getitem (read var4 var3))) nullAddr))) (inv_main12 (newHeap (alloc var4 (O_item var1))) var2 var0 var3 (newAddr (alloc var4 (O_item var1)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main12 var9 var5 var2 var7 var1) (and (not (= var4 nullAddr)) (and (= var0 0) (and (and (and (= var6 (write var9 var7 (O_item (item (next (getitem (read var9 var7))) var1)))) (= var8 var5)) (= var3 var2)) (= var4 var7)))))) (inv_main15 var6 var4))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Heap) (var7 Heap)) (or (not (and (inv_main15 var7 var2) (and (and (and (= var6 var7) (= var1 var2)) (= var4 (next (getitem (read var7 var2))))) (and (and (= var5 (write var6 var1 defObj)) (= var3 var1)) (= var0 var4))))) (inv_main14 var5 var0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Heap)) (or (not (and (inv_main20 var7 var4) (and (and (and (= var6 var7) (= var0 var4)) (= var5 (next (getitem (read var7 var4))))) (and (and (= var1 (write var6 var0 defObj)) (= var3 var0)) (= var2 var5))))) (inv_main14 var1 var2))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main12 var9 var5 var2 var7 var1) (and (= var4 nullAddr) (and (= var0 0) (and (and (and (= var6 (write var9 var7 (O_item (item (next (getitem (read var9 var7))) var1)))) (= var8 var5)) (= var3 var2)) (= var4 var7)))))) (inv_main14 var6 var4))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (inv_main9 var3 var1 var0 var2)) (inv_main10 (write var3 var2 (O_item (item var1 (data (getitem (read var3 var2)))))) var1 var0 var2))))
(assert (forall ((var0 Addr) (var1 Heap)) (or (not (and (inv_main14 var1 var0) (not (= var0 nullAddr)))) (inv_main20 var1 var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 item) (var3 Heap)) (or (not (and (inv_main2 var3) (and (= var0 var3) (= var1 nullAddr)))) (inv_main9 (newHeap (alloc var0 (O_item var2))) var1 1 (newAddr (alloc var0 (O_item var2)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Int) (var4 Addr) (var5 item) (var6 Heap) (var7 Int) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main12 var10 var4 var1 var8 var0) (and (not (= var7 0)) (and (and (and (= var6 (write var10 var8 (O_item (item (next (getitem (read var10 var8))) var0)))) (= var9 var4)) (= var3 var1)) (= var2 var8))))) (inv_main9 (newHeap (alloc var6 (O_item var5))) var2 1 (newAddr (alloc var6 (O_item var5)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main9 var3 var1 var0 var2) (not (is-O_item (read var3 var2)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main10 var3 var1 var0 var2) (not (is-O_item (read var3 var2)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main10 var3 var1 var0 var2) (and (not (= (next (getitem (read var3 var2))) nullAddr)) (not (is-O_item (read var3 var2))))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main10 var3 var1 var0 var2) (and (not (= (next (getitem (read var3 var2))) nullAddr)) (not (is-O_item (read var3 (next (getitem (read var3 var2)))))))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main12 var4 var2 var1 var3 var0) (not (is-O_item (read var4 var3)))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main15 var1 var0) (not (is-O_item (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main20 var1 var0) (not (is-O_item (read var1 var0)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap)) (not (and (inv_main0 var2 var0) (not (= (read var2 var1) defObj))))))
(check-sat)
