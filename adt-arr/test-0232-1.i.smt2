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
                   (((O_Int (getInt Int)) (O_UInt (getUInt Int)) (O_Addr (getAddr Addr)) (O_item (getitem item)) (defObj))
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
(declare-fun inv_main15 (Heap Addr) Bool)
(declare-fun inv_main16 (Heap Addr) Bool)
(declare-fun inv_main2 (Heap) Bool)
(declare-fun inv_main22 (Heap Addr) Bool)
(declare-fun inv_main9 (Heap Addr Int Addr) Bool)
(assert (inv_main2 emptyHeap))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Heap)) (or (not (and (inv_main9 var3 var2 var1 var0) (is-O_item (read var3 var0)))) (inv_main10 (write var3 var0 (O_item (item var2 (data (getitem (read var3 var0)))))) var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Int) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Int) (var8 Addr) (var9 Heap)) (or (not (and (inv_main12 var9 var8 var7 var6 var5) (and (not (= var4 nullAddr)) (and (= var3 0) (and (is-O_item (read var9 var6)) (and (and (and (= var2 (write var9 var6 (O_item (item (next (getitem (read var9 var6))) var5)))) (= var1 var8)) (= var0 var7)) (= var4 var6))))))) (inv_main16 var2 var4))))
(assert (forall ((var0 item) (var1 Addr) (var2 Heap) (var3 Heap)) (or (not (and (inv_main2 var3) (and (= var2 var3) (= var1 nullAddr)))) (inv_main9 (newHeap (alloc var2 (O_item var0))) var1 1 (newAddr (alloc var2 (O_item var0)))))))
(assert (forall ((var0 item) (var1 Addr) (var2 Int) (var3 Addr) (var4 Heap) (var5 Int) (var6 Addr) (var7 Addr) (var8 Int) (var9 Addr) (var10 Heap)) (or (not (and (inv_main12 var10 var9 var8 var7 var6) (and (not (= var5 0)) (and (is-O_item (read var10 var7)) (and (and (and (= var4 (write var10 var7 (O_item (item (next (getitem (read var10 var7))) var6)))) (= var3 var9)) (= var2 var8)) (= var1 var7)))))) (inv_main9 (newHeap (alloc var4 (O_item var0))) var1 1 (newAddr (alloc var4 (O_item var0)))))))
(assert (forall ((var0 Addr) (var1 Heap)) (or (not (and (inv_main15 var1 var0) (not (= var0 nullAddr)))) (inv_main22 var1 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Heap)) (or (not (and (inv_main10 var3 var2 var1 var0) (and (and (and (is-O_item (read var3 var0)) (not (= (next (getitem (read var3 var0))) nullAddr))) (is-O_item (read var3 var0))) (is-O_item (read var3 (next (getitem (read var3 var0)))))))) (inv_main12 var3 var2 var1 var0 (data (getitem (read var3 (next (getitem (read var3 var0))))))))))
(assert (forall ((var0 item) (var1 Addr) (var2 Int) (var3 Addr) (var4 Heap)) (or (not (and (inv_main10 var4 var3 var2 var1) (and (is-O_item (read var4 var1)) (= (next (getitem (read var4 var1))) nullAddr)))) (inv_main12 (newHeap (alloc var4 (O_item var0))) var3 var2 var1 (newAddr (alloc var4 (O_item var0)))))))
(assert (forall ((var0 Addr) (var1 Heap)) (or (not (and (inv_main15 var1 var0) (= var0 nullAddr))) (inv_main0 var1 0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Heap)) (or (not (and (inv_main16 var7 var6) (and (and (is-O_item (read var7 var6)) (and (and (= var5 var7) (= var4 var6)) (= var3 (next (getitem (read var7 var6)))))) (and (and (= var2 (write var5 var4 defObj)) (= var1 var4)) (= var0 var3))))) (inv_main15 var2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Heap)) (or (not (and (inv_main22 var7 var6) (and (and (is-O_item (read var7 var6)) (and (and (= var5 var7) (= var4 var6)) (= var3 (next (getitem (read var7 var6)))))) (and (and (= var2 (write var5 var4 defObj)) (= var1 var4)) (= var0 var3))))) (inv_main15 var2 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Int) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Int) (var8 Addr) (var9 Heap)) (or (not (and (inv_main12 var9 var8 var7 var6 var5) (and (= var4 nullAddr) (and (= var3 0) (and (is-O_item (read var9 var6)) (and (and (and (= var2 (write var9 var6 (O_item (item (next (getitem (read var9 var6))) var5)))) (= var1 var8)) (= var0 var7)) (= var4 var6))))))) (inv_main15 var2 var4))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Heap)) (not (and (inv_main9 var3 var2 var1 var0) (not (is-O_item (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Heap)) (not (and (inv_main10 var3 var2 var1 var0) (not (is-O_item (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Heap)) (not (and (inv_main10 var3 var2 var1 var0) (and (and (is-O_item (read var3 var0)) (not (= (next (getitem (read var3 var0))) nullAddr))) (not (is-O_item (read var3 var0))))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Heap)) (not (and (inv_main10 var3 var2 var1 var0) (and (and (and (is-O_item (read var3 var0)) (not (= (next (getitem (read var3 var0))) nullAddr))) (is-O_item (read var3 var0))) (not (is-O_item (read var3 (next (getitem (read var3 var0)))))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Heap)) (not (and (inv_main12 var4 var3 var2 var1 var0) (not (is-O_item (read var4 var1)))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main16 var1 var0) (not (is-O_item (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main22 var1 var0) (not (is-O_item (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Heap)) (not (and (inv_main0 var2 var1) (not (= (read var2 var0) defObj))))))
(check-sat)
