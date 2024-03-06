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
(declare-datatypes ((AddrRange 0))
                   (((AddrRange (AddrRangeStart Addr) (AddrRangeSize Int)))))

(declare-datatypes ((HeapObject 0) (node 0))
                   (((O_Int (getInt Int)) (O_UInt (getUInt Int)) (O_Addr (getAddr Addr)) (O_AddrRange (getAddrRange AddrRange)) (O_node (getnode node)) (defObj))
                   ((node (|node::h| Int) (|node::n| Addr)))))
(declare-datatypes ((BatchAllocResHeap 0) (AllocResHeap 0) (Heap 0))
                   (((BatchAllocResHeap   (newBatchHeap Heap) (newAddrRange AddrRange)))
                   ((AllocResHeap   (newHeap Heap) (newAddr Addr)))
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
(declare-fun inv_main534_3 (Heap Addr Addr) Bool)
(declare-fun inv_main536_17 (Heap Addr Addr Int) Bool)
(declare-fun inv_main_3 (Heap Addr Addr) Bool)
(declare-fun inv_main_5 (Heap Addr Addr) Bool)
(declare-fun inv_main_7 (Heap Addr Addr) Bool)
(declare-fun inv_main_8 (Heap Addr Addr) Bool)
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (and (= var2 emptyHeap) (= var1 nullAddr))) (inv_main534_3 var2 var0 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (inv_main536_17 var3 var2 var1 var0)) (inv_main536_17 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 node) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main534_3 var9 var8 var7) (and (and (= var6 nullAddr) (and (and (and (and (= var5 (newHeap (alloc var9 (O_node var4)))) (= var3 var8)) (= var2 var7)) (= var6 (newAddr (alloc var9 (O_node var4))))) (not (= var1 0)))) (= var0 1)))) (inv_main536_17 var5 var6 var2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Int) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main_7 var6 var5 var4) (and (and (= var3 1) (is-O_node (read var6 var4))) (and (and (and (= var2 var6) (= var1 var5)) (= var0 var4)) (= var3 (|node::h| (getnode (read var6 var4)))))))) (inv_main_8 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main_8 var6 var5 var4) (and (not (= var3 nullAddr)) (and (is-O_node (read var6 var4)) (and (and (and (= var2 var6) (= var1 var5)) (= var0 var4)) (= var3 (|node::n| (getnode (read var6 var4))))))))) (inv_main_7 var2 var1 var3))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main534_3 var3 var2 var1) (and (not (= var1 nullAddr)) (= var0 0)))) (inv_main_7 var3 var2 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 node) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main534_3 var8 var7 var6) (and (not (= var5 nullAddr)) (and (and (and (and (= var4 (newHeap (alloc var8 (O_node var3)))) (= var2 var7)) (= var1 var6)) (= var5 (newAddr (alloc var8 (O_node var3))))) (not (= var0 0)))))) (inv_main_3 var4 var5 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main_5 var5 var4 var3) (and (and (is-O_node (read var5 var4)) (is-O_node (read var5 var4))) (and (and (= var2 (write var5 var4 (O_node (node (|node::h| (getnode (read var5 var4))) var3)))) (= var1 var4)) (= var0 var3))))) (inv_main534_3 var2 var1 var1))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main_3 var3 var2 var1) (and (and (is-O_node (read var3 var2)) (is-O_node (read var3 var2))) (= var0 (write var3 var2 (O_node (node 1 (|node::n| (getnode (read var3 var2)))))))))) (inv_main_5 var0 var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_3 var2 var1 var0) (not (is-O_node (read var2 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_3 var2 var1 var0) (and (is-O_node (read var2 var1)) (not (is-O_node (read var2 var1))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_5 var2 var1 var0) (not (is-O_node (read var2 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_5 var2 var1 var0) (and (is-O_node (read var2 var1)) (not (is-O_node (read var2 var1))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_7 var2 var1 var0) (not (is-O_node (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_8 var2 var1 var0) (not (is-O_node (read var2 var0)))))))
(check-sat)
