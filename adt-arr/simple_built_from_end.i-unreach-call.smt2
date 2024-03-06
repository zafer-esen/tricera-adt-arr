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
(declare-fun inv_main (Heap Addr Addr) Bool)
(declare-fun inv_main534_3 (Heap Addr Addr) Bool)
(declare-fun inv_main536_17 (Heap Addr Addr Int) Bool)
(declare-fun inv_main542_9_9 (Heap Addr Addr) Bool)
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (and (= var2 emptyHeap) (= var1 nullAddr))) (inv_main534_3 var2 var0 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main534_3 var3 var2 var1) (= var0 0))) (inv_main var3 var2 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main var10 var9 var8) (and (and (and (and (= var7 var6) (= var5 var4)) (= var3 var2)) (= var1 (|node::n| (getnode (read var6 var2))))) (and (and (= var0 1) (and (and (and (= var6 var10) (= var4 var9)) (= var2 var8)) (= var0 (|node::h| (getnode (read var10 var8)))))) (not (= var8 nullAddr)))))) (inv_main var7 var5 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Int) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main var6 var5 var4) (and (and (not (= var3 1)) (and (and (and (= var2 var6) (= var1 var5)) (= var0 var4)) (= var3 (|node::h| (getnode (read var6 var4)))))) (not (= var4 nullAddr))))) (inv_main542_9_9 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (inv_main536_17 var3 var2 var1 var0)) (inv_main536_17 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 node) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main534_3 var9 var8 var7) (and (and (= var6 nullAddr) (and (and (and (and (= var5 (newHeap (alloc var9 (O_node var4)))) (= var3 var8)) (= var2 var7)) (= var6 (newAddr (alloc var9 (O_node var4))))) (not (= var1 0)))) (= var0 1)))) (inv_main536_17 var5 var6 var2 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 node) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap) (var11 Heap) (var12 Addr) (var13 Addr) (var14 Heap)) (or (not (and (inv_main534_3 var14 var13 var12) (and (and (and (and (= var11 (write var10 var9 (O_node (node 1 (|node::n| (getnode (read var10 var9))))))) (= var8 var9)) (= var7 var6)) (and (and (= var5 (write var11 var8 (O_node (node (|node::h| (getnode (read var11 var8))) var7)))) (= var4 var8)) (= var3 var7))) (and (not (= var9 nullAddr)) (and (and (and (and (= var10 (newHeap (alloc var14 (O_node var2)))) (= var1 var13)) (= var6 var12)) (= var9 (newAddr (alloc var14 (O_node var2))))) (not (= var0 0))))))) (inv_main534_3 var5 var4 var4))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (inv_main542_9_9 var2 var1 var0))))
(check-sat)
