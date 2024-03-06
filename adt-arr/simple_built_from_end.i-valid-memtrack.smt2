(set-logic HORN)
(set-info :source |
    Benchmark: C_VC
    Output by Princess (http://www.philipp.ruemmer.org/princess.shtml)
|)
(set-info :status unsat)
(declare-datatype bool ((true) (false)))
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
(declare-fun inv_exit (Heap Addr) Bool)
(declare-fun inv_main (Heap Addr Addr Addr) Bool)
(declare-fun inv_main534_3 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main536_17 (Heap Addr Addr Addr Int) Bool)
(declare-fun inv_main545_9_0 (Heap Addr) Bool)
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (and (= var3 emptyHeap) (= var2 nullAddr)) (= var1 nullAddr))) (inv_main534_3 var3 var2 var0 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main534_3 var4 var3 var2 var1) (= var0 0))) (inv_main var4 var3 var2 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Heap)) (or (not (and (inv_main var13 var12 var11 var10) (and (and (and (and (and (= var9 var8) (= var7 var6)) (= var5 var4)) (= var3 var2)) (= var1 (|node::n| (getnode (read var8 var2))))) (and (and (= var0 1) (and (and (and (and (= var8 var13) (= var6 var12)) (= var4 var11)) (= var2 var10)) (= var0 (|node::h| (getnode (read var13 var10)))))) (not (= var10 nullAddr)))))) (inv_main var9 var7 var5 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main var8 var7 var6 var5) (and (and (not (= var4 1)) (and (and (and (and (= var3 var8) (= var2 var7)) (= var1 var6)) (= var0 var5)) (= var4 (|node::h| (getnode (read var8 var5)))))) (not (= var5 nullAddr))))) (inv_exit var3 var2))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Bool) (var3 node) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Heap) (var15 Heap) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Heap)) (or (not (and (inv_main534_3 var19 var18 var17 var16) (and (and (and (and (and (= var15 (write var14 var13 (O_node (node 1 (|node::n| (getnode (read var14 var13))))))) (= var12 var11)) (= var10 var13)) (= var9 var8)) (and (and (and (= var7 (write var15 var10 (O_node (node (|node::h| (getnode (read var15 var10))) var9)))) (= var6 var12)) (= var5 var10)) (= var4 var9))) (and (not (= var13 nullAddr)) (and (and (and (and (and (= var14 (newHeap (alloc var19 (O_node var3)))) (or (and var2 (= var11 (newAddr (alloc var19 (O_node var3))))) (and (not var2) (= var11 var18)))) (= var1 var17)) (= var8 var16)) (= var13 (newAddr (alloc var19 (O_node var3))))) (not (= var0 0))))))) (inv_main534_3 var7 var6 var5 var5))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main var3 var2 var1 var0) (= var0 nullAddr))) (inv_main545_9_0 var3 var2))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (inv_main536_17 var4 var3 var2 var1 var0)) (inv_main536_17 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Bool) (var5 Addr) (var6 node) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Heap)) (or (not (and (inv_main534_3 var12 var11 var10 var9) (and (and (= var8 nullAddr) (and (and (and (and (and (= var7 (newHeap (alloc var12 (O_node var6)))) (or (and var4 (= var5 (newAddr (alloc var12 (O_node var6))))) (and (not var4) (= var5 var11)))) (= var3 var10)) (= var2 var9)) (= var8 (newAddr (alloc var12 (O_node var6))))) (not (= var1 0)))) (= var0 1)))) (inv_main536_17 var7 var5 var8 var2 var0))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_exit var1 var0) (not (= var0 nullAddr))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main545_9_0 var1 var0) (not (= var0 nullAddr))))))
(check-sat)
