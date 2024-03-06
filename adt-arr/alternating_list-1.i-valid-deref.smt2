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
(declare-fun inv_main533_3 (Heap Int) Bool)
(declare-fun inv_main534_15 (Heap Int Addr Int) Bool)
(declare-fun inv_main536_3 (Heap Int Addr Addr Addr) Bool)
(declare-fun inv_main538_15 (Heap Int Addr Addr Addr) Bool)
(declare-fun inv_main541_12 (Heap Int Addr Addr Addr) Bool)
(declare-fun inv_main546_17 (Heap Int Addr Addr Addr Int) Bool)
(declare-fun inv_main567_5 (Heap Int Addr Addr Addr Addr) Bool)
(declare-fun inv_main_13 (Heap Int Addr Addr Addr) Bool)
(declare-fun inv_main_16 (Heap Int Addr Addr Addr) Bool)
(declare-fun inv_main_19 (Heap Int Addr Addr Addr) Bool)
(declare-fun inv_main_20 (Heap Int Addr Addr Addr) Bool)
(declare-fun inv_main_23 (Heap Int Addr Addr Addr) Bool)
(declare-fun inv_main_26 (Heap Int Addr Addr Addr) Bool)
(declare-fun inv_main_3 (Heap Int Addr Addr Addr) Bool)
(declare-fun inv_main_9 (Heap Int Addr Addr Addr) Bool)
(assert (forall ((var0 Int) (var1 Heap)) (or (not (and (= var1 emptyHeap) (= var0 1))) (inv_main533_3 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap) (var5 Int) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Int) (var10 Heap)) (or (not (and (inv_main_26 var10 var9 var8 var7 var6) (and (and (not (= var5 3)) (is-O_node (read var10 var6))) (and (and (and (and (and (= var4 var10) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var0 var6)) (= var5 (|node::h| (getnode (read var10 var6)))))))) (inv_main567_5 var4 var3 var2 var1 var0 var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Int) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Int) (var13 Heap)) (or (not (and (inv_main567_5 var13 var12 var11 var10 var9 var8) (and (and (is-O_node (read var13 var9)) (and (and (and (and (and (and (= var7 var13) (= var6 var12)) (= var5 var11)) (= var4 var10)) (= var3 var9)) (= var2 var8)) (= var1 (|node::n| (getnode (read var13 var9)))))) (= var0 (write var7 var2 defObj))))) (inv_main_26 var0 var6 var5 var4 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap) (var5 Int) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Int) (var10 Heap)) (or (not (and (inv_main_16 var10 var9 var8 var7 var6) (and (and (= var5 3) (is-O_node (read var10 var6))) (and (and (and (and (and (= var4 var10) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var0 var6)) (= var5 (|node::h| (getnode (read var10 var6)))))))) (inv_main_26 var4 var3 var2 var1 var2))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap)) (or (not (and (inv_main536_3 var5 var4 var3 var2 var1) (and (not (= var4 0)) (not (= var0 0))))) (inv_main538_15 var5 var4 var3 var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Int) (var10 Heap)) (or (not (and (inv_main_19 var10 var9 var8 var7 var6) (and (is-O_node (read var10 var6)) (and (and (and (and (and (= var5 var10) (= var4 var9)) (= var3 var8)) (= var2 var7)) (= var1 var6)) (= var0 (|node::n| (getnode (read var10 var6)))))))) (inv_main_16 var5 var4 var3 var2 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Int) (var10 Heap)) (or (not (and (inv_main_3 var10 var9 var8 var7 var6) (and (and (and (is-O_node (read var10 var6)) (is-O_node (read var10 var6))) (and (and (and (and (= var5 (write var10 var6 (O_node (node 3 (|node::n| (getnode (read var10 var6))))))) (= var4 var9)) (= var3 var8)) (= var2 var7)) (= var1 var6))) (= var0 1)))) (inv_main_16 var5 var0 var3 var2 var3))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Int) (var6 Int) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Int) (var11 Heap)) (or (not (and (inv_main_16 var11 var10 var9 var8 var7) (and (and (= var6 0) (and (and (not (= var5 3)) (is-O_node (read var11 var7))) (and (and (and (and (and (= var4 var11) (= var6 var10)) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var5 (|node::h| (getnode (read var11 var7))))))) (= var0 1)))) (inv_main_23 var4 var0 var3 var2 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap)) (or (not (and (inv_main536_3 var5 var4 var3 var2 var1) (= var0 0))) (inv_main_3 var5 var4 var3 var2 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Int) (var6 Int) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Int) (var11 Heap)) (or (not (and (inv_main_16 var11 var10 var9 var8 var7) (and (and (not (= var6 0)) (and (and (not (= var5 3)) (is-O_node (read var11 var7))) (and (and (and (and (and (= var4 var11) (= var6 var10)) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var5 (|node::h| (getnode (read var11 var7))))))) (= var0 0)))) (inv_main_20 var4 var0 var3 var2 var1))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap)) (or (not (and (inv_main_9 var5 var4 var3 var2 var1) (and (and (is-O_node (read var5 var1)) (is-O_node (read var5 var1))) (= var0 (write var5 var1 (O_node (node (|node::h| (getnode (read var5 var1))) var2))))))) (inv_main_13 var0 var4 var3 var2 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap)) (or (not (and (inv_main536_3 var5 var4 var3 var2 var1) (and (= var4 0) (not (= var0 0))))) (inv_main541_12 var5 var4 var3 var2 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Int) (var8 node) (var9 Heap) (var10 Heap) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Int) (var16 Heap)) (or (not (and (inv_main538_15 var16 var15 var14 var13 var12) (and (and (not (= var11 nullAddr)) (and (and (and (and (and (= var10 (newHeap (alloc var9 (O_node var8)))) (= var7 0)) (= var6 var5)) (= var4 var3)) (= var2 var1)) (= var11 (newAddr (alloc var9 (O_node var8)))))) (and (and (is-O_node (read var16 var12)) (is-O_node (read var16 var12))) (and (and (and (and (= var9 (write var16 var12 (O_node (node 1 (|node::n| (getnode (read var16 var12))))))) (= var0 var15)) (= var5 var14)) (= var3 var13)) (= var1 var12)))))) (inv_main_9 var10 var7 var6 var11 var2))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Int) (var8 node) (var9 Heap) (var10 Heap) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Int) (var16 Heap)) (or (not (and (inv_main541_12 var16 var15 var14 var13 var12) (and (and (not (= var11 nullAddr)) (and (and (and (and (and (= var10 (newHeap (alloc var9 (O_node var8)))) (= var7 1)) (= var6 var5)) (= var4 var3)) (= var2 var1)) (= var11 (newAddr (alloc var9 (O_node var8)))))) (and (and (is-O_node (read var16 var12)) (is-O_node (read var16 var12))) (and (and (and (and (= var9 (write var16 var12 (O_node (node 2 (|node::n| (getnode (read var16 var12))))))) (= var0 var15)) (= var5 var14)) (= var3 var13)) (= var1 var12)))))) (inv_main_9 var10 var7 var6 var11 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Int) (var10 Heap)) (or (not (and (inv_main_13 var10 var9 var8 var7 var6) (and (is-O_node (read var10 var6)) (and (and (and (and (and (= var5 var10) (= var4 var9)) (= var3 var8)) (= var2 var7)) (= var1 var6)) (= var0 (|node::n| (getnode (read var10 var6)))))))) (inv_main536_3 var5 var4 var3 var2 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 node) (var3 Heap) (var4 Addr) (var5 Int) (var6 Heap)) (or (not (and (inv_main533_3 var6 var5) (and (not (= var4 nullAddr)) (and (and (= var3 (newHeap (alloc var6 (O_node var2)))) (= var1 var5)) (= var4 (newAddr (alloc var6 (O_node var2)))))))) (inv_main536_3 var3 var1 var4 var0 var4))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap) (var5 Int) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Int) (var10 Heap)) (or (not (and (inv_main_20 var10 var9 var8 var7 var6) (and (and (= var5 1) (is-O_node (read var10 var6))) (and (and (and (and (and (= var4 var10) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var0 var6)) (= var5 (|node::h| (getnode (read var10 var6)))))))) (inv_main_19 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap) (var5 Int) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Int) (var10 Heap)) (or (not (and (inv_main_23 var10 var9 var8 var7 var6) (and (and (= var5 2) (is-O_node (read var10 var6))) (and (and (and (and (and (= var4 var10) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var0 var6)) (= var5 (|node::h| (getnode (read var10 var6)))))))) (inv_main_19 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap)) (or (not (inv_main546_17 var5 var4 var3 var2 var1 var0)) (inv_main546_17 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Int) (var9 node) (var10 Heap) (var11 Heap) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Int) (var17 Heap)) (or (not (and (inv_main538_15 var17 var16 var15 var14 var13) (and (and (and (= var12 nullAddr) (and (and (and (and (and (= var11 (newHeap (alloc var10 (O_node var9)))) (= var8 0)) (= var7 var6)) (= var5 var4)) (= var3 var2)) (= var12 (newAddr (alloc var10 (O_node var9)))))) (and (and (is-O_node (read var17 var13)) (is-O_node (read var17 var13))) (and (and (and (and (= var10 (write var17 var13 (O_node (node 1 (|node::n| (getnode (read var17 var13))))))) (= var1 var16)) (= var6 var15)) (= var4 var14)) (= var2 var13)))) (= var0 1)))) (inv_main546_17 var11 var8 var7 var12 var3 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Int) (var9 node) (var10 Heap) (var11 Heap) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Int) (var17 Heap)) (or (not (and (inv_main541_12 var17 var16 var15 var14 var13) (and (and (and (= var12 nullAddr) (and (and (and (and (and (= var11 (newHeap (alloc var10 (O_node var9)))) (= var8 1)) (= var7 var6)) (= var5 var4)) (= var3 var2)) (= var12 (newAddr (alloc var10 (O_node var9)))))) (and (and (is-O_node (read var17 var13)) (is-O_node (read var17 var13))) (and (and (and (and (= var10 (write var17 var13 (O_node (node 2 (|node::n| (getnode (read var17 var13))))))) (= var1 var16)) (= var6 var15)) (= var4 var14)) (= var2 var13)))) (= var0 1)))) (inv_main546_17 var11 var8 var7 var12 var3 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Heap)) (or (not (inv_main534_15 var3 var2 var1 var0)) (inv_main534_15 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 node) (var3 Heap) (var4 Addr) (var5 Int) (var6 Heap)) (or (not (and (inv_main533_3 var6 var5) (and (and (= var4 nullAddr) (and (and (= var3 (newHeap (alloc var6 (O_node var2)))) (= var1 var5)) (= var4 (newAddr (alloc var6 (O_node var2)))))) (= var0 1)))) (inv_main534_15 var3 var1 var4 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap)) (not (and (inv_main538_15 var4 var3 var2 var1 var0) (not (is-O_node (read var4 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap)) (not (and (inv_main538_15 var4 var3 var2 var1 var0) (and (is-O_node (read var4 var0)) (not (is-O_node (read var4 var0))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap)) (not (and (inv_main541_12 var4 var3 var2 var1 var0) (not (is-O_node (read var4 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap)) (not (and (inv_main541_12 var4 var3 var2 var1 var0) (and (is-O_node (read var4 var0)) (not (is-O_node (read var4 var0))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap)) (not (and (inv_main_9 var4 var3 var2 var1 var0) (not (is-O_node (read var4 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap)) (not (and (inv_main_9 var4 var3 var2 var1 var0) (and (is-O_node (read var4 var0)) (not (is-O_node (read var4 var0))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap)) (not (and (inv_main_13 var4 var3 var2 var1 var0) (not (is-O_node (read var4 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap)) (not (and (inv_main_3 var4 var3 var2 var1 var0) (not (is-O_node (read var4 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap)) (not (and (inv_main_3 var4 var3 var2 var1 var0) (and (is-O_node (read var4 var0)) (not (is-O_node (read var4 var0))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap)) (not (and (inv_main_16 var4 var3 var2 var1 var0) (not (is-O_node (read var4 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap)) (not (and (inv_main_20 var4 var3 var2 var1 var0) (not (is-O_node (read var4 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap)) (not (and (inv_main_23 var4 var3 var2 var1 var0) (not (is-O_node (read var4 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap)) (not (and (inv_main_19 var4 var3 var2 var1 var0) (not (is-O_node (read var4 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap)) (not (and (inv_main_26 var4 var3 var2 var1 var0) (not (is-O_node (read var4 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap)) (not (and (inv_main567_5 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var5 var1)))))))
(check-sat)
