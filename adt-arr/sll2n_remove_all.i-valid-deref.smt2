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
                   ((node (|node::data| Int) (|node::next| Addr)))))
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
(declare-fun inv_main577_5 (Heap Int Int Int Int Addr Int Addr Int) Bool)
(declare-fun inv_main585_7 (Heap Int Int Int Int Addr) Bool)
(declare-fun inv_main586_5 (Heap Int Int Int Int Addr Addr) Bool)
(declare-fun inv_main600_3 (Heap Int Int) Bool)
(declare-fun inv_main603_5 (Heap Int Int Addr Int Int) Bool)
(declare-fun inv_main_3 (Heap Int Int Int Int Addr Int Addr) Bool)
(declare-fun inv_main_5 (Heap Int Int Int Int Addr Int Addr) Bool)
(assert (forall ((var0 Int) (var1 Int) (var2 Heap)) (or (not (and (and (= var2 emptyHeap) (= var1 2)) (= var0 1))) (inv_main600_3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Int) (var4 Addr) (var5 Int) (var6 Int) (var7 Heap) (var8 Addr) (var9 Int) (var10 Int) (var11 Addr) (var12 Int) (var13 Int) (var14 Heap) (var15 Int) (var16 Int) (var17 Int) (var18 Addr) (var19 Int) (var20 Int) (var21 Heap)) (or (not (and (inv_main603_5 var21 var20 var19 var18 var17 var16) (and (and (and (<= 0 (+ var15 (- 1))) (and (and (is-O_node (read var21 var18)) (and (and (and (and (and (and (= var14 var21) (= var13 var20)) (= var12 var19)) (= var11 var18)) (= var10 var17)) (= var9 var16)) (= var8 (|node::next| (getnode (read var21 var18)))))) (and (and (and (and (and (and (= var7 (write var14 var11 defObj)) (= var6 var13)) (= var5 var12)) (= var4 var11)) (= var15 var10)) (= var3 var9)) (= var2 var8)))) (= var1 (+ var15 (- 1)))) (= var0 3)))) (inv_main603_5 var7 var6 var5 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Heap)) (or (not (and (inv_main585_7 var7 var6 var5 var4 var3 var2) (and (and (and (<= 0 (+ var6 (- 1))) (not (<= 0 (+ var4 (- 1))))) (= var1 (+ var6 (- 1)))) (= var0 3)))) (inv_main603_5 var7 var6 var5 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Addr) (var4 Int) (var5 Int) (var6 Int) (var7 Int) (var8 Heap)) (or (not (inv_main577_5 var8 var7 var6 var5 var4 var3 var2 var1 var0)) (inv_main577_5 var8 var7 var6 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 node) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Int) (var12 Int) (var13 Int) (var14 Int) (var15 Heap)) (or (not (and (inv_main585_7 var15 var14 var13 var12 var11 var10) (and (and (and (= nullAddr var9) (and (and (and (and (and (and (and (= var8 (newHeap (alloc var15 (O_node var7)))) (= var6 var14)) (= var5 var13)) (= var4 var12)) (= var3 var11)) (= var2 var10)) (= var1 var11)) (= var9 (newAddr (alloc var15 (O_node var7)))))) (<= 0 (+ var12 (- 1)))) (= var0 1)))) (inv_main577_5 var8 var6 var5 var4 var3 var2 var1 var9 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Heap) (var8 Addr) (var9 Int) (var10 Addr) (var11 Int) (var12 Int) (var13 Int) (var14 Int) (var15 Heap)) (or (not (and (inv_main_5 var15 var14 var13 var12 var11 var10 var9 var8) (and (and (is-O_node (read var15 var8)) (is-O_node (read var15 var8))) (and (and (and (and (and (and (and (= var7 (write var15 var8 (O_node (node var9 (|node::next| (getnode (read var15 var8))))))) (= var6 var14)) (= var5 var13)) (= var4 var12)) (= var3 var11)) (= var2 var10)) (= var1 var9)) (= var0 var8))))) (inv_main586_5 var7 var6 var5 var4 var3 var2 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 node) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Int) (var11 Int) (var12 Int) (var13 Int) (var14 Heap)) (or (not (and (inv_main585_7 var14 var13 var12 var11 var10 var9) (and (and (not (= nullAddr var8)) (and (and (and (and (and (and (and (= var7 (newHeap (alloc var14 (O_node var6)))) (= var5 var13)) (= var4 var12)) (= var3 var11)) (= var2 var10)) (= var1 var9)) (= var0 var10)) (= var8 (newAddr (alloc var14 (O_node var6)))))) (<= 0 (+ var11 (- 1)))))) (inv_main_3 var7 var5 var4 var3 var2 var1 var0 var8))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Int) (var3 Addr) (var4 Int) (var5 Int) (var6 Int) (var7 Int) (var8 Heap)) (or (not (and (inv_main_3 var8 var7 var6 var5 var4 var3 var2 var1) (and (and (is-O_node (read var8 var1)) (is-O_node (read var8 var1))) (= var0 (write var8 var1 (O_node (node (|node::data| (getnode (read var8 var1))) nullAddr))))))) (inv_main_5 var0 var7 var6 var5 var4 var3 var2 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Int) (var11 Int) (var12 Int) (var13 Int) (var14 Heap)) (or (not (and (inv_main586_5 var14 var13 var12 var11 var10 var9 var8) (and (and (and (is-O_node (read var14 var8)) (is-O_node (read var14 var8))) (and (and (and (and (and (and (= var7 (write var14 var8 (O_node (node (|node::data| (getnode (read var14 var8))) var9)))) (= var6 var13)) (= var5 var12)) (= var4 var11)) (= var3 var10)) (= var2 var9)) (= var1 var8))) (= var0 (+ var4 (- 1)))))) (inv_main585_7 var7 var6 var5 var0 var3 var1))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Int) (var4 Int) (var5 Heap) (var6 Int) (var7 Int) (var8 Heap)) (or (not (and (inv_main600_3 var8 var7 var6) (and (and (and (and (and (= var5 var8) (= var4 var7)) (= var3 var6)) (= var2 var7)) (= var1 var6)) (= var0 nullAddr)))) (inv_main585_7 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Heap)) (not (and (inv_main_3 var7 var6 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var7 var0)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Heap)) (not (and (inv_main_3 var7 var6 var5 var4 var3 var2 var1 var0) (and (is-O_node (read var7 var0)) (not (is-O_node (read var7 var0))))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Heap)) (not (and (inv_main_5 var7 var6 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var7 var0)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Heap)) (not (and (inv_main_5 var7 var6 var5 var4 var3 var2 var1 var0) (and (is-O_node (read var7 var0)) (not (is-O_node (read var7 var0))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Heap)) (not (and (inv_main586_5 var6 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var6 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Heap)) (not (and (inv_main586_5 var6 var5 var4 var3 var2 var1 var0) (and (is-O_node (read var6 var0)) (not (is-O_node (read var6 var0))))))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Int) (var4 Int) (var5 Heap)) (not (and (inv_main603_5 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var5 var2)))))))
(check-sat)
