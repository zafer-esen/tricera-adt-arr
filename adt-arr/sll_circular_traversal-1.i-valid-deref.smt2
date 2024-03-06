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
                   ((node (|node::next| Addr) (|node::data| Int)))))
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
(declare-fun inv_main (Heap Int Int Int Int Addr) Bool)
(declare-fun inv_main577_5 (Heap Int Int Int Int Addr Int) Bool)
(declare-fun inv_main581_3 (Heap Int Int Int Int Addr Addr) Bool)
(declare-fun inv_main585_7 (Heap Int Int Int Int Addr Addr Addr Int) Bool)
(declare-fun inv_main598_3 (Heap Int Int) Bool)
(declare-fun inv_main600_3 (Heap Int Int Addr Int Addr) Bool)
(declare-fun inv_main_10 (Heap Int Int Int Int Addr Addr Addr) Bool)
(declare-fun inv_main_16 (Heap Int Int Addr Int Addr) Bool)
(declare-fun inv_main_18 (Heap Int Int Addr Int Addr) Bool)
(declare-fun inv_main_2 (Heap Int Int Int Int Addr) Bool)
(declare-fun inv_main_20 (Heap Int Int Addr Int Addr) Bool)
(declare-fun inv_main_22 (Heap Int Int Addr Int Addr) Bool)
(declare-fun inv_main_4 (Heap Int Int Int Int Addr Addr) Bool)
(declare-fun inv_main_6 (Heap Int Int Int Int Addr Addr Addr) Bool)
(assert (forall ((var0 Int) (var1 Int) (var2 Heap)) (or (not (and (and (= var2 emptyHeap) (= var1 5)) (= var0 1))) (inv_main598_3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Int) (var10 Addr) (var11 Int) (var12 Int) (var13 Heap)) (or (not (and (inv_main_18 var13 var12 var11 var10 var9 var8) (and (and (not (= var7 var6)) (and (is-O_node (read var13 var8)) (and (and (and (and (and (and (= var5 var13) (= var4 var12)) (= var3 var11)) (= var6 var10)) (= var2 var9)) (= var1 var8)) (= var7 (|node::next| (getnode (read var13 var8))))))) (= var0 (+ var2 1))))) (inv_main600_3 var5 var4 var3 var6 var0 var7))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Int) (var11 Int) (var12 Int) (var13 Int) (var14 Heap)) (or (not (and (inv_main_4 var14 var13 var12 var11 var10 var9 var8) (and (and (and (is-O_node (read var14 var9)) (is-O_node (read var14 var9))) (and (and (and (and (and (and (= var7 (write var14 var9 (O_node (node var8 (|node::data| (getnode (read var14 var9))))))) (= var6 var13)) (= var5 var12)) (= var4 var11)) (= var3 var10)) (= var2 var9)) (= var1 var8))) (= var0 1)))) (inv_main600_3 var7 var6 var5 var1 var0 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Int) (var10 Addr) (var11 Int) (var12 Int) (var13 Heap)) (or (not (and (inv_main_18 var13 var12 var11 var10 var9 var8) (and (and (= var7 var6) (and (is-O_node (read var13 var8)) (and (and (and (and (and (and (= var5 var13) (= var4 var12)) (= var3 var11)) (= var6 var10)) (= var2 var9)) (= var1 var8)) (= var7 (|node::next| (getnode (read var13 var8))))))) (= var0 (+ (+ var2 1) (* (- 1) var4)))))) (inv_main_20 var5 var4 var3 var6 var0 var7))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Heap) (var6 Addr) (var7 Int) (var8 Int) (var9 Int) (var10 Heap) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Int) (var17 Addr) (var18 Int) (var19 Int) (var20 Heap)) (or (not (and (inv_main_22 var20 var19 var18 var17 var16 var15) (and (and (not (= var14 var13)) (and (and (and (not (= var12 var11)) (is-O_node (read var20 var15))) (and (and (and (and (and (and (= var10 var20) (= var9 var19)) (= var8 var18)) (= var11 var17)) (= var7 var16)) (= var12 var15)) (= var6 (|node::next| (getnode (read var20 var15)))))) (and (and (and (and (and (and (= var5 (write var10 var12 defObj)) (= var4 var9)) (= var3 var8)) (= var13 var11)) (= var2 var7)) (= var1 var12)) (= var14 var6)))) (= var0 (+ var2 1))))) (inv_main_20 var5 var4 var3 var13 var0 var14))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Int) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Int) (var10 Addr) (var11 Int) (var12 Int) (var13 Heap)) (or (not (and (inv_main_22 var13 var12 var11 var10 var9 var8) (and (and (not (= var7 var6)) (and (and (= var5 var6) (is-O_node (read var13 var8))) (and (and (and (and (and (and (= var4 var13) (= var3 var12)) (= var2 var11)) (= var6 var10)) (= var1 var9)) (= var5 var8)) (= var7 (|node::next| (getnode (read var13 var8))))))) (= var0 (+ var1 1))))) (inv_main_20 var4 var3 var2 var6 var0 var7))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Heap)) (or (not (and (inv_main var6 var5 var4 var3 var2 var1) (and (and (is-O_node (read var6 var1)) (is-O_node (read var6 var1))) (= var0 (write var6 var1 (O_node (node var1 (|node::data| (getnode (read var6 var1)))))))))) (inv_main_2 var0 var5 var4 var3 var2 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Int) (var6 Int) (var7 Int) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Int) (var13 Int) (var14 Int) (var15 Int) (var16 Heap)) (or (not (and (inv_main_10 var16 var15 var14 var13 var12 var11 var10 var9) (and (and (and (is-O_node (read var16 var9)) (is-O_node (read var16 var9))) (and (and (and (and (and (and (and (= var8 (write var16 var9 (O_node (node (|node::next| (getnode (read var16 var9))) var12)))) (= var7 var15)) (= var6 var14)) (= var5 var13)) (= var4 var12)) (= var3 var11)) (= var2 var10)) (= var1 var9))) (= var0 (+ var5 (- 1)))))) (inv_main581_3 var8 var7 var6 var0 var4 var3 var1))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Int) (var4 Int) (var5 Heap) (var6 Addr) (var7 Int) (var8 Int) (var9 Int) (var10 Int) (var11 Heap)) (or (not (and (inv_main_2 var11 var10 var9 var8 var7 var6) (and (and (is-O_node (read var11 var6)) (is-O_node (read var11 var6))) (and (and (and (and (and (= var5 (write var11 var6 (O_node (node (|node::next| (getnode (read var11 var6))) var7)))) (= var4 var10)) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var0 var6))))) (inv_main581_3 var5 var4 var3 var2 var1 var0 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Int) (var4 Int) (var5 Heap)) (or (not (and (inv_main600_3 var5 var4 var3 var2 var1 var0) (and (is-O_node (read var5 var0)) (= var3 (|node::data| (getnode (read var5 var0))))))) (inv_main_16 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 node) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Int) (var12 Int) (var13 Int) (var14 Int) (var15 Heap)) (or (not (and (inv_main581_3 var15 var14 var13 var12 var11 var10 var9) (and (and (not (= nullAddr var8)) (and (and (and (and (and (and (and (= var7 (newHeap (alloc var15 (O_node var6)))) (= var5 var14)) (= var4 var13)) (= var3 var12)) (= var2 var11)) (= var1 var10)) (= var0 var9)) (= var8 (newAddr (alloc var15 (O_node var6)))))) (<= 0 (+ (+ var12 (- 1)) (- 1)))))) (inv_main_6 var7 var5 var4 var3 var2 var1 var0 var8))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Int) (var4 node) (var5 Heap) (var6 Addr) (var7 Int) (var8 Int) (var9 Heap)) (or (not (and (inv_main598_3 var9 var8 var7) (and (not (= nullAddr var6)) (and (and (and (and (and (= var5 (newHeap (alloc var9 (O_node var4)))) (= var3 var8)) (= var2 var7)) (= var1 var8)) (= var0 var7)) (= var6 (newAddr (alloc var9 (O_node var4)))))))) (inv_main var5 var3 var2 var1 var0 var6))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Int) (var3 Addr) (var4 Int) (var5 Int) (var6 Heap)) (or (not (and (inv_main_16 var6 var5 var4 var3 var2 var1) (and (and (is-O_node (read var6 var1)) (is-O_node (read var6 var1))) (= var0 (write var6 var1 (O_node (node (|node::next| (getnode (read var6 var1))) var2))))))) (inv_main_18 var0 var5 var4 var3 var2 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Int) (var6 Int) (var7 Int) (var8 Heap)) (or (not (inv_main585_7 var8 var7 var6 var5 var4 var3 var2 var1 var0)) (inv_main585_7 var8 var7 var6 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 node) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Int) (var13 Int) (var14 Int) (var15 Int) (var16 Heap)) (or (not (and (inv_main581_3 var16 var15 var14 var13 var12 var11 var10) (and (and (and (= nullAddr var9) (and (and (and (and (and (and (and (= var8 (newHeap (alloc var16 (O_node var7)))) (= var6 var15)) (= var5 var14)) (= var4 var13)) (= var3 var12)) (= var2 var11)) (= var1 var10)) (= var9 (newAddr (alloc var16 (O_node var7)))))) (<= 0 (+ (+ var13 (- 1)) (- 1)))) (= var0 1)))) (inv_main585_7 var8 var6 var5 var4 var3 var2 var1 var9 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Heap)) (or (not (inv_main577_5 var6 var5 var4 var3 var2 var1 var0)) (inv_main577_5 var6 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Int) (var4 Int) (var5 node) (var6 Heap) (var7 Addr) (var8 Int) (var9 Int) (var10 Heap)) (or (not (and (inv_main598_3 var10 var9 var8) (and (and (= nullAddr var7) (and (and (and (and (and (= var6 (newHeap (alloc var10 (O_node var5)))) (= var4 var9)) (= var3 var8)) (= var2 var9)) (= var1 var8)) (= var7 (newAddr (alloc var10 (O_node var5)))))) (= var0 1)))) (inv_main577_5 var6 var4 var3 var2 var1 var7 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Int) (var4 Int) (var5 Heap)) (or (not (and (inv_main_20 var5 var4 var3 var2 var1 var0) (and (is-O_node (read var5 var0)) (= var1 (|node::data| (getnode (read var5 var0))))))) (inv_main_22 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Int) (var6 Int) (var7 Int) (var8 Heap)) (or (not (and (inv_main_6 var8 var7 var6 var5 var4 var3 var2 var1) (and (and (is-O_node (read var8 var1)) (is-O_node (read var8 var1))) (= var0 (write var8 var1 (O_node (node var2 (|node::data| (getnode (read var8 var1)))))))))) (inv_main_10 var0 var7 var6 var5 var4 var3 var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Heap)) (or (not (and (inv_main581_3 var6 var5 var4 var3 var2 var1 var0) (not (<= 0 (+ (+ var3 (- 1)) (- 1)))))) (inv_main_4 var6 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Int) (var4 Int) (var5 Heap)) (not (and (inv_main var5 var4 var3 var2 var1 var0) (not (is-O_node (read var5 var0)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Int) (var4 Int) (var5 Heap)) (not (and (inv_main var5 var4 var3 var2 var1 var0) (and (is-O_node (read var5 var0)) (not (is-O_node (read var5 var0))))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Int) (var4 Int) (var5 Heap)) (not (and (inv_main_2 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var5 var0)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Int) (var4 Int) (var5 Heap)) (not (and (inv_main_2 var5 var4 var3 var2 var1 var0) (and (is-O_node (read var5 var0)) (not (is-O_node (read var5 var0))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Heap)) (not (and (inv_main_6 var7 var6 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var7 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Heap)) (not (and (inv_main_6 var7 var6 var5 var4 var3 var2 var1 var0) (and (is-O_node (read var7 var0)) (not (is-O_node (read var7 var0))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Heap)) (not (and (inv_main_10 var7 var6 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var7 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Heap)) (not (and (inv_main_10 var7 var6 var5 var4 var3 var2 var1 var0) (and (is-O_node (read var7 var0)) (not (is-O_node (read var7 var0))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Heap)) (not (and (inv_main_4 var6 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var6 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Heap)) (not (and (inv_main_4 var6 var5 var4 var3 var2 var1 var0) (and (is-O_node (read var6 var1)) (not (is-O_node (read var6 var1))))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Int) (var4 Int) (var5 Heap)) (not (and (inv_main600_3 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var5 var0)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Int) (var4 Int) (var5 Heap)) (not (and (inv_main_16 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var5 var0)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Int) (var4 Int) (var5 Heap)) (not (and (inv_main_16 var5 var4 var3 var2 var1 var0) (and (is-O_node (read var5 var0)) (not (is-O_node (read var5 var0))))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Int) (var4 Int) (var5 Heap)) (not (and (inv_main_18 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var5 var0)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Int) (var4 Int) (var5 Heap)) (not (and (inv_main_20 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var5 var0)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Int) (var4 Int) (var5 Heap)) (not (and (inv_main_22 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var5 var0)))))))
(check-sat)