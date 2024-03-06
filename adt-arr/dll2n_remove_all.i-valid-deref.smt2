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
                   ((node (|node::data| Int) (|node::next| Addr) (|node::prev| Addr)))))
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
(declare-fun inv_main586_3 (Heap Int Int Int Int Addr) Bool)
(declare-fun inv_main590_7 (Heap Int Int Int Int Addr Addr Int) Bool)
(declare-fun inv_main595_8 (Heap Int Int Int Int Addr Addr) Bool)
(declare-fun inv_main605_6 (Heap Int Int Addr Int Int Addr) Bool)
(declare-fun inv_main614_3 (Heap Int Int) Bool)
(declare-fun inv_main617_5 (Heap Int Int Addr Int Int) Bool)
(declare-fun inv_main_2 (Heap Int Int Int Int Addr Addr) Bool)
(declare-fun inv_main_4 (Heap Int Int Int Int Addr Addr) Bool)
(declare-fun inv_main_5 (Heap Int Int Int Int Addr Addr) Bool)
(assert (forall ((var0 Int) (var1 Int) (var2 Heap)) (or (not (and (and (= var2 emptyHeap) (= var1 2)) (= var0 1))) (inv_main614_3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Heap)) (or (not (inv_main590_7 var7 var6 var5 var4 var3 var2 var1 var0)) (inv_main590_7 var7 var6 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 node) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Int) (var11 Int) (var12 Int) (var13 Int) (var14 Heap)) (or (not (and (inv_main586_3 var14 var13 var12 var11 var10 var9) (and (and (and (= nullAddr var8) (and (and (and (and (and (and (= var7 (newHeap (alloc var14 (O_node var6)))) (= var5 var13)) (= var4 var12)) (= var3 var11)) (= var2 var10)) (= var1 var9)) (= var8 (newAddr (alloc var14 (O_node var6)))))) (<= 0 (+ var11 (- 1)))) (= var0 1)))) (inv_main590_7 var7 var5 var4 var3 var2 var1 var8 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Int) (var11 Int) (var12 Int) (var13 Int) (var14 Heap)) (or (not (and (inv_main595_8 var14 var13 var12 var11 var10 var9 var8) (and (and (and (is-O_node (read var14 var9)) (is-O_node (read var14 var9))) (and (and (and (and (and (and (= var7 (write var14 var9 (O_node (node (|node::data| (getnode (read var14 var9))) (|node::next| (getnode (read var14 var9))) var8)))) (= var6 var13)) (= var5 var12)) (= var4 var11)) (= var3 var10)) (= var2 var9)) (= var1 var8))) (= var0 (+ var4 (- 1)))))) (inv_main586_3 var7 var6 var5 var0 var3 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Int) (var11 Int) (var12 Int) (var13 Int) (var14 Heap)) (or (not (and (inv_main_5 var14 var13 var12 var11 var10 var9 var8) (and (and (and (= var7 nullAddr) (and (is-O_node (read var14 var8)) (is-O_node (read var14 var8)))) (and (and (and (and (and (and (= var6 (write var14 var8 (O_node (node (|node::data| (getnode (read var14 var8))) (|node::next| (getnode (read var14 var8))) nullAddr)))) (= var5 var13)) (= var4 var12)) (= var3 var11)) (= var2 var10)) (= var7 var9)) (= var1 var8))) (= var0 (+ var3 (- 1)))))) (inv_main586_3 var6 var5 var4 var0 var2 var1))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Heap)) (or (not (and (inv_main614_3 var3 var2 var1) (= var0 nullAddr))) (inv_main586_3 var3 var2 var1 var2 var1 var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Heap)) (or (not (and (inv_main_4 var7 var6 var5 var4 var3 var2 var1) (and (and (is-O_node (read var7 var1)) (is-O_node (read var7 var1))) (= var0 (write var7 var1 (O_node (node (|node::data| (getnode (read var7 var1))) var2 (|node::prev| (getnode (read var7 var1)))))))))) (inv_main_5 var0 var6 var5 var4 var3 var2 var1))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Int) (var4 Int) (var5 Heap) (var6 Addr) (var7 Int) (var8 Int) (var9 Addr) (var10 Int) (var11 Int) (var12 Heap)) (or (not (and (inv_main617_5 var12 var11 var10 var9 var8 var7) (and (and (not (= var6 nullAddr)) (is-O_node (read var12 var9))) (and (and (and (and (and (and (= var5 var12) (= var4 var11)) (= var3 var10)) (= var2 var9)) (= var1 var8)) (= var0 var7)) (= var6 (|node::next| (getnode (read var12 var9)))))))) (inv_main605_6 var5 var4 var3 var2 var1 var0 var6))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Int) (var5 Int) (var6 Int) (var7 Addr) (var8 Int) (var9 Int) (var10 Int) (var11 Int) (var12 Addr) (var13 Heap) (var14 Heap) (var15 Int) (var16 Addr) (var17 Int) (var18 Int) (var19 Addr) (var20 Int) (var21 Int) (var22 Heap)) (or (not (and (inv_main605_6 var22 var21 var20 var19 var18 var17 var16) (and (and (and (<= 0 (+ var15 (- 1))) (and (and (and (and (and (and (and (and (= var14 (write var13 var12 defObj)) (= var11 var10)) (= var9 var8)) (= var7 var12)) (= var15 var6)) (= var5 var4)) (= var3 var2)) (and (is-O_node (read var22 var16)) (is-O_node (read var22 var16)))) (and (and (and (and (and (and (= var13 (write var22 var16 (O_node (node (|node::data| (getnode (read var22 var16))) (|node::next| (getnode (read var22 var16))) nullAddr)))) (= var10 var21)) (= var8 var20)) (= var12 var19)) (= var6 var18)) (= var4 var17)) (= var2 var16)))) (= var1 (+ var15 (- 1)))) (= var0 3)))) (inv_main617_5 var14 var11 var9 var3 var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Int) (var5 Int) (var6 Int) (var7 Addr) (var8 Int) (var9 Int) (var10 Int) (var11 Int) (var12 Addr) (var13 Heap) (var14 Heap) (var15 Int) (var16 Int) (var17 Int) (var18 Addr) (var19 Int) (var20 Int) (var21 Heap)) (or (not (and (inv_main617_5 var21 var20 var19 var18 var17 var16) (and (and (and (<= 0 (+ var15 (- 1))) (and (and (and (and (and (and (and (= var14 (write var13 var12 defObj)) (= var11 var10)) (= var9 var8)) (= var7 var12)) (= var15 var6)) (= var5 var4)) (= var3 var2)) (and (and (= var2 nullAddr) (is-O_node (read var21 var18))) (and (and (and (and (and (and (= var13 var21) (= var10 var20)) (= var8 var19)) (= var12 var18)) (= var6 var17)) (= var4 var16)) (= var2 (|node::next| (getnode (read var21 var18)))))))) (= var1 (+ var15 (- 1)))) (= var0 3)))) (inv_main617_5 var14 var11 var9 var3 var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Heap)) (or (not (and (inv_main586_3 var7 var6 var5 var4 var3 var2) (and (and (and (<= 0 (+ var6 (- 1))) (not (<= 0 (+ var4 (- 1))))) (= var1 (+ var6 (- 1)))) (= var0 3)))) (inv_main617_5 var7 var6 var5 var2 var1 var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Heap)) (or (not (and (inv_main_2 var7 var6 var5 var4 var3 var2 var1) (and (and (is-O_node (read var7 var1)) (is-O_node (read var7 var1))) (= var0 (write var7 var1 (O_node (node var3 (|node::next| (getnode (read var7 var1))) (|node::prev| (getnode (read var7 var1)))))))))) (inv_main_4 var0 var6 var5 var4 var3 var2 var1))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Int) (var4 Int) (var5 node) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Int) (var10 Int) (var11 Int) (var12 Int) (var13 Heap)) (or (not (and (inv_main586_3 var13 var12 var11 var10 var9 var8) (and (and (not (= nullAddr var7)) (and (and (and (and (and (and (= var6 (newHeap (alloc var13 (O_node var5)))) (= var4 var12)) (= var3 var11)) (= var2 var10)) (= var1 var9)) (= var0 var8)) (= var7 (newAddr (alloc var13 (O_node var5)))))) (<= 0 (+ var10 (- 1)))))) (inv_main_2 var6 var4 var3 var2 var1 var0 var7))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Int) (var4 Int) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Int) (var10 Int) (var11 Int) (var12 Int) (var13 Heap)) (or (not (and (inv_main_5 var13 var12 var11 var10 var9 var8 var7) (and (and (not (= var6 nullAddr)) (and (is-O_node (read var13 var7)) (is-O_node (read var13 var7)))) (and (and (and (and (and (and (= var5 (write var13 var7 (O_node (node (|node::data| (getnode (read var13 var7))) (|node::next| (getnode (read var13 var7))) nullAddr)))) (= var4 var12)) (= var3 var11)) (= var2 var10)) (= var1 var9)) (= var6 var8)) (= var0 var7))))) (inv_main595_8 var5 var4 var3 var2 var1 var6 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Heap)) (not (and (inv_main_2 var6 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var6 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Heap)) (not (and (inv_main_2 var6 var5 var4 var3 var2 var1 var0) (and (is-O_node (read var6 var0)) (not (is-O_node (read var6 var0))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Heap)) (not (and (inv_main_4 var6 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var6 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Heap)) (not (and (inv_main_4 var6 var5 var4 var3 var2 var1 var0) (and (is-O_node (read var6 var0)) (not (is-O_node (read var6 var0))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Heap)) (not (and (inv_main_5 var6 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var6 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Heap)) (not (and (inv_main_5 var6 var5 var4 var3 var2 var1 var0) (and (is-O_node (read var6 var0)) (not (is-O_node (read var6 var0))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Heap)) (not (and (inv_main595_8 var6 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var6 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Heap)) (not (and (inv_main595_8 var6 var5 var4 var3 var2 var1 var0) (and (is-O_node (read var6 var1)) (not (is-O_node (read var6 var1))))))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Int) (var4 Int) (var5 Heap)) (not (and (inv_main617_5 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var5 var2)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Addr) (var4 Int) (var5 Int) (var6 Heap)) (not (and (inv_main605_6 var6 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var6 var0)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Addr) (var4 Int) (var5 Int) (var6 Heap)) (not (and (inv_main605_6 var6 var5 var4 var3 var2 var1 var0) (and (is-O_node (read var6 var0)) (not (is-O_node (read var6 var0))))))))
(check-sat)
