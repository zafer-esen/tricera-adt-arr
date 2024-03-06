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
                   ((node (|node::next| Addr) (|node::event1| Int) (|node::event2| Int)))))
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
(declare-fun inv_main574_5 (Heap) Bool)
(declare-fun inv_main574_5_1 (Heap Addr) Bool)
(declare-fun inv_main587_5 (Heap Addr Addr) Bool)
(declare-fun inv_main589_13 (Heap Addr Addr Int) Bool)
(declare-fun inv_main589_13_12 (Heap Addr Addr) Bool)
(declare-fun inv_main589_14 (Heap Addr Addr Int) Bool)
(assert (forall ((var0 Heap)) (or (not (= var0 emptyHeap)) (inv_main574_5 var0))))
(assert (forall ((var0 Addr) (var1 Heap)) (or (not (and (inv_main574_5 var1) (= var0 nullAddr))) (inv_main574_5_1 var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Heap)) (or (not (and (inv_main574_5_1 var4 var3) (and (or (or (or (<= 0 (+ (* (- 1) var2) (- 1))) (<= 0 (+ (+ var2 (- 3)) (- 1)))) (<= 0 (+ (* (- 1) var1) (- 1)))) (<= 0 (+ (+ var1 (- 3)) (- 1)))) (not (= var0 0))))) (inv_main574_5_1 var4 var3))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Heap)) (or (not (and (inv_main574_5_1 var4 var3) (and (and (or (or (and (= var2 0) (= var1 2)) (and (= var2 1) (= var1 3))) (and (= var2 0) (= var1 3))) (and (and (and (not (<= 0 (+ (* (- 1) var2) (- 1)))) (not (<= 0 (+ (+ var2 (- 3)) (- 1))))) (not (<= 0 (+ (* (- 1) var1) (- 1))))) (not (<= 0 (+ (+ var1 (- 3)) (- 1)))))) (not (= var0 0))))) (inv_main574_5_1 var4 var3))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Int) (var8 Int) (var9 Addr) (var10 Heap) (var11 Addr) (var12 Int) (var13 Int) (var14 Addr) (var15 Heap) (var16 Addr) (var17 Int) (var18 Int) (var19 Int) (var20 Int) (var21 Addr) (var22 node) (var23 Heap) (var24 Addr) (var25 Heap)) (or (not (and (inv_main574_5_1 var25 var24) (and (and (and (and (and (and (and (and (and (= var23 (newHeap (alloc var25 (O_node var22)))) (= var21 var24)) (= var20 var19)) (= var18 var17)) (= var16 (newAddr (alloc var25 (O_node var22))))) (and (and (and (and (= var15 (write var23 var16 (O_node (node (|node::next| (getnode (read var23 var16))) var20 (|node::event2| (getnode (read var23 var16))))))) (= var14 var21)) (= var13 var20)) (= var12 var18)) (= var11 var16))) (and (and (and (and (= var10 (write var15 var11 (O_node (node (|node::next| (getnode (read var15 var11))) (|node::event1| (getnode (read var15 var11))) var12)))) (= var9 var14)) (= var8 var13)) (= var7 var12)) (= var6 var11))) (and (and (and (and (= var5 (write var10 var6 (O_node (node var9 (|node::event1| (getnode (read var10 var6))) (|node::event2| (getnode (read var10 var6))))))) (= var4 var9)) (= var3 var8)) (= var2 var7)) (= var1 var6))) (and (and (and (or (not (= var19 0)) (not (= var17 2))) (or (not (= var19 1)) (not (= var17 3)))) (or (not (= var19 0)) (not (= var17 3)))) (and (and (and (not (<= 0 (+ (* (- 1) var19) (- 1)))) (not (<= 0 (+ (+ var19 (- 3)) (- 1))))) (not (<= 0 (+ (* (- 1) var17) (- 1))))) (not (<= 0 (+ (+ var17 (- 3)) (- 1))))))) (not (= var0 0))))) (inv_main574_5_1 var5 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main589_13_12 var6 var5 var4) (and (and (and (= var3 var6) (= var2 var5)) (= var1 var4)) (= var0 (|node::next| (getnode (read var6 var4))))))) (inv_main587_5 var3 var2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main589_13 var7 var6 var5 var4) (and (and (and (and (= var3 var7) (= var2 var6)) (= var1 var5)) (= var0 (|node::next| (getnode (read var7 var5))))) (= var4 0)))) (inv_main587_5 var3 var2 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap)) (or (not (and (inv_main574_5_1 var2 var1) (= var0 0))) (inv_main587_5 var2 var1 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main589_13 var3 var2 var1 var0) (not (= var0 0)))) (inv_main589_13_12 var3 var2 var1))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main589_14 var4 var3 var2 var1) (and (not (= var1 0)) (= var0 1)))) (inv_main589_13 var4 var3 var2 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Int) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main589_14 var8 var7 var6 var5) (and (and (and (not (= var4 0)) (= var5 0)) (and (and (and (= var3 var8) (= var2 var7)) (= var1 var6)) (= var4 (|node::event1| (getnode (read var8 var6)))))) (= var0 0)))) (inv_main589_13 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Heap) (var11 Int) (var12 Int) (var13 Addr) (var14 Addr) (var15 Heap)) (or (not (and (inv_main589_14 var15 var14 var13 var12) (and (and (and (and (= var11 0) (= var12 0)) (and (and (and (= var10 var15) (= var9 var14)) (= var8 var13)) (= var11 (|node::event1| (getnode (read var15 var13)))))) (and (and (and (= var7 var10) (= var6 var9)) (= var5 var8)) (= var4 (|node::event2| (getnode (read var10 var8)))))) (and (and (and (= var3 var7) (= var2 var6)) (= var1 var5)) (or (and (= var4 2) (= var0 1)) (and (not (= var4 2)) (= var0 0))))))) (inv_main589_13 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main587_5 var7 var6 var5) (and (and (and (not (= var4 1)) (and (and (and (= var3 var7) (= var2 var6)) (= var1 var5)) (= var4 (|node::event1| (getnode (read var7 var5)))))) (not (= var5 nullAddr))) (= var0 0)))) (inv_main589_14 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Int) (var9 Addr) (var10 Addr) (var11 Heap)) (or (not (and (inv_main587_5 var11 var10 var9) (and (and (and (and (= var8 1) (and (and (and (= var7 var11) (= var6 var10)) (= var5 var9)) (= var8 (|node::event1| (getnode (read var11 var9)))))) (and (and (and (= var4 var7) (= var3 var6)) (= var2 var5)) (= var1 (|node::event2| (getnode (read var7 var5)))))) (not (= var9 nullAddr))) (or (and (= var1 3) (= var0 1)) (and (not (= var1 3)) (= var0 0)))))) (inv_main589_14 var4 var3 var2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (inv_main589_13_12 var2 var1 var0))))
(check-sat)
