(set-logic HORN)
(set-info :source |
    Benchmark: 
    Output by Princess (http://www.philipp.ruemmer.org/princess.shtml)
|)
;===============================================================================
; Encoding of Heap sorts and operations
;-------------------------------------------------------------------------------
(define-sort Addr() Int)
(declare-datatypes ((AddrRange 0))
                   (((AddrRange (AddrRangeStart Addr) (AddrRangeSize Int)))))

(declare-datatypes ((HeapObject 0) (node 0))
                   (((O_Int (getInt Int)) (O_UInt (getUInt Int)) (O_Addr (getAddr Addr)) (O_AddrRange (getAddrRange AddrRange)) (O_node (getnode node)) (defObj))
                   ((node (|node::hash| Int) (|node::next| Addr)))))
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
(declare-fun inv_main581_5 (Heap Addr Int) Bool)
(declare-fun inv_main591_13 (Heap Addr Int) Bool)
(declare-fun Inv_Heap_exp_exp (Addr Int Addr) Bool)
(declare-fun inv_main (Heap Addr Int) Bool)
(declare-fun _Glue1 (Addr Int Int Addr Heap HeapObject) Bool)
(declare-fun _Glue3 (Heap Int Int Addr HeapObject) Bool)
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap)) (or (not (and (inv_main581_5 var2 var1 var0) (and (<= 0 (+ (* (- 1) var0) 1000000)) (<= 0 var0)))) (inv_main581_5 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap)) (or (not (and (inv_main581_5 var2 var1 var0) (and (<= 0 (+ (* (- 1) var0) 1000000)) (<= 0 var0)))) (inv_main581_5 var2 var1 var0))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Int) (var3 Heap) (var4 Addr) (var5 Int) (var6 Addr)) (or (not (and (and (Inv_Heap_exp_exp var6 var5 var4) (inv_main591_13 var3 var6 var2)) (and (and (and (= (O_node var1) var0) (= (node var5 var4) var1)) (= (read var3 var6) var0)) (valid var3 var6)))) (inv_main var3 var4 var2))))
(assert (forall ((var0 Addr) (var1 node) (var2 HeapObject) (var3 Int) (var4 Addr) (var5 Heap)) (or (not (and (inv_main591_13 var5 var4 var3) (and (and (and (= (read var5 var4) var2) (= (getnode var2) var1)) (= (|node::next| var1) var0)) (not (valid var5 var4))))) (inv_main var5 var0 var3))))
(assert (forall ((var0 AllocResHeap) (var1 Addr) (var2 Int) (var3 HeapObject) (var4 node) (var5 Int) (var6 Addr) (var7 Heap)) (or (not (and (inv_main581_5 var7 var6 var5) (and (and (= (O_node var4) var3) (= (node var2 var1) var4)) (= (alloc var7 var3) var0)))) (Inv_Heap_exp_exp (newAddr var0) var2 var1))))
(assert (forall ((var0 Int) (var1 AllocResHeap) (var2 Heap) (var3 HeapObject) (var4 node) (var5 HeapObject) (var6 node) (var7 Int) (var8 Addr) (var9 Heap) (var10 Addr) (var11 Int) (var12 Addr)) (or (not (and (and (Inv_Heap_exp_exp var12 var11 var10) (inv_main581_5 var9 var8 var7)) (and (and (and (and (and (and (= (O_node var6) var5) (= (O_node var4) var3)) (= (AllocResHeap var2 var12) var1)) (= (node var11 var10) var6)) (= (read var2 var12) var5)) (valid var2 var12)) (= (alloc var9 var3) var1)))) (_Glue1 var8 var7 var0 var12 var2 var5))))
(assert (forall ((var0 Int) (var1 AllocResHeap) (var2 HeapObject) (var3 node) (var4 HeapObject) (var5 Addr) (var6 Heap) (var7 Int) (var8 Addr) (var9 Heap)) (or (not (and (inv_main581_5 var9 var8 var7) (and (and (and (and (= (read var6 var5) var4) (not (valid var6 var5))) (= (O_node var3) var2)) (= (AllocResHeap var6 var5) var1)) (= (alloc var9 var2) var1)))) (_Glue1 var8 var7 var0 var5 var6 var4))))
(assert (forall ((var0 Int) (var1 node) (var2 HeapObject) (var3 Heap) (var4 Addr) (var5 Int) (var6 Int) (var7 Addr)) (or (not (and (_Glue1 var7 var6 var5 var4 var3 var2) (and (and (= (getnode var2) var1) (= (|node::hash| var1) var0)) (valid var3 var4)))) (Inv_Heap_exp_exp var4 var0 var7))))
(assert (forall ((var0 node) (var1 Heap) (var2 HeapObject) (var3 node) (var4 Int) (var5 HeapObject) (var6 node) (var7 HeapObject) (var8 Heap) (var9 Int) (var10 Int) (var11 Addr) (var12 Addr) (var13 Int) (var14 Addr)) (or (not (and (and (Inv_Heap_exp_exp var14 var13 var12) (_Glue1 var11 var10 var9 var14 var8 var7)) (and (and (and (and (and (and (and (and (= (O_node var6) var5) (= (node var4 var11) var3)) (= (O_node var3) var2)) (= (node var13 var12) var6)) (= (read var1 var14) var5)) (valid var1 var14)) (= (getnode var7) var0)) (= (|node::hash| var0) var4)) (= (write var8 var14 var2) var1)))) (_Glue3 var1 var10 var9 var14 var5))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Int) (var3 node) (var4 HeapObject) (var5 Heap) (var6 HeapObject) (var7 Heap) (var8 Addr) (var9 Int) (var10 Int) (var11 Addr)) (or (not (and (_Glue1 var11 var10 var9 var8 var7 var6) (and (and (and (and (and (and (= (read var5 var8) var4) (not (valid var5 var8))) (= (getnode var6) var3)) (= (|node::hash| var3) var2)) (= (node var2 var11) var1)) (= (O_node var1) var0)) (= (write var7 var8 var0) var5)))) (_Glue3 var5 var10 var9 var8 var4))))
(assert (forall ((var0 Addr) (var1 node) (var2 HeapObject) (var3 Addr) (var4 Int) (var5 Int) (var6 Heap)) (or (not (and (_Glue3 var6 var5 var4 var3 var2) (and (and (and (and (and (and (= (getnode var2) var1) (= (|node::next| var1) var0)) (<= 0 (+ (+ var4 (* (- 1) var5)) (- 1)))) (<= 0 (+ (+ (+ 100 (* (- 1) var4)) var5) (- 1)))) (<= 0 var5)) (<= 0 (+ 1000000 (* (- 1) var5)))) (valid var6 var3)))) (Inv_Heap_exp_exp var3 var4 var0))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 node) (var3 Addr) (var4 node) (var5 HeapObject) (var6 Addr) (var7 Int) (var8 Int) (var9 Heap)) (or (not (and (_Glue3 var9 var8 var7 var6 var5) (and (and (and (and (and (and (and (and (= (getnode var5) var4) (= (|node::next| var4) var3)) (= (node var7 var3) var2)) (= (O_node var2) var1)) (= (write var9 var6 var1) var0)) (<= 0 (+ (+ var7 (* (- 1) var8)) (- 1)))) (<= 0 (+ (+ (+ 100 (* (- 1) var7)) var8) (- 1)))) (<= 0 var8)) (<= 0 (+ 1000000 (* (- 1) var8)))))) (inv_main581_5 var0 var6 var8))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Int) (var4 Heap) (var5 Addr) (var6 Int) (var7 Addr)) (or (not (and (and (Inv_Heap_exp_exp var7 var6 var5) (inv_main var4 var7 var3)) (and (and (and (and (and (and (and (not (= var2 var7)) (<= 0 (+ (* (- 1) var3) var6))) (<= 0 (+ (+ var3 (* (- 1) var6)) 99))) (= (O_node var1) var0)) (= (node var6 var5) var1)) (= nullAddr var2)) (= (read var4 var7) var0)) (valid var4 var7)))) (inv_main var4 var5 var3))))
(assert (forall ((var0 Addr) (var1 node) (var2 HeapObject) (var3 Int) (var4 Addr) (var5 Int) (var6 Addr) (var7 Heap)) (or (not (and (inv_main var7 var6 var5) (and (and (and (and (and (and (and (and (not (= var4 var6)) (<= 0 (+ (* (- 1) var5) var3))) (<= 0 (+ (+ var5 (* (- 1) var3)) 99))) (= nullAddr var4)) (= (read var7 var6) var2)) (= (getnode var2) var1)) (= (|node::hash| var1) var3)) (= (|node::next| var1) var0)) (not (valid var7 var6))))) (inv_main var7 var0 var5))))
(assert (forall ((var0 Addr) (var1 HeapObject) (var2 node) (var3 Int) (var4 Heap) (var5 Addr) (var6 Int) (var7 Addr)) (or (not (and (and (Inv_Heap_exp_exp var7 var6 var5) (inv_main var4 var7 var3)) (and (and (and (and (and (and (and (= (O_node var2) var1) (= (node var6 var5) var2)) (= nullAddr var0)) (= (read var4 var7) var1)) (not (= var7 var0))) (not (<= 0 (+ (+ (+ 100 (* (- 1) var6)) var3) (- 1))))) (<= 0 (+ var6 (* (- 1) var3)))) (valid var4 var7)))) (inv_main591_13 var4 var7 var3))))
(assert (forall ((var0 Int) (var1 node) (var2 HeapObject) (var3 Addr) (var4 Int) (var5 Addr) (var6 Heap)) (or (not (and (inv_main var6 var5 var4) (and (and (and (and (and (and (and (= nullAddr var3) (= (read var6 var5) var2)) (= (getnode var2) var1)) (= (|node::hash| var1) var0)) (not (= var5 var3))) (not (<= 0 (+ (+ (+ 100 (* (- 1) var0)) var4) (- 1))))) (<= 0 (+ var0 (* (- 1) var4)))) (not (valid var6 var5))))) (inv_main591_13 var6 var5 var4))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap)) (or (not (inv_main581_5 var2 var1 var0)) (inv_main var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Heap) (var2 Addr)) (or (not (and (= nullAddr var2) (= emptyHeap var1))) (inv_main581_5 var1 var2 var0))))
(assert (forall ((var0 Addr) (var1 HeapObject) (var2 node) (var3 Int) (var4 Heap) (var5 Addr) (var6 Int) (var7 Addr)) (or (not (and (and (Inv_Heap_exp_exp var7 var6 var5) (inv_main var4 var7 var3)) (and (and (and (and (and (and (= (O_node var2) var1) (= (node var6 var5) var2)) (not (= var7 var0))) (not (<= 0 (+ var6 (* (- 1) var3))))) (= nullAddr var0)) (= (read var4 var7) var1)) (valid var4 var7)))) (inv_main591_13 var4 var7 var3))))
(assert (forall ((var0 node) (var1 HeapObject) (var2 Int) (var3 Addr) (var4 Int) (var5 Addr) (var6 Heap)) (or (not (and (inv_main var6 var5 var4) (and (and (and (and (and (and (not (= var5 var3)) (not (<= 0 (+ var2 (* (- 1) var4))))) (= nullAddr var3)) (= (read var6 var5) var1)) (= (getnode var1) var0)) (= (|node::hash| var0) var2)) (not (valid var6 var5))))) (inv_main591_13 var6 var5 var4))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap)) (not (inv_main591_13 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap)) (or (not (and (inv_main581_5 var2 var1 var0) (<= 0 (+ var0 (- 1000001))))) (inv_main581_5 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap)) (or (not (and (inv_main581_5 var2 var1 var0) (<= 0 (+ (* (- 1) var0) (- 1))))) (inv_main581_5 var2 var1 var0))))
(check-sat)
