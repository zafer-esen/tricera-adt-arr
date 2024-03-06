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
(declare-fun _Glue2 (Addr Int Addr Heap HeapObject) Bool)
(declare-fun _Glue4 (Heap Addr Int Addr HeapObject) Bool)
(declare-fun inv_main585_7 (Heap Int Addr) Bool)
(declare-fun inv_main602_7 (Heap Addr Int) Bool)
(declare-fun _Glue0 (Int Heap Addr HeapObject) Bool)
(declare-fun _Glue6 (Heap Addr Int Addr HeapObject) Bool)
(declare-fun Inv_Heap (Addr HeapObject) Bool)
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Heap)) (or (not (and (inv_main585_7 var3 var2 var1) (and (not (<= 0 (+ var2 (- 1)))) (= var0 1)))) (inv_main602_7 var3 var1 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Heap)) (not (and (inv_main602_7 var3 var2 var1) (and (and (not (<= 0 var1)) (not (= var0 var2))) (= nullAddr var0))))))
(assert (forall ((var0 AllocResHeap) (var1 HeapObject) (var2 node) (var3 Addr) (var4 Int) (var5 Heap)) (or (not (and (inv_main585_7 var5 (+ var4 1) var3) (and (= (O_node var2) var1) (= (alloc var5 var1) var0)))) (Inv_Heap (newAddr var0) var1))))
(assert (forall ((var0 AllocResHeap) (var1 HeapObject) (var2 node) (var3 Heap) (var4 Addr) (var5 Int) (var6 Heap) (var7 HeapObject) (var8 Addr)) (or (not (and (and (Inv_Heap var8 var7) (inv_main585_7 var6 (+ var5 1) var4)) (and (and (and (and (and (= (read var3 var8) var7) (valid var3 var8)) true) (= (O_node var2) var1)) (= (AllocResHeap var3 var8) var0)) (= (alloc var6 var1) var0)))) (_Glue2 var4 var5 var8 var3 var7))))
(assert (forall ((var0 AllocResHeap) (var1 HeapObject) (var2 node) (var3 HeapObject) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Int) (var8 Heap)) (or (not (and (inv_main585_7 var8 (+ var7 1) var6) (and (and (and (and (= (read var5 var4) var3) (not (valid var5 var4))) (= (O_node var2) var1)) (= (AllocResHeap var5 var4) var0)) (= (alloc var8 var1) var0)))) (_Glue2 var6 var7 var4 var5 var3))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Int) (var4 node) (var5 HeapObject) (var6 Heap) (var7 Addr) (var8 Int) (var9 Addr)) (or (not (and (_Glue2 var9 var8 var7 var6 var5) (and (and (and (and (and (and (and (= (getnode var5) var4) (= (|node::data| var4) var3)) (<= 0 (+ (+ var8 1) (- 1)))) (= nullAddr var2)) (not (= var2 var7))) (= (node var3 var2) var1)) (= (O_node var1) var0)) (valid var6 var7)))) (Inv_Heap var7 var0))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Int) (var4 node) (var5 Heap) (var6 HeapObject) (var7 Heap) (var8 Int) (var9 Addr) (var10 HeapObject) (var11 Addr)) (or (not (and (and (Inv_Heap var11 var10) (_Glue2 var9 var8 var11 var7 var6)) (and (and (and (and (and (and (and (and (and (and (= (read var5 var11) var10) (valid var5 var11)) true) (= (getnode var6) var4)) (= (|node::data| var4) var3)) (<= 0 (+ (+ var8 1) (- 1)))) (= nullAddr var2)) (not (= var2 var11))) (= (node var3 var2) var1)) (= (O_node var1) var0)) (= (write var7 var11 var0) var5)))) (_Glue4 var5 var9 var8 var11 var10))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Int) (var4 node) (var5 HeapObject) (var6 Heap) (var7 HeapObject) (var8 Heap) (var9 Addr) (var10 Int) (var11 Addr)) (or (not (and (_Glue2 var11 var10 var9 var8 var7) (and (and (and (and (and (and (and (and (and (= (read var6 var9) var5) (not (valid var6 var9))) (= (getnode var7) var4)) (= (|node::data| var4) var3)) (<= 0 (+ (+ var10 1) (- 1)))) (= nullAddr var2)) (not (= var2 var9))) (= (node var3 var2) var1)) (= (O_node var1) var0)) (= (write var8 var9 var0) var6)))) (_Glue4 var6 var11 var10 var9 var5))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 node) (var4 HeapObject) (var5 Addr) (var6 Int) (var7 Addr) (var8 Heap)) (or (not (and (_Glue4 var8 var7 var6 var5 var4) (and (and (and (and (= (getnode var4) var3) (= (|node::next| var3) var2)) (= (node 1 var2) var1)) (= (O_node var1) var0)) (valid var8 var5)))) (Inv_Heap var5 var0))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 node) (var4 Heap) (var5 HeapObject) (var6 Int) (var7 Addr) (var8 Heap) (var9 HeapObject) (var10 Addr)) (or (not (and (and (Inv_Heap var10 var9) (_Glue4 var8 var7 var6 var10 var5)) (and (and (and (and (and (and (and (= (read var4 var10) var9) (valid var4 var10)) true) (= (getnode var5) var3)) (= (|node::next| var3) var2)) (= (node 1 var2) var1)) (= (O_node var1) var0)) (= (write var8 var10 var0) var4)))) (_Glue6 var4 var7 var6 var10 var9))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 node) (var4 HeapObject) (var5 Heap) (var6 HeapObject) (var7 Addr) (var8 Int) (var9 Addr) (var10 Heap)) (or (not (and (_Glue4 var10 var9 var8 var7 var6) (and (and (and (and (and (and (= (read var5 var7) var4) (not (valid var5 var7))) (= (getnode var6) var3)) (= (|node::next| var3) var2)) (= (node 1 var2) var1)) (= (O_node var1) var0)) (= (write var10 var7 var0) var5)))) (_Glue6 var5 var9 var8 var7 var4))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Int) (var3 node) (var4 HeapObject) (var5 Addr) (var6 Int) (var7 Addr) (var8 Heap)) (or (not (and (_Glue6 var8 var7 var6 var5 var4) (and (and (and (and (= (getnode var4) var3) (= (|node::data| var3) var2)) (= (node var2 var7) var1)) (= (O_node var1) var0)) (valid var8 var5)))) (Inv_Heap var5 var0))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 node) (var3 Int) (var4 node) (var5 HeapObject) (var6 Addr) (var7 Int) (var8 Addr) (var9 Heap)) (or (not (and (_Glue6 var9 var8 var7 var6 var5) (and (and (and (and (= (getnode var5) var4) (= (|node::data| var4) var3)) (= (node var3 var8) var2)) (= (O_node var2) var1)) (= (write var9 var6 var1) var0)))) (inv_main585_7 var0 var7 var6))))
(assert (forall ((var0 Int) (var1 Heap) (var2 HeapObject) (var3 Addr)) (or (not (and (and (Inv_Heap var3 var2) (inv_main602_7 var1 var3 (+ var0 1))) (and (= (read var1 var3) var2) (valid var1 var3)))) (_Glue0 var0 var1 var3 var2))))
(assert (forall ((var0 HeapObject) (var1 Int) (var2 Addr) (var3 Heap)) (or (not (and (inv_main602_7 var3 var2 (+ var1 1)) (and (= (read var3 var2) var0) (not (valid var3 var2))))) (_Glue0 var1 var3 var2 var0))))
(assert (forall ((var0 HeapObject) (var1 HeapObject) (var2 Addr) (var3 Heap) (var4 Int)) (or (not (and (_Glue0 var4 var3 var2 var1) (and (and (<= 0 (+ var4 1)) (= defObj var0)) (valid var3 var2)))) (Inv_Heap var2 var0))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 Addr) (var3 node) (var4 HeapObject) (var5 Addr) (var6 Heap) (var7 Int)) (or (not (and (_Glue0 var7 var6 var5 var4) (and (and (and (and (= (getnode var4) var3) (= (|node::next| var3) var2)) (<= 0 (+ var7 1))) (= defObj var1)) (= (write var6 var5 var1) var0)))) (inv_main602_7 var0 var2 var7))))
(assert (forall ((var0 Int) (var1 Heap) (var2 Addr)) (or (not (and (and (= nullAddr var2) (= emptyHeap var1)) (= var0 2))) (inv_main585_7 var1 var0 var2))))
(check-sat)
