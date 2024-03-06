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
(declare-fun Inv_Heap (Addr HeapObject) Bool)
(declare-fun _Glue6 (Heap Addr Int Addr HeapObject) Bool)
(declare-fun inv_main613_5 (Heap Addr Int) Bool)
(declare-fun inv_main598_5 (Heap Addr Int Addr Addr) Bool)
(declare-fun inv_main585_7 (Heap Int Addr) Bool)
(declare-fun _Glue21 (Addr Addr Heap HeapObject) Bool)
(declare-fun _Glue23 (Int Addr Heap HeapObject) Bool)
(declare-fun _Glue4 (Heap Addr Int Addr HeapObject) Bool)
(declare-fun _Glue14 (Int Addr Heap HeapObject) Bool)
(declare-fun _Glue19 (Int Addr Heap HeapObject) Bool)
(declare-fun _Glue16 (Heap Addr HeapObject) Bool)
(declare-fun _Glue12 (Addr Int Heap Addr HeapObject) Bool)
(declare-fun _Glue28 (Addr Heap Addr HeapObject) Bool)
(declare-fun _Glue26 (Addr Heap Addr Int Addr Addr Int HeapObject) Bool)
(declare-fun _Glue25 (Addr Addr Int Addr Heap Addr HeapObject) Bool)
(declare-fun _Glue8 (Int Addr Heap HeapObject) Bool)
(declare-fun _Glue10 (Heap Addr HeapObject) Bool)
(declare-fun _Glue2 (Addr Int Addr Heap HeapObject) Bool)
(assert (forall ((var0 AllocResHeap) (var1 HeapObject) (var2 node) (var3 Addr) (var4 Int) (var5 Heap)) (or (not (and (inv_main585_7 var5 var4 var3) (and (= (O_node var2) var1) (= (alloc var5 var1) var0)))) (Inv_Heap (newAddr var0) var1))))
(assert (forall ((var0 AllocResHeap) (var1 HeapObject) (var2 node) (var3 Heap) (var4 Addr) (var5 Int) (var6 Heap) (var7 HeapObject) (var8 Addr)) (or (not (and (and (Inv_Heap var8 var7) (inv_main585_7 var6 var5 var4)) (and (and (and (and (and (= (read var3 var8) var7) (valid var3 var8)) true) (= (O_node var2) var1)) (= (AllocResHeap var3 var8) var0)) (= (alloc var6 var1) var0)))) (_Glue8 var5 var8 var3 var7))))
(assert (forall ((var0 AllocResHeap) (var1 HeapObject) (var2 node) (var3 HeapObject) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Int) (var8 Heap)) (or (not (and (inv_main585_7 var8 var7 var6) (and (and (and (and (= (read var5 var4) var3) (not (valid var5 var4))) (= (O_node var2) var1)) (= (AllocResHeap var5 var4) var0)) (= (alloc var8 var1) var0)))) (_Glue8 var7 var4 var5 var3))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Int) (var4 node) (var5 HeapObject) (var6 Heap) (var7 Addr) (var8 Int)) (or (not (and (_Glue8 var8 var7 var6 var5) (and (and (and (and (and (and (and (and (is-O_node var5) (= (getnode var5) var4)) (= (|node::data| var4) var3)) (<= 0 (+ var8 (- 1)))) (= nullAddr var2)) (not (= var2 var7))) (= (node var3 var2) var1)) (= (O_node var1) var0)) (valid var6 var7)))) (Inv_Heap var7 var0))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Int) (var4 node) (var5 Heap) (var6 HeapObject) (var7 Heap) (var8 Int) (var9 HeapObject) (var10 Addr)) (or (not (and (and (Inv_Heap var10 var9) (_Glue8 var8 var10 var7 var6)) (and (and (and (and (and (and (and (and (and (and (and (= (read var5 var10) var9) (valid var5 var10)) true) (is-O_node var6)) (= (getnode var6) var4)) (= (|node::data| var4) var3)) (<= 0 (+ var8 (- 1)))) (= nullAddr var2)) (not (= var2 var10))) (= (node var3 var2) var1)) (= (O_node var1) var0)) (= (write var7 var10 var0) var5)))) (_Glue10 var5 var10 var9))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Int) (var4 node) (var5 HeapObject) (var6 Heap) (var7 HeapObject) (var8 Heap) (var9 Addr) (var10 Int)) (or (not (and (_Glue8 var10 var9 var8 var7) (and (and (and (and (and (and (and (and (and (and (= (read var6 var9) var5) (not (valid var6 var9))) (is-O_node var7)) (= (getnode var7) var4)) (= (|node::data| var4) var3)) (<= 0 (+ var10 (- 1)))) (= nullAddr var2)) (not (= var2 var9))) (= (node var3 var2) var1)) (= (O_node var1) var0)) (= (write var8 var9 var0) var6)))) (_Glue10 var6 var9 var5))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 node) (var4 HeapObject) (var5 Addr) (var6 Heap)) (or (not (and (_Glue10 var6 var5 var4) (and (and (and (and (and (is-O_node var4) (= (getnode var4) var3)) (= (|node::next| var3) var2)) (= (node 1 var2) var1)) (= (O_node var1) var0)) (valid var6 var5)))) (Inv_Heap var5 var0))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 node) (var4 Heap) (var5 HeapObject) (var6 Heap) (var7 HeapObject) (var8 Addr)) (not (and (and (Inv_Heap var8 var7) (_Glue10 var6 var8 var5)) (and (and (and (and (and (and (and (and (and (= (read var4 var8) var7) (not (is-O_node var7))) (valid var4 var8)) true) (is-O_node var5)) (= (getnode var5) var3)) (= (|node::next| var3) var2)) (= (node 1 var2) var1)) (= (O_node var1) var0)) (= (write var6 var8 var0) var4))))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 node) (var4 HeapObject) (var5 Heap) (var6 HeapObject) (var7 Addr) (var8 Heap)) (not (and (_Glue10 var8 var7 var6) (and (and (and (and (and (and (and (and (= (read var5 var7) var4) (not (is-O_node var4))) (not (valid var5 var7))) (is-O_node var6)) (= (getnode var6) var3)) (= (|node::next| var3) var2)) (= (node 1 var2) var1)) (= (O_node var1) var0)) (= (write var8 var7 var0) var5))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Heap) (var3 HeapObject) (var4 Addr)) (or (not (and (and (Inv_Heap var4 var3) (inv_main613_5 var2 var4 (+ var1 1))) (and (and (= nullAddr var0) (= (read var2 var4) var3)) (valid var2 var4)))) (_Glue12 var0 var1 var2 var4 var3))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Int) (var3 Addr) (var4 Heap)) (or (not (and (inv_main613_5 var4 var3 (+ var2 1)) (and (and (= nullAddr var1) (= (read var4 var3) var0)) (not (valid var4 var3))))) (_Glue12 var1 var2 var4 var3 var0))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 HeapObject) (var3 Addr) (var4 Heap) (var5 Int) (var6 Addr)) (or (not (and (_Glue12 var6 var5 var4 var3 var2) (and (and (and (and (and (is-O_node var2) (= (getnode var2) var1)) (= (|node::next| var1) var6)) (<= 0 (+ (+ var5 1) (- 1)))) (= defObj var0)) (valid var4 var3)))) (Inv_Heap var3 var0))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 node) (var3 HeapObject) (var4 Addr) (var5 Heap) (var6 Int) (var7 Addr)) (or (not (and (_Glue12 var7 var6 var5 var4 var3) (and (and (and (and (and (is-O_node var3) (= (getnode var3) var2)) (= (|node::next| var2) var7)) (<= 0 (+ (+ var6 1) (- 1)))) (= defObj var1)) (= (write var5 var4 var1) var0)))) (inv_main613_5 var0 var7 var6))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 node) (var3 Addr) (var4 Int) (var5 Addr) (var6 Heap) (var7 HeapObject) (var8 Addr)) (or (not (and (and (Inv_Heap var8 var7) (inv_main598_5 var6 var5 var4 var3 var8)) (and (and (and (and (and (and (is-O_node var7) (= (read var6 var8) var7)) (= (getnode var7) var2)) (= (|node::next| var2) var1)) (= nullAddr var0)) (not (= var1 var0))) (valid var6 var8)))) (inv_main598_5 var6 var5 var4 var8 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 node) (var3 HeapObject) (var4 Addr) (var5 Addr) (var6 Int) (var7 Addr) (var8 Heap)) (or (not (and (inv_main598_5 var8 var7 var6 var5 var4) (and (and (and (and (and (and (is-O_node var3) (= (read var8 var4) var3)) (= (getnode var3) var2)) (= (|node::next| var2) var1)) (= nullAddr var0)) (not (= var1 var0))) (not (valid var8 var4))))) (inv_main598_5 var8 var7 var6 var4 var1))))
(assert (forall ((var0 AllocResHeap) (var1 HeapObject) (var2 node) (var3 Addr) (var4 Int) (var5 Heap)) (or (not (and (inv_main585_7 var5 (+ var4 1) var3) (and (= (O_node var2) var1) (= (alloc var5 var1) var0)))) (Inv_Heap (newAddr var0) var1))))
(assert (forall ((var0 AllocResHeap) (var1 HeapObject) (var2 node) (var3 Heap) (var4 Addr) (var5 Int) (var6 Heap) (var7 HeapObject) (var8 Addr)) (or (not (and (and (Inv_Heap var8 var7) (inv_main585_7 var6 (+ var5 1) var4)) (and (and (and (and (and (= (read var3 var8) var7) (valid var3 var8)) true) (= (O_node var2) var1)) (= (AllocResHeap var3 var8) var0)) (= (alloc var6 var1) var0)))) (_Glue2 var4 var5 var8 var3 var7))))
(assert (forall ((var0 AllocResHeap) (var1 HeapObject) (var2 node) (var3 HeapObject) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Int) (var8 Heap)) (or (not (and (inv_main585_7 var8 (+ var7 1) var6) (and (and (and (and (= (read var5 var4) var3) (not (valid var5 var4))) (= (O_node var2) var1)) (= (AllocResHeap var5 var4) var0)) (= (alloc var8 var1) var0)))) (_Glue2 var6 var7 var4 var5 var3))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Int) (var4 node) (var5 HeapObject) (var6 Heap) (var7 Addr) (var8 Int) (var9 Addr)) (or (not (and (_Glue2 var9 var8 var7 var6 var5) (and (and (and (and (and (and (and (and (is-O_node var5) (= (getnode var5) var4)) (= (|node::data| var4) var3)) (<= 0 (+ (+ var8 1) (- 1)))) (= nullAddr var2)) (not (= var2 var7))) (= (node var3 var2) var1)) (= (O_node var1) var0)) (valid var6 var7)))) (Inv_Heap var7 var0))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Int) (var4 node) (var5 Heap) (var6 HeapObject) (var7 Heap) (var8 Int) (var9 Addr) (var10 HeapObject) (var11 Addr)) (or (not (and (and (Inv_Heap var11 var10) (_Glue2 var9 var8 var11 var7 var6)) (and (and (and (and (and (and (and (and (and (and (and (= (read var5 var11) var10) (valid var5 var11)) true) (is-O_node var6)) (= (getnode var6) var4)) (= (|node::data| var4) var3)) (<= 0 (+ (+ var8 1) (- 1)))) (= nullAddr var2)) (not (= var2 var11))) (= (node var3 var2) var1)) (= (O_node var1) var0)) (= (write var7 var11 var0) var5)))) (_Glue4 var5 var9 var8 var11 var10))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Int) (var4 node) (var5 HeapObject) (var6 Heap) (var7 HeapObject) (var8 Heap) (var9 Addr) (var10 Int) (var11 Addr)) (or (not (and (_Glue2 var11 var10 var9 var8 var7) (and (and (and (and (and (and (and (and (and (and (= (read var6 var9) var5) (not (valid var6 var9))) (is-O_node var7)) (= (getnode var7) var4)) (= (|node::data| var4) var3)) (<= 0 (+ (+ var10 1) (- 1)))) (= nullAddr var2)) (not (= var2 var9))) (= (node var3 var2) var1)) (= (O_node var1) var0)) (= (write var8 var9 var0) var6)))) (_Glue4 var6 var11 var10 var9 var5))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 node) (var4 HeapObject) (var5 Addr) (var6 Int) (var7 Addr) (var8 Heap)) (or (not (and (_Glue4 var8 var7 var6 var5 var4) (and (and (and (and (and (is-O_node var4) (= (getnode var4) var3)) (= (|node::next| var3) var2)) (= (node 1 var2) var1)) (= (O_node var1) var0)) (valid var8 var5)))) (Inv_Heap var5 var0))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 node) (var4 Heap) (var5 HeapObject) (var6 Int) (var7 Addr) (var8 Heap) (var9 HeapObject) (var10 Addr)) (or (not (and (and (Inv_Heap var10 var9) (_Glue4 var8 var7 var6 var10 var5)) (and (and (and (and (and (and (and (and (= (read var4 var10) var9) (valid var4 var10)) true) (is-O_node var5)) (= (getnode var5) var3)) (= (|node::next| var3) var2)) (= (node 1 var2) var1)) (= (O_node var1) var0)) (= (write var8 var10 var0) var4)))) (_Glue6 var4 var7 var6 var10 var9))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 node) (var4 HeapObject) (var5 Heap) (var6 HeapObject) (var7 Addr) (var8 Int) (var9 Addr) (var10 Heap)) (or (not (and (_Glue4 var10 var9 var8 var7 var6) (and (and (and (and (and (and (and (= (read var5 var7) var4) (not (valid var5 var7))) (is-O_node var6)) (= (getnode var6) var3)) (= (|node::next| var3) var2)) (= (node 1 var2) var1)) (= (O_node var1) var0)) (= (write var10 var7 var0) var5)))) (_Glue6 var5 var9 var8 var7 var4))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Int) (var3 node) (var4 HeapObject) (var5 Addr) (var6 Int) (var7 Addr) (var8 Heap)) (or (not (and (_Glue6 var8 var7 var6 var5 var4) (and (and (and (and (and (is-O_node var4) (= (getnode var4) var3)) (= (|node::data| var3) var2)) (= (node var2 var7) var1)) (= (O_node var1) var0)) (valid var8 var5)))) (Inv_Heap var5 var0))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 node) (var3 Int) (var4 node) (var5 HeapObject) (var6 Addr) (var7 Int) (var8 Addr) (var9 Heap)) (or (not (and (_Glue6 var9 var8 var7 var6 var5) (and (and (and (and (and (is-O_node var5) (= (getnode var5) var4)) (= (|node::data| var4) var3)) (= (node var3 var8) var2)) (= (O_node var2) var1)) (= (write var9 var6 var1) var0)))) (inv_main585_7 var0 var7 var6))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Heap) (var5 HeapObject) (var6 Addr)) (or (not (and (and (Inv_Heap var6 var5) (inv_main598_5 var4 var3 var2 var1 var6)) (and (and (= nullAddr var0) (= (read var4 var6) var5)) (valid var4 var6)))) (_Glue21 var0 var1 var4 var5))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Addr) (var6 Heap)) (or (not (and (inv_main598_5 var6 var5 var4 var3 var2) (and (and (= nullAddr var1) (= (read var6 var2) var0)) (not (valid var6 var2))))) (_Glue21 var1 var3 var6 var0))))
(assert (forall ((var0 node) (var1 HeapObject) (var2 Heap) (var3 Addr) (var4 HeapObject) (var5 Addr)) (not (and (and (Inv_Heap var5 var4) (_Glue21 var3 var5 var2 var1)) (and (and (and (and (and (is-O_node var1) (= (getnode var1) var0)) (= (|node::next| var0) var3)) (= (read var2 var5) var4)) (not (is-O_node var4))) (valid var2 var5))))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 HeapObject) (var3 Heap) (var4 Addr) (var5 Addr)) (not (and (_Glue21 var5 var4 var3 var2) (and (and (and (and (and (is-O_node var2) (= (getnode var2) var1)) (= (|node::next| var1) var5)) (= (read var3 var4) var0)) (not (is-O_node var0))) (not (valid var3 var4)))))))
(assert (forall ((var0 AllocResHeap) (var1 HeapObject) (var2 node) (var3 Addr) (var4 Int) (var5 Heap)) (or (not (and (inv_main585_7 var5 var4 var3) (and (and (not (= 4 4)) (= (O_node var2) var1)) (= (alloc var5 var1) var0)))) (Inv_Heap (newAddr var0) var1))))
(assert (forall ((var0 AllocResHeap) (var1 HeapObject) (var2 node) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Int) (var7 Heap) (var8 HeapObject) (var9 Addr)) (not (and (and (Inv_Heap var9 var8) (inv_main585_7 var7 var6 var5)) (and (and (and (and (and (and (and (and (and (and (not (= var4 var9)) (= (read var3 var9) var8)) (is-O_node var8)) (<= 0 (+ var6 (- 1)))) (valid var3 var9)) true) (= (O_node var2) var1)) (= (AllocResHeap var3 var9) var0)) (not (= 4 4))) (= nullAddr var4)) (= (alloc var7 var1) var0))))))
(assert (forall ((var0 AllocResHeap) (var1 HeapObject) (var2 node) (var3 HeapObject) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Int) (var9 Heap)) (not (and (inv_main585_7 var9 var8 var7) (and (and (and (and (and (and (and (and (and (not (= var6 var5)) (= (read var4 var5) var3)) (is-O_node var3)) (<= 0 (+ var8 (- 1)))) (not (valid var4 var5))) (= (O_node var2) var1)) (= (AllocResHeap var4 var5) var0)) (not (= 4 4))) (= nullAddr var6)) (= (alloc var9 var1) var0))))))
(assert (forall ((var0 Addr) (var1 node) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap) (var6 HeapObject) (var7 Addr)) (or (not (and (and (Inv_Heap var7 var6) (inv_main613_5 var5 var7 var4)) (and (and (and (and (and (and (and (not (= var3 var2)) (is-O_node var6)) (= nullAddr var3)) (= (read var5 var7) var6)) (= (getnode var6) var1)) (= (|node::next| var1) var2)) (valid var5 var7)) (= var0 var7)))) (inv_main598_5 var5 var0 var4 var3 var7))))
(assert (forall ((var0 Addr) (var1 node) (var2 HeapObject) (var3 Addr) (var4 Addr) (var5 Int) (var6 Addr) (var7 Heap)) (or (not (and (inv_main613_5 var7 var6 var5) (and (and (and (and (and (and (and (not (= var4 var3)) (is-O_node var2)) (= nullAddr var4)) (= (read var7 var6) var2)) (= (getnode var2) var1)) (= (|node::next| var1) var3)) (not (valid var7 var6))) (= var0 var6)))) (inv_main598_5 var7 var0 var5 var4 var6))))
(assert (forall ((var0 Int) (var1 Heap) (var2 Addr)) (or (not (and (and (= nullAddr var2) (= emptyHeap var1)) (= var0 2))) (inv_main585_7 var1 var0 var2))))
(assert (forall ((var0 AllocResHeap) (var1 HeapObject) (var2 node) (var3 Addr) (var4 Int) (var5 Heap)) (or (not (and (inv_main585_7 var5 var4 var3) (and (= (O_node var2) var1) (= (alloc var5 var1) var0)))) (Inv_Heap (newAddr var0) var1))))
(assert (forall ((var0 AllocResHeap) (var1 HeapObject) (var2 node) (var3 Heap) (var4 Addr) (var5 Int) (var6 Heap) (var7 HeapObject) (var8 Addr)) (or (not (and (and (Inv_Heap var8 var7) (inv_main585_7 var6 var5 var4)) (and (and (and (and (and (= (read var3 var8) var7) (valid var3 var8)) true) (= (O_node var2) var1)) (= (AllocResHeap var3 var8) var0)) (= (alloc var6 var1) var0)))) (_Glue19 var5 var8 var3 var7))))
(assert (forall ((var0 AllocResHeap) (var1 HeapObject) (var2 node) (var3 HeapObject) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Int) (var8 Heap)) (or (not (and (inv_main585_7 var8 var7 var6) (and (and (and (and (= (read var5 var4) var3) (not (valid var5 var4))) (= (O_node var2) var1)) (= (AllocResHeap var5 var4) var0)) (= (alloc var8 var1) var0)))) (_Glue19 var7 var4 var5 var3))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Int) (var4 node) (var5 HeapObject) (var6 Heap) (var7 Addr) (var8 Int)) (or (not (and (_Glue19 var8 var7 var6 var5) (and (and (and (and (and (and (and (and (is-O_node var5) (= (getnode var5) var4)) (= (|node::data| var4) var3)) (<= 0 (+ var8 (- 1)))) (= nullAddr var2)) (not (= var2 var7))) (= (node var3 var2) var1)) (= (O_node var1) var0)) (valid var6 var7)))) (Inv_Heap var7 var0))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Int) (var4 node) (var5 Heap) (var6 HeapObject) (var7 Heap) (var8 Int) (var9 HeapObject) (var10 Addr)) (not (and (and (Inv_Heap var10 var9) (_Glue19 var8 var10 var7 var6)) (and (and (and (and (and (and (and (and (and (and (and (and (= (read var5 var10) var9) (not (is-O_node var9))) (valid var5 var10)) true) (is-O_node var6)) (= (getnode var6) var4)) (= (|node::data| var4) var3)) (<= 0 (+ var8 (- 1)))) (= nullAddr var2)) (not (= var2 var10))) (= (node var3 var2) var1)) (= (O_node var1) var0)) (= (write var7 var10 var0) var5))))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Int) (var4 node) (var5 HeapObject) (var6 Heap) (var7 HeapObject) (var8 Heap) (var9 Addr) (var10 Int)) (not (and (_Glue19 var10 var9 var8 var7) (and (and (and (and (and (and (and (and (and (and (and (= (read var6 var9) var5) (not (is-O_node var5))) (not (valid var6 var9))) (is-O_node var7)) (= (getnode var7) var4)) (= (|node::data| var4) var3)) (<= 0 (+ var10 (- 1)))) (= nullAddr var2)) (not (= var2 var9))) (= (node var3 var2) var1)) (= (O_node var1) var0)) (= (write var8 var9 var0) var6))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Heap) (var5 HeapObject) (var6 Addr)) (or (not (and (and (Inv_Heap var6 var5) (inv_main598_5 var4 var3 var2 var6 var1)) (and (and (and (not (= 4 4)) (= nullAddr var0)) (= (read var4 var6) var5)) (valid var4 var6)))) (_Glue28 var0 var4 var1 var5))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Addr) (var6 Heap)) (or (not (and (inv_main598_5 var6 var5 var4 var3 var2) (and (and (and (not (= 4 4)) (= nullAddr var1)) (= (read var6 var3) var0)) (not (valid var6 var3))))) (_Glue28 var1 var6 var2 var0))))
(assert (forall ((var0 node) (var1 HeapObject) (var2 Heap) (var3 Addr) (var4 HeapObject) (var5 Addr)) (not (and (and (Inv_Heap var5 var4) (_Glue28 var3 var2 var5 var1)) (and (and (and (and (and (is-O_node var1) (= (read var2 var5) var4)) (is-O_node var4)) (= (getnode var4) var0)) (= (|node::next| var0) var3)) (valid var2 var5))))))
(assert (forall ((var0 node) (var1 HeapObject) (var2 HeapObject) (var3 Addr) (var4 Heap) (var5 Addr)) (not (and (_Glue28 var5 var4 var3 var2) (and (and (and (and (and (is-O_node var2) (= (read var4 var3) var1)) (is-O_node var1)) (= (getnode var1) var0)) (= (|node::next| var0) var5)) (not (valid var4 var3)))))))
(assert (forall ((var0 AllocResHeap) (var1 HeapObject) (var2 node) (var3 Addr) (var4 Int) (var5 Heap)) (or (not (and (inv_main585_7 var5 var4 var3) (and (and (not (= 4 4)) (= (O_node var2) var1)) (= (alloc var5 var1) var0)))) (Inv_Heap (newAddr var0) var1))))
(assert (forall ((var0 AllocResHeap) (var1 HeapObject) (var2 node) (var3 Heap) (var4 Addr) (var5 Int) (var6 Heap) (var7 HeapObject) (var8 Addr)) (or (not (and (and (Inv_Heap var8 var7) (inv_main585_7 var6 var5 var4)) (and (and (and (and (and (and (= (read var3 var8) var7) (valid var3 var8)) true) (= (O_node var2) var1)) (= (AllocResHeap var3 var8) var0)) (not (= 4 4))) (= (alloc var6 var1) var0)))) (_Glue23 var5 var8 var3 var7))))
(assert (forall ((var0 AllocResHeap) (var1 HeapObject) (var2 node) (var3 HeapObject) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Int) (var8 Heap)) (or (not (and (inv_main585_7 var8 var7 var6) (and (and (and (and (and (= (read var5 var4) var3) (not (valid var5 var4))) (= (O_node var2) var1)) (= (AllocResHeap var5 var4) var0)) (not (= 4 4))) (= (alloc var8 var1) var0)))) (_Glue23 var7 var4 var5 var3))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Int) (var4 node) (var5 HeapObject) (var6 Heap) (var7 Addr) (var8 Int)) (or (not (and (_Glue23 var8 var7 var6 var5) (and (and (and (and (and (and (and (and (is-O_node var5) (= (getnode var5) var4)) (= (|node::data| var4) var3)) (<= 0 (+ var8 (- 1)))) (= nullAddr var2)) (not (= var2 var7))) (= (node var3 var2) var1)) (= (O_node var1) var0)) (valid var6 var7)))) (Inv_Heap var7 var0))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Int) (var4 node) (var5 Heap) (var6 HeapObject) (var7 Heap) (var8 Int) (var9 HeapObject) (var10 Addr)) (not (and (and (Inv_Heap var10 var9) (_Glue23 var8 var10 var7 var6)) (and (and (and (and (and (and (and (and (and (and (and (and (= (read var5 var10) var9) (is-O_node var9)) (valid var5 var10)) true) (is-O_node var6)) (= (getnode var6) var4)) (= (|node::data| var4) var3)) (<= 0 (+ var8 (- 1)))) (= nullAddr var2)) (not (= var2 var10))) (= (node var3 var2) var1)) (= (O_node var1) var0)) (= (write var7 var10 var0) var5))))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Int) (var4 node) (var5 HeapObject) (var6 Heap) (var7 HeapObject) (var8 Heap) (var9 Addr) (var10 Int)) (not (and (_Glue23 var10 var9 var8 var7) (and (and (and (and (and (and (and (and (and (and (and (= (read var6 var9) var5) (is-O_node var5)) (not (valid var6 var9))) (is-O_node var7)) (= (getnode var7) var4)) (= (|node::data| var4) var3)) (<= 0 (+ var10 (- 1)))) (= nullAddr var2)) (not (= var2 var9))) (= (node var3 var2) var1)) (= (O_node var1) var0)) (= (write var8 var9 var0) var6))))))
(assert (forall ((var0 AllocResHeap) (var1 HeapObject) (var2 node) (var3 Addr) (var4 Int) (var5 Heap)) (or (not (and (inv_main585_7 var5 var4 var3) (and (= (O_node var2) var1) (= (alloc var5 var1) var0)))) (Inv_Heap (newAddr var0) var1))))
(assert (forall ((var0 AllocResHeap) (var1 HeapObject) (var2 node) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Int) (var7 Heap) (var8 HeapObject) (var9 Addr)) (not (and (and (Inv_Heap var9 var8) (inv_main585_7 var7 var6 var5)) (and (and (and (and (and (and (and (and (and (not (= var4 var9)) (= (read var3 var9) var8)) (not (is-O_node var8))) (<= 0 (+ var6 (- 1)))) (valid var3 var9)) true) (= (O_node var2) var1)) (= (AllocResHeap var3 var9) var0)) (= nullAddr var4)) (= (alloc var7 var1) var0))))))
(assert (forall ((var0 AllocResHeap) (var1 HeapObject) (var2 node) (var3 HeapObject) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Int) (var9 Heap)) (not (and (inv_main585_7 var9 var8 var7) (and (and (and (and (and (and (and (and (not (= var6 var5)) (= (read var4 var5) var3)) (not (is-O_node var3))) (<= 0 (+ var8 (- 1)))) (not (valid var4 var5))) (= (O_node var2) var1)) (= (AllocResHeap var4 var5) var0)) (= nullAddr var6)) (= (alloc var9 var1) var0))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 node) (var3 Addr) (var4 Int) (var5 Addr) (var6 Heap) (var7 HeapObject) (var8 Addr)) (not (and (and (Inv_Heap var8 var7) (inv_main598_5 var6 var5 var4 var3 var8)) (and (and (and (and (and (and (and (= (read var6 var8) var7) (is-O_node var7)) (= (getnode var7) var2)) (= (|node::next| var2) var1)) (= nullAddr var0)) (not (= 4 4))) (not (= var1 var0))) (valid var6 var8))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 node) (var3 HeapObject) (var4 Addr) (var5 Addr) (var6 Int) (var7 Addr) (var8 Heap)) (not (and (inv_main598_5 var8 var7 var6 var5 var4) (and (and (and (and (and (and (and (= (read var8 var4) var3) (is-O_node var3)) (= (getnode var3) var2)) (= (|node::next| var2) var1)) (= nullAddr var0)) (not (= 4 4))) (not (= var1 var0))) (not (valid var8 var4)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Heap) (var4 HeapObject) (var5 Addr)) (not (and (and (Inv_Heap var5 var4) (inv_main598_5 var3 var2 var1 var0 var5)) (and (and (not (is-O_node var4)) (= (read var3 var5) var4)) (valid var3 var5))))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Int) (var4 Addr) (var5 Heap)) (not (and (inv_main598_5 var5 var4 var3 var2 var1) (and (and (not (is-O_node var0)) (= (read var5 var1) var0)) (not (valid var5 var1)))))))
(assert (forall ((var0 Int) (var1 Heap) (var2 HeapObject) (var3 Addr)) (not (and (and (Inv_Heap var3 var2) (inv_main613_5 var1 var3 var0)) (and (and (not (is-O_node var2)) (= (read var1 var3) var2)) (valid var1 var3))))))
(assert (forall ((var0 HeapObject) (var1 Int) (var2 Addr) (var3 Heap)) (not (and (inv_main613_5 var3 var2 var1) (and (and (not (is-O_node var0)) (= (read var3 var2) var0)) (not (valid var3 var2)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Heap) (var5 HeapObject) (var6 Addr)) (or (not (and (and (Inv_Heap var6 var5) (inv_main598_5 var4 var3 (+ var2 1) var6 var1)) (and (and (= nullAddr var0) (= (read var4 var6) var5)) (valid var4 var6)))) (_Glue25 var0 var3 var2 var1 var4 var6 var5))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Addr) (var6 Heap)) (or (not (and (inv_main598_5 var6 var5 (+ var4 1) var3 var2) (and (and (= nullAddr var1) (= (read var6 var3) var0)) (not (valid var6 var3))))) (_Glue25 var1 var5 var4 var2 var6 var3 var0))))
(assert (forall ((var0 Int) (var1 node) (var2 HeapObject) (var3 Addr) (var4 Heap) (var5 Int) (var6 Addr) (var7 Addr) (var8 HeapObject) (var9 Addr)) (or (not (and (and (Inv_Heap var9 var8) (_Glue25 var7 var6 var5 var9 var4 var3 var2)) (and (and (and (and (is-O_node var2) (= (getnode var2) var1)) (= (|node::data| var1) var0)) (= (read var4 var9) var8)) (valid var4 var9)))) (_Glue26 var3 var4 var9 var5 var6 var7 var0 var8))))
(assert (forall ((var0 HeapObject) (var1 Int) (var2 node) (var3 HeapObject) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Int) (var8 Addr) (var9 Addr)) (or (not (and (_Glue25 var9 var8 var7 var6 var5 var4 var3) (and (and (and (and (is-O_node var3) (= (getnode var3) var2)) (= (|node::data| var2) var1)) (= (read var5 var6) var0)) (not (valid var5 var6))))) (_Glue26 var4 var5 var6 var7 var8 var9 var1 var0))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 node) (var4 HeapObject) (var5 Int) (var6 Addr) (var7 Addr) (var8 Int) (var9 Addr) (var10 Heap) (var11 Addr)) (or (not (and (_Glue26 var11 var10 var9 var8 var7 var6 var5 var4) (and (and (and (and (and (and (and (is-O_node var4) (= (getnode var4) var3)) (= (|node::next| var3) var6)) (<= 0 (+ (+ var8 1) (- 1)))) (= nullAddr var2)) (= (node var5 var2) var1)) (= (O_node var1) var0)) (valid var10 var11)))) (Inv_Heap var11 var0))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 node) (var4 Heap) (var5 HeapObject) (var6 HeapObject) (var7 Int) (var8 Addr) (var9 Addr) (var10 Int) (var11 Addr) (var12 Heap) (var13 Addr)) (or (not (and (_Glue26 var13 var12 var11 var10 var9 var8 var7 var6) (and (and (and (and (and (and (and (and (and (= defObj var5) (valid var4 var11)) (is-O_node var6)) (= (getnode var6) var3)) (= (|node::next| var3) var8)) (<= 0 (+ (+ var10 1) (- 1)))) (= nullAddr var2)) (= (node var7 var2) var1)) (= (O_node var1) var0)) (= (write var12 var13 var0) var4)))) (Inv_Heap var11 var5))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 node) (var4 Heap) (var5 Heap) (var6 HeapObject) (var7 HeapObject) (var8 Int) (var9 Addr) (var10 Addr) (var11 Int) (var12 Addr) (var13 Heap) (var14 Addr)) (or (not (and (_Glue26 var14 var13 var12 var11 var10 var9 var8 var7) (and (and (and (and (and (and (and (and (and (= defObj var6) (= (write var5 var12 var6) var4)) (is-O_node var7)) (= (getnode var7) var3)) (= (|node::next| var3) var9)) (<= 0 (+ (+ var11 1) (- 1)))) (= nullAddr var2)) (= (node var8 var2) var1)) (= (O_node var1) var0)) (= (write var13 var14 var0) var5)))) (inv_main613_5 var4 var10 var11))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Heap)) (or (not (and (inv_main585_7 var3 var2 var1) (and (not (<= 0 (+ var2 (- 1)))) (= var0 1)))) (inv_main613_5 var3 var1 var0))))
(assert (forall ((var0 AllocResHeap) (var1 HeapObject) (var2 node) (var3 Addr) (var4 Int) (var5 Heap)) (or (not (and (inv_main585_7 var5 var4 var3) (and (and (not (= 4 4)) (= (O_node var2) var1)) (= (alloc var5 var1) var0)))) (Inv_Heap (newAddr var0) var1))))
(assert (forall ((var0 AllocResHeap) (var1 HeapObject) (var2 node) (var3 Heap) (var4 Addr) (var5 Int) (var6 Heap) (var7 HeapObject) (var8 Addr)) (or (not (and (and (Inv_Heap var8 var7) (inv_main585_7 var6 var5 var4)) (and (and (and (and (and (and (= (read var3 var8) var7) (valid var3 var8)) true) (= (O_node var2) var1)) (= (AllocResHeap var3 var8) var0)) (not (= 4 4))) (= (alloc var6 var1) var0)))) (_Glue14 var5 var8 var3 var7))))
(assert (forall ((var0 AllocResHeap) (var1 HeapObject) (var2 node) (var3 HeapObject) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Int) (var8 Heap)) (or (not (and (inv_main585_7 var8 var7 var6) (and (and (and (and (and (= (read var5 var4) var3) (not (valid var5 var4))) (= (O_node var2) var1)) (= (AllocResHeap var5 var4) var0)) (not (= 4 4))) (= (alloc var8 var1) var0)))) (_Glue14 var7 var4 var5 var3))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Int) (var4 node) (var5 HeapObject) (var6 Heap) (var7 Addr) (var8 Int)) (or (not (and (_Glue14 var8 var7 var6 var5) (and (and (and (and (and (and (and (and (is-O_node var5) (= (getnode var5) var4)) (= (|node::data| var4) var3)) (<= 0 (+ var8 (- 1)))) (= nullAddr var2)) (not (= var2 var7))) (= (node var3 var2) var1)) (= (O_node var1) var0)) (valid var6 var7)))) (Inv_Heap var7 var0))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Int) (var4 node) (var5 Heap) (var6 HeapObject) (var7 Heap) (var8 Int) (var9 HeapObject) (var10 Addr)) (or (not (and (and (Inv_Heap var10 var9) (_Glue14 var8 var10 var7 var6)) (and (and (and (and (and (and (and (and (and (and (and (= (read var5 var10) var9) (valid var5 var10)) true) (is-O_node var6)) (= (getnode var6) var4)) (= (|node::data| var4) var3)) (<= 0 (+ var8 (- 1)))) (= nullAddr var2)) (not (= var2 var10))) (= (node var3 var2) var1)) (= (O_node var1) var0)) (= (write var7 var10 var0) var5)))) (_Glue16 var5 var10 var9))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Int) (var4 node) (var5 HeapObject) (var6 Heap) (var7 HeapObject) (var8 Heap) (var9 Addr) (var10 Int)) (or (not (and (_Glue14 var10 var9 var8 var7) (and (and (and (and (and (and (and (and (and (and (= (read var6 var9) var5) (not (valid var6 var9))) (is-O_node var7)) (= (getnode var7) var4)) (= (|node::data| var4) var3)) (<= 0 (+ var10 (- 1)))) (= nullAddr var2)) (not (= var2 var9))) (= (node var3 var2) var1)) (= (O_node var1) var0)) (= (write var8 var9 var0) var6)))) (_Glue16 var6 var9 var5))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 node) (var4 HeapObject) (var5 Addr) (var6 Heap)) (or (not (and (_Glue16 var6 var5 var4) (and (and (and (and (and (is-O_node var4) (= (getnode var4) var3)) (= (|node::next| var3) var2)) (= (node 1 var2) var1)) (= (O_node var1) var0)) (valid var6 var5)))) (Inv_Heap var5 var0))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 node) (var4 Heap) (var5 HeapObject) (var6 Heap) (var7 HeapObject) (var8 Addr)) (not (and (and (Inv_Heap var8 var7) (_Glue16 var6 var8 var5)) (and (and (and (and (and (and (and (and (and (= (read var4 var8) var7) (is-O_node var7)) (valid var4 var8)) true) (is-O_node var5)) (= (getnode var5) var3)) (= (|node::next| var3) var2)) (= (node 1 var2) var1)) (= (O_node var1) var0)) (= (write var6 var8 var0) var4))))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 node) (var4 HeapObject) (var5 Heap) (var6 HeapObject) (var7 Addr) (var8 Heap)) (not (and (_Glue16 var8 var7 var6) (and (and (and (and (and (and (and (and (= (read var5 var7) var4) (is-O_node var4)) (not (valid var5 var7))) (is-O_node var6)) (= (getnode var6) var3)) (= (|node::next| var3) var2)) (= (node 1 var2) var1)) (= (O_node var1) var0)) (= (write var8 var7 var0) var5))))))
(check-sat)