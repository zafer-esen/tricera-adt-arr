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
(declare-fun _Glue10 (Heap Addr Addr Addr HeapObject) Bool)
(declare-fun Inv_Heap_exp_exp (Addr Int Addr) Bool)
(declare-fun _Glue6 (Addr Addr Addr Heap HeapObject) Bool)
(declare-fun _Glue2 (Addr Heap HeapObject) Bool)
(declare-fun inv_main_3 (Heap Addr Addr) Bool)
(declare-fun _Glue8 (Addr Addr Heap Addr HeapObject) Bool)
(declare-fun _Glue3_exp_exp (Addr Int Addr Addr Heap Addr HeapObject) Bool)
(declare-fun inv_main_15 (Heap Addr) Bool)
(assert (forall ((var0 AllocResHeap) (var1 Heap) (var2 Addr) (var3 Int) (var4 HeapObject) (var5 node)) (or (not (and (and (and (= (O_node var5) var4) (= (node var3 var2) var5)) (= (alloc var1 var4) var0)) (= emptyHeap var1))) (Inv_Heap_exp_exp (newAddr var0) var3 var2))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 HeapObject) (var3 node) (var4 AllocResHeap) (var5 Heap) (var6 HeapObject) (var7 node) (var8 Addr) (var9 Int) (var10 Addr)) (or (not (and (Inv_Heap_exp_exp var10 var9 var8) (and (and (and (and (and (and (and (and (and (= (O_node var7) var6) (= (AllocResHeap var5 var10) var4)) (= (O_node var3) var2)) (= (node var9 var8) var7)) (not (= var10 var1))) (= (read var5 var10) var6)) (valid var5 var10)) (= (alloc var0 var2) var4)) (= nullAddr var1)) (= emptyHeap var0)))) (_Glue2 var10 var5 var6))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 node) (var3 AllocResHeap) (var4 HeapObject) (var5 Heap) (var6 Addr) (var7 Addr)) (or (not (and (and (and (and (and (and (and (not (= var7 var6)) (= (read var5 var7) var4)) (not (valid var5 var7))) (= (AllocResHeap var5 var7) var3)) (= (O_node var2) var1)) (= (alloc var0 var1) var3)) (= nullAddr var6)) (= emptyHeap var0))) (_Glue2 var7 var5 var4))))
(assert (forall ((var0 Int) (var1 Addr) (var2 node) (var3 HeapObject) (var4 Heap) (var5 Addr)) (or (not (and (_Glue2 var5 var4 var3) (and (and (and (= (getnode var3) var2) (= (|node::n| var2) var1)) (valid var4 var5)) (= var0 2)))) (Inv_Heap_exp_exp var5 var0 var1))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 HeapObject) (var3 node) (var4 Addr) (var5 node) (var6 HeapObject) (var7 Heap) (var8 Addr)) (or (not (and (_Glue2 var8 var7 var6) (and (and (and (and (and (= (getnode var6) var5) (= (|node::n| var5) var4)) (= (node 2 var4) var3)) (= (O_node var3) var2)) (= (write var7 var8 var2) var1)) (= var0 var8)))) (inv_main_3 var1 var8 var0))))
(assert (forall ((var0 Addr) (var1 HeapObject) (var2 node) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Int) (var7 Addr)) (or (not (and (and (Inv_Heap_exp_exp var7 var6 var5) (inv_main_3 var4 var3 var7)) (and (and (and (= (O_node var2) var1) (= (node var6 var5) var2)) (= (read var4 var7) var1)) (valid var4 var7)))) (_Glue8 var0 var3 var4 var7 var1))))
(assert (forall ((var0 Addr) (var1 HeapObject) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main_3 var4 var3 var2) (and (= (read var4 var2) var1) (not (valid var4 var2))))) (_Glue8 var0 var3 var4 var2 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 node) (var3 HeapObject) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr)) (or (not (and (_Glue8 var7 var6 var5 var4 var3) (and (and (and (= (getnode var3) var2) (= (|node::n| var2) var1)) (valid var5 var4)) (= var0 2)))) (Inv_Heap_exp_exp var4 var0 var1))))
(assert (forall ((var0 node) (var1 Heap) (var2 HeapObject) (var3 node) (var4 Addr) (var5 HeapObject) (var6 node) (var7 HeapObject) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Int) (var13 Addr)) (or (not (and (and (Inv_Heap_exp_exp var13 var12 var11) (_Glue8 var10 var9 var8 var13 var7)) (and (and (and (and (and (and (and (and (= (O_node var6) var5) (= (node 2 var4) var3)) (= (O_node var3) var2)) (= (node var12 var11) var6)) (= (read var1 var13) var5)) (valid var1 var13)) (= (getnode var7) var0)) (= (|node::n| var0) var4)) (= (write var8 var13 var2) var1)))) (_Glue10 var1 var10 var9 var13 var5))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 node) (var4 HeapObject) (var5 Heap) (var6 HeapObject) (var7 Addr) (var8 Heap) (var9 Addr) (var10 Addr)) (or (not (and (_Glue8 var10 var9 var8 var7 var6) (and (and (and (and (and (and (= (read var5 var7) var4) (not (valid var5 var7))) (= (getnode var6) var3)) (= (|node::n| var3) var2)) (= (node 2 var2) var1)) (= (O_node var1) var0)) (= (write var8 var7 var0) var5)))) (_Glue10 var5 var10 var9 var7 var4))))
(assert (forall ((var0 Addr) (var1 Int) (var2 node) (var3 HeapObject) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (_Glue10 var6 var5 var5 var4 var3) (and (and (and (= (getnode var3) var2) (= (|node::h| var2) var1)) (valid var6 var4)) (= var0 0)))) (Inv_Heap_exp_exp var4 var1 var0))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 node) (var3 Int) (var4 node) (var5 HeapObject) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (_Glue10 var8 var7 var7 var6 var5) (and (and (and (and (= (getnode var5) var4) (= (|node::h| var4) var3)) (= (node var3 0) var2)) (= (O_node var2) var1)) (= (write var8 var6 var1) var0)))) (inv_main_15 var0 var7))))
(assert (forall ((var0 Addr) (var1 HeapObject) (var2 node) (var3 Heap) (var4 Addr) (var5 Addr)) (or (not (and (and (Inv_Heap_exp_exp var5 2 var4) (inv_main_15 var3 var5)) (and (and (and (and (and (= (O_node var2) var1) (= (node 2 var4) var2)) (= nullAddr var0)) (= (read var3 var5) var1)) (not (= var5 var0))) (valid var3 var5)))) (inv_main_15 var3 var4))))
(assert (forall ((var0 Addr) (var1 node) (var2 HeapObject) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main_15 var5 var4) (and (and (and (and (and (and (= nullAddr var3) (= (read var5 var4) var2)) (= (getnode var2) var1)) (= (|node::h| var1) 2)) (= (|node::n| var1) var0)) (not (= var4 var3))) (not (valid var5 var4))))) (inv_main_15 var5 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 HeapObject) (var4 node) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Int) (var9 Addr)) (or (not (and (and (Inv_Heap_exp_exp var9 var8 var7) (inv_main_3 var6 var5 var9)) (and (and (and (and (= (O_node var4) var3) (= (node var8 var7) var4)) (= nullAddr var2)) (= (read var6 var9) var3)) (valid var6 var9)))) (_Glue3_exp_exp var2 var1 var0 var5 var6 var9 var3))))
(assert (forall ((var0 Addr) (var1 Int) (var2 HeapObject) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main_3 var6 var5 var4) (and (and (= nullAddr var3) (= (read var6 var4) var2)) (not (valid var6 var4))))) (_Glue3_exp_exp var3 var1 var0 var5 var6 var4 var2))))
(assert (forall ((var0 Int) (var1 Addr) (var2 node) (var3 HeapObject) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Int) (var9 Addr)) (or (not (and (_Glue3_exp_exp var9 var8 var7 var6 var5 var4 var3) (and (and (and (= (getnode var3) var2) (= (|node::n| var2) var1)) (valid var5 var4)) (= var0 1)))) (Inv_Heap_exp_exp var4 var0 var1))))
(assert (forall ((var0 node) (var1 AllocResHeap) (var2 Heap) (var3 HeapObject) (var4 node) (var5 Addr) (var6 HeapObject) (var7 node) (var8 HeapObject) (var9 Addr) (var10 Heap) (var11 Addr) (var12 Addr) (var13 Int) (var14 Addr)) (or (not (and (_Glue3_exp_exp var14 var13 var12 var11 var10 var9 var8) (and (and (and (and (and (and (and (= (O_node var7) var6) (= (node 1 var5) var4)) (= (O_node var4) var3)) (= (node var13 var12) var7)) (= (alloc var2 var6) var1)) (= (getnode var8) var0)) (= (|node::n| var0) var5)) (= (write var10 var9 var3) var2)))) (Inv_Heap_exp_exp (newAddr var1) var13 var12))))
(assert (forall ((var0 node) (var1 Heap) (var2 HeapObject) (var3 node) (var4 Addr) (var5 HeapObject) (var6 node) (var7 AllocResHeap) (var8 Addr) (var9 Heap) (var10 HeapObject) (var11 node) (var12 HeapObject) (var13 Heap) (var14 Addr) (var15 Addr) (var16 Int) (var17 Addr) (var18 Addr) (var19 Int) (var20 Addr)) (or (not (and (and (Inv_Heap_exp_exp var20 var19 var18) (_Glue3_exp_exp var17 var16 var15 var14 var13 var20 var12)) (and (and (and (and (and (and (and (and (and (and (and (and (and (= (O_node var11) var10) (= (AllocResHeap var9 var8) var7)) (= (O_node var6) var5)) (= (node 1 var4) var3)) (= (O_node var3) var2)) (= (node var19 var18) var11)) (= (node var16 var15) var6)) (not (= var8 var17))) (= (read var9 var20) var10)) (valid var9 var20)) (= (alloc var1 var5) var7)) (= (getnode var12) var0)) (= (|node::n| var0) var4)) (= (write var13 var20 var2) var1)))) (_Glue6 var20 var14 var8 var9 var10))))
(assert (forall ((var0 node) (var1 Heap) (var2 HeapObject) (var3 HeapObject) (var4 node) (var5 Addr) (var6 HeapObject) (var7 node) (var8 AllocResHeap) (var9 Addr) (var10 Heap) (var11 HeapObject) (var12 Addr) (var13 Heap) (var14 Addr) (var15 Addr) (var16 Int) (var17 Addr)) (or (not (and (_Glue3_exp_exp var17 var16 var15 var14 var13 var12 var11) (and (and (and (and (and (and (and (and (and (and (and (= (AllocResHeap var10 var9) var8) (= (O_node var7) var6)) (= (node 1 var5) var4)) (= (O_node var4) var3)) (= (node var16 var15) var7)) (not (= var9 var17))) (= (read var10 var12) var2)) (not (valid var10 var12))) (= (alloc var1 var6) var8)) (= (getnode var11) var0)) (= (|node::n| var0) var5)) (= (write var13 var12 var3) var1)))) (_Glue6 var12 var14 var9 var10 var2))))
(assert (forall ((var0 Int) (var1 node) (var2 HeapObject) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr)) (or (not (and (_Glue6 var6 var5 var4 var3 var2) (and (and (= (getnode var2) var1) (= (|node::h| var1) var0)) (valid var3 var6)))) (Inv_Heap_exp_exp var6 var0 var4))))
(assert (forall ((var0 node) (var1 Heap) (var2 HeapObject) (var3 node) (var4 Int) (var5 HeapObject) (var6 node) (var7 HeapObject) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Int) (var13 Addr)) (or (not (and (and (Inv_Heap_exp_exp var13 var12 var11) (_Glue6 var13 var10 var9 var8 var7)) (and (and (and (and (and (and (and (and (= (O_node var6) var5) (= (node var4 var9) var3)) (= (O_node var3) var2)) (= (node var12 var11) var6)) (= (read var1 var13) var5)) (valid var1 var13)) (= (getnode var7) var0)) (= (|node::h| var0) var4)) (= (write var8 var13 var2) var1)))) (inv_main_3 var1 var10 var11))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Int) (var3 node) (var4 Addr) (var5 node) (var6 HeapObject) (var7 Heap) (var8 HeapObject) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Addr)) (or (not (and (_Glue6 var12 var11 var10 var9 var8) (and (and (and (and (and (and (and (and (= (read var7 var12) var6) (= (getnode var6) var5)) (= (|node::n| var5) var4)) (not (valid var7 var12))) (= (getnode var8) var3)) (= (|node::h| var3) var2)) (= (node var2 var10) var1)) (= (O_node var1) var0)) (= (write var9 var12 var0) var7)))) (inv_main_3 var7 var11 var4))))
(assert (forall ((var0 Addr) (var1 HeapObject) (var2 node) (var3 Heap) (var4 Addr) (var5 Int) (var6 Addr)) (not (and (and (Inv_Heap_exp_exp var6 var5 var4) (inv_main_15 var3 var6)) (and (and (and (and (and (and (= (O_node var2) var1) (= (node var5 var4) var2)) (not (= var6 var0))) (not (= var5 2))) (= nullAddr var0)) (= (read var3 var6) var1)) (valid var3 var6))))))
(assert (forall ((var0 node) (var1 HeapObject) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap)) (not (and (inv_main_15 var5 var4) (and (and (and (and (and (and (not (= var4 var3)) (not (= var2 2))) (= nullAddr var3)) (= (read var5 var4) var1)) (= (getnode var1) var0)) (= (|node::h| var0) var2)) (not (valid var5 var4)))))))
(check-sat)
