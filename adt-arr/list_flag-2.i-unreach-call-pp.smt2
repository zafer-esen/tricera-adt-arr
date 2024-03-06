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
(declare-fun inv_main556_7_19 () Bool)
(declare-fun _Glue9 (Addr Int Addr Addr Heap HeapObject) Bool)
(declare-fun inv_main554_5 (Heap Addr) Bool)
(declare-fun _Glue12 (Addr Addr Int Heap Addr HeapObject) Bool)
(declare-fun inv_main551_5 (Heap Addr) Bool)
(declare-fun _Glue4 (Addr Addr Addr Heap HeapObject) Bool)
(declare-fun Inv_Heap_exp_exp (Addr Int Addr) Bool)
(declare-fun _Glue1_exp_exp (Addr Int Addr Addr Heap Addr HeapObject) Bool)
(declare-fun _Glue6_exp_exp (Addr Int Addr Addr Int Heap Addr HeapObject) Bool)
(declare-fun _Glue11 (Addr Addr Heap Addr HeapObject) Bool)
(declare-fun inv_main_4 (Heap Int Addr Addr) Bool)
(assert (forall ((var0 HeapObject) (var1 node) (var2 Heap) (var3 Addr) (var4 Addr)) (or (not (and (and (Inv_Heap_exp_exp var4 1 var3) (inv_main551_5 var2 var4)) (and (and (and (= (O_node var1) var0) (= (node 1 var3) var1)) (= (read var2 var4) var0)) (valid var2 var4)))) (inv_main551_5 var2 var3))))
(assert (forall ((var0 Addr) (var1 node) (var2 HeapObject) (var3 Addr) (var4 Heap)) (or (not (and (inv_main551_5 var4 var3) (and (and (and (and (= (read var4 var3) var2) (= (getnode var2) var1)) (= (|node::h| var1) 1)) (= (|node::n| var1) var0)) (not (valid var4 var3))))) (inv_main551_5 var4 var0))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Heap) (var3 Addr) (var4 Int) (var5 Addr)) (or (not (and (and (Inv_Heap_exp_exp var5 var4 var3) (inv_main554_5 var2 var5)) (and (and (and (and (and (= (O_node var1) var0) (= (node var4 var3) var1)) (= (read var2 var5) var0)) (not (= var4 2))) (not (= var4 3))) (valid var2 var5)))) inv_main556_7_19)))
(assert (forall ((var0 Int) (var1 node) (var2 HeapObject) (var3 Addr) (var4 Heap)) (or (not (and (inv_main554_5 var4 var3) (and (and (and (and (and (= (read var4 var3) var2) (= (getnode var2) var1)) (= (|node::h| var1) var0)) (not (= var0 2))) (not (= var0 3))) (not (valid var4 var3))))) inv_main556_7_19)))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 HeapObject) (var4 node) (var5 Addr) (var6 Int) (var7 Heap) (var8 Addr) (var9 Int) (var10 Addr)) (or (not (and (and (Inv_Heap_exp_exp var10 var9 var8) (inv_main_4 var7 var6 var10 var5)) (and (and (and (and (= (O_node var4) var3) (= (node var9 var8) var4)) (= nullAddr var2)) (= (read var7 var10) var3)) (valid var7 var10)))) (_Glue6_exp_exp var2 var1 var0 var5 var6 var7 var10 var3))))
(assert (forall ((var0 Addr) (var1 Int) (var2 HeapObject) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Int) (var7 Heap)) (or (not (and (inv_main_4 var7 var6 var5 var4) (and (and (= nullAddr var3) (= (read var7 var5) var2)) (not (valid var7 var5))))) (_Glue6_exp_exp var3 var1 var0 var4 var6 var7 var5 var2))))
(assert (forall ((var0 Int) (var1 Addr) (var2 node) (var3 HeapObject) (var4 Addr) (var5 Heap) (var6 Int) (var7 Addr) (var8 Addr) (var9 Int) (var10 Addr)) (or (not (and (_Glue6_exp_exp var10 var9 var8 var7 var6 var5 var4 var3) (and (and (and (= (getnode var3) var2) (= (|node::n| var2) var1)) (valid var5 var4)) (= var0 1)))) (Inv_Heap_exp_exp var4 var0 var1))))
(assert (forall ((var0 node) (var1 AllocResHeap) (var2 Heap) (var3 HeapObject) (var4 node) (var5 Addr) (var6 HeapObject) (var7 node) (var8 HeapObject) (var9 Addr) (var10 Heap) (var11 Int) (var12 Addr) (var13 Addr) (var14 Int) (var15 Addr)) (or (not (and (_Glue6_exp_exp var15 var14 var13 var12 var11 var10 var9 var8) (and (and (and (and (and (and (and (= (O_node var7) var6) (= (node 1 var5) var4)) (= (O_node var4) var3)) (= (node var14 var13) var7)) (= (alloc var2 var6) var1)) (= (getnode var8) var0)) (= (|node::n| var0) var5)) (= (write var10 var9 var3) var2)))) (Inv_Heap_exp_exp (newAddr var1) var14 var13))))
(assert (forall ((var0 node) (var1 Heap) (var2 HeapObject) (var3 node) (var4 Addr) (var5 HeapObject) (var6 node) (var7 AllocResHeap) (var8 Addr) (var9 Heap) (var10 HeapObject) (var11 node) (var12 HeapObject) (var13 Heap) (var14 Int) (var15 Addr) (var16 Addr) (var17 Int) (var18 Addr) (var19 Addr) (var20 Int) (var21 Addr)) (or (not (and (and (Inv_Heap_exp_exp var21 var20 var19) (_Glue6_exp_exp var18 var17 var16 var15 var14 var13 var21 var12)) (and (and (and (and (and (and (and (and (and (and (and (and (and (= (O_node var11) var10) (= (AllocResHeap var9 var8) var7)) (= (O_node var6) var5)) (= (node 1 var4) var3)) (= (O_node var3) var2)) (= (node var20 var19) var11)) (= (node var17 var16) var6)) (not (= var8 var18))) (= (read var9 var21) var10)) (valid var9 var21)) (= (alloc var1 var5) var7)) (= (getnode var12) var0)) (= (|node::n| var0) var4)) (= (write var13 var21 var2) var1)))) (_Glue9 var21 var14 var15 var8 var9 var10))))
(assert (forall ((var0 node) (var1 Heap) (var2 HeapObject) (var3 HeapObject) (var4 node) (var5 Addr) (var6 HeapObject) (var7 node) (var8 AllocResHeap) (var9 Addr) (var10 Heap) (var11 HeapObject) (var12 Addr) (var13 Heap) (var14 Int) (var15 Addr) (var16 Addr) (var17 Int) (var18 Addr)) (or (not (and (_Glue6_exp_exp var18 var17 var16 var15 var14 var13 var12 var11) (and (and (and (and (and (and (and (and (and (and (and (= (AllocResHeap var10 var9) var8) (= (O_node var7) var6)) (= (node 1 var5) var4)) (= (O_node var4) var3)) (= (node var17 var16) var7)) (not (= var9 var18))) (= (read var10 var12) var2)) (not (valid var10 var12))) (= (alloc var1 var6) var8)) (= (getnode var11) var0)) (= (|node::n| var0) var5)) (= (write var13 var12 var3) var1)))) (_Glue9 var12 var14 var15 var9 var10 var2))))
(assert (forall ((var0 Int) (var1 node) (var2 HeapObject) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Int) (var7 Addr)) (or (not (and (_Glue9 var7 var6 var5 var4 var3 var2) (and (and (= (getnode var2) var1) (= (|node::h| var1) var0)) (valid var3 var7)))) (Inv_Heap_exp_exp var7 var0 var4))))
(assert (forall ((var0 node) (var1 Heap) (var2 HeapObject) (var3 node) (var4 Int) (var5 HeapObject) (var6 node) (var7 HeapObject) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Int) (var12 Addr) (var13 Int) (var14 Addr)) (or (not (and (and (Inv_Heap_exp_exp var14 var13 var12) (_Glue9 var14 var11 var10 var9 var8 var7)) (and (and (and (and (and (and (and (and (and (= (O_node var6) var5) (= (node var4 var9) var3)) (= (O_node var3) var2)) (= (node var13 var12) var6)) (= (read var1 var14) var5)) (not (= var11 0))) (valid var1 var14)) (= (getnode var7) var0)) (= (|node::h| var0) var4)) (= (write var8 var14 var2) var1)))) (inv_main_4 var1 var11 var12 var10))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Int) (var3 node) (var4 Addr) (var5 node) (var6 HeapObject) (var7 Heap) (var8 HeapObject) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Int) (var13 Addr)) (or (not (and (_Glue9 var13 var12 var11 var10 var9 var8) (and (and (and (and (and (and (and (and (and (= (read var7 var13) var6) (= (getnode var6) var5)) (= (|node::n| var5) var4)) (not (= var12 0))) (not (valid var7 var13))) (= (getnode var8) var3)) (= (|node::h| var3) var2)) (= (node var2 var10) var1)) (= (O_node var1) var0)) (= (write var9 var13 var0) var7)))) (inv_main_4 var7 var12 var4 var11))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 AllocResHeap) (var3 Heap) (var4 Addr) (var5 Int) (var6 HeapObject) (var7 node)) (or (not (and (and (and (and (and (and (= (O_node var7) var6) (= (node var5 var4) var7)) (= (alloc var3 var6) var2)) (= (newAddr var2) var1)) (not (= var1 var0))) (= nullAddr var0)) (= emptyHeap var3))) (Inv_Heap_exp_exp (newAddr var2) var5 var4))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 AllocResHeap) (var6 Heap) (var7 HeapObject) (var8 node)) (or (not (and (and (and (and (and (and (and (= (O_node var8) var7) (= (alloc var6 var7) var5)) (= (newHeap var5) var4)) (= (newAddr var5) var3)) (not (= var3 var2))) (= nullAddr var2)) (= emptyHeap var6)) (= var1 var3))) (inv_main_4 var4 var0 var1 var3))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Heap) (var3 Addr) (var4 Addr)) (or (not (and (and (Inv_Heap_exp_exp var4 2 var3) (inv_main554_5 var2 var4)) (and (and (and (= (O_node var1) var0) (= (node 2 var3) var1)) (= (read var2 var4) var0)) (valid var2 var4)))) (inv_main554_5 var2 var3))))
(assert (forall ((var0 Addr) (var1 node) (var2 HeapObject) (var3 Addr) (var4 Heap)) (or (not (and (inv_main554_5 var4 var3) (and (and (and (and (= (read var4 var3) var2) (= (getnode var2) var1)) (= (|node::h| var1) 2)) (= (|node::n| var1) var0)) (not (valid var4 var3))))) (inv_main554_5 var4 var0))))
(assert (forall ((var0 Addr) (var1 HeapObject) (var2 node) (var3 Addr) (var4 Int) (var5 Heap) (var6 Addr) (var7 Int) (var8 Addr)) (or (not (and (and (Inv_Heap_exp_exp var8 var7 var6) (inv_main_4 var5 var4 var8 var3)) (and (and (and (= (O_node var2) var1) (= (node var7 var6) var2)) (= (read var5 var8) var1)) (valid var5 var8)))) (_Glue12 var0 var3 var4 var5 var8 var1))))
(assert (forall ((var0 Addr) (var1 HeapObject) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap)) (or (not (and (inv_main_4 var5 var4 var3 var2) (and (= (read var5 var3) var1) (not (valid var5 var3))))) (_Glue12 var0 var2 var4 var5 var3 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 node) (var3 HeapObject) (var4 Addr) (var5 Heap) (var6 Int) (var7 Addr)) (or (not (and (_Glue12 var7 var7 var6 var5 var4 var3) (and (and (and (and (= (getnode var3) var2) (= (|node::n| var2) var1)) (not (= var6 0))) (valid var5 var4)) (= var0 3)))) (Inv_Heap_exp_exp var4 var0 var1))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 node) (var3 Addr) (var4 node) (var5 HeapObject) (var6 Addr) (var7 Heap) (var8 Int) (var9 Addr)) (or (not (and (_Glue12 var9 var9 var8 var7 var6 var5) (and (and (and (and (and (= (getnode var5) var4) (= (|node::n| var4) var3)) (= (node 3 var3) var2)) (= (O_node var2) var1)) (= (write var7 var6 var1) var0)) (not (= var8 0))))) (inv_main551_5 var0 var9))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 HeapObject) (var4 node) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Int) (var9 Addr)) (or (not (and (and (Inv_Heap_exp_exp var9 var8 var7) (inv_main_4 var6 0 var9 var5)) (and (and (and (and (= (O_node var4) var3) (= (node var8 var7) var4)) (= nullAddr var2)) (= (read var6 var9) var3)) (valid var6 var9)))) (_Glue1_exp_exp var2 var1 var0 var5 var6 var9 var3))))
(assert (forall ((var0 Addr) (var1 Int) (var2 HeapObject) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main_4 var6 0 var5 var4) (and (and (= nullAddr var3) (= (read var6 var5) var2)) (not (valid var6 var5))))) (_Glue1_exp_exp var3 var1 var0 var4 var6 var5 var2))))
(assert (forall ((var0 Int) (var1 Addr) (var2 node) (var3 HeapObject) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Int) (var9 Addr)) (or (not (and (_Glue1_exp_exp var9 var8 var7 var6 var5 var4 var3) (and (and (and (= (getnode var3) var2) (= (|node::n| var2) var1)) (valid var5 var4)) (= var0 2)))) (Inv_Heap_exp_exp var4 var0 var1))))
(assert (forall ((var0 node) (var1 AllocResHeap) (var2 Heap) (var3 HeapObject) (var4 node) (var5 Addr) (var6 HeapObject) (var7 node) (var8 HeapObject) (var9 Addr) (var10 Heap) (var11 Addr) (var12 Addr) (var13 Int) (var14 Addr)) (or (not (and (_Glue1_exp_exp var14 var13 var12 var11 var10 var9 var8) (and (and (and (and (and (and (and (= (O_node var7) var6) (= (node 2 var5) var4)) (= (O_node var4) var3)) (= (node var13 var12) var7)) (= (alloc var2 var6) var1)) (= (getnode var8) var0)) (= (|node::n| var0) var5)) (= (write var10 var9 var3) var2)))) (Inv_Heap_exp_exp (newAddr var1) var13 var12))))
(assert (forall ((var0 node) (var1 Heap) (var2 HeapObject) (var3 node) (var4 Addr) (var5 HeapObject) (var6 node) (var7 AllocResHeap) (var8 Addr) (var9 Heap) (var10 HeapObject) (var11 node) (var12 HeapObject) (var13 Heap) (var14 Addr) (var15 Addr) (var16 Int) (var17 Addr) (var18 Addr) (var19 Int) (var20 Addr)) (or (not (and (and (Inv_Heap_exp_exp var20 var19 var18) (_Glue1_exp_exp var17 var16 var15 var14 var13 var20 var12)) (and (and (and (and (and (and (and (and (and (and (and (and (and (= (O_node var11) var10) (= (AllocResHeap var9 var8) var7)) (= (O_node var6) var5)) (= (node 2 var4) var3)) (= (O_node var3) var2)) (= (node var19 var18) var11)) (= (node var16 var15) var6)) (not (= var8 var17))) (= (read var9 var20) var10)) (valid var9 var20)) (= (alloc var1 var5) var7)) (= (getnode var12) var0)) (= (|node::n| var0) var4)) (= (write var13 var20 var2) var1)))) (_Glue4 var20 var14 var8 var9 var10))))
(assert (forall ((var0 node) (var1 Heap) (var2 HeapObject) (var3 HeapObject) (var4 node) (var5 Addr) (var6 HeapObject) (var7 node) (var8 AllocResHeap) (var9 Addr) (var10 Heap) (var11 HeapObject) (var12 Addr) (var13 Heap) (var14 Addr) (var15 Addr) (var16 Int) (var17 Addr)) (or (not (and (_Glue1_exp_exp var17 var16 var15 var14 var13 var12 var11) (and (and (and (and (and (and (and (and (and (and (and (= (AllocResHeap var10 var9) var8) (= (O_node var7) var6)) (= (node 2 var5) var4)) (= (O_node var4) var3)) (= (node var16 var15) var7)) (not (= var9 var17))) (= (read var10 var12) var2)) (not (valid var10 var12))) (= (alloc var1 var6) var8)) (= (getnode var11) var0)) (= (|node::n| var0) var5)) (= (write var13 var12 var3) var1)))) (_Glue4 var12 var14 var9 var10 var2))))
(assert (forall ((var0 Int) (var1 node) (var2 HeapObject) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr)) (or (not (and (_Glue4 var6 var5 var4 var3 var2) (and (and (= (getnode var2) var1) (= (|node::h| var1) var0)) (valid var3 var6)))) (Inv_Heap_exp_exp var6 var0 var4))))
(assert (forall ((var0 Int) (var1 node) (var2 Heap) (var3 HeapObject) (var4 node) (var5 Int) (var6 HeapObject) (var7 node) (var8 HeapObject) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Int) (var14 Addr)) (or (not (and (and (Inv_Heap_exp_exp var14 var13 var12) (_Glue4 var14 var11 var10 var9 var8)) (and (and (and (and (and (and (and (and (and (= (O_node var7) var6) (= (node var5 var10) var4)) (= (O_node var4) var3)) (= (node var13 var12) var7)) (= (read var2 var14) var6)) (valid var2 var14)) (= (getnode var8) var1)) (= (|node::h| var1) var5)) (= (write var9 var14 var3) var2)) (= var0 0)))) (inv_main_4 var2 var0 var12 var11))))
(assert (forall ((var0 Int) (var1 HeapObject) (var2 node) (var3 Int) (var4 node) (var5 Addr) (var6 node) (var7 HeapObject) (var8 Heap) (var9 HeapObject) (var10 Heap) (var11 Addr) (var12 Addr) (var13 Addr)) (or (not (and (_Glue4 var13 var12 var11 var10 var9) (and (and (and (and (and (and (and (and (and (= (read var8 var13) var7) (= (getnode var7) var6)) (= (|node::n| var6) var5)) (not (valid var8 var13))) (= (getnode var9) var4)) (= (|node::h| var4) var3)) (= (node var3 var11) var2)) (= (O_node var2) var1)) (= (write var10 var13 var1) var8)) (= var0 0)))) (inv_main_4 var8 var0 var5 var12))))
(assert (not inv_main556_7_19))
(assert (forall ((var0 Addr) (var1 HeapObject) (var2 node) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Int) (var7 Addr)) (or (not (and (and (Inv_Heap_exp_exp var7 var6 var5) (inv_main_4 var4 0 var7 var3)) (and (and (and (= (O_node var2) var1) (= (node var6 var5) var2)) (= (read var4 var7) var1)) (valid var4 var7)))) (_Glue11 var0 var3 var4 var7 var1))))
(assert (forall ((var0 Addr) (var1 HeapObject) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main_4 var4 0 var3 var2) (and (= (read var4 var3) var1) (not (valid var4 var3))))) (_Glue11 var0 var2 var4 var3 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 node) (var3 HeapObject) (var4 Addr) (var5 Heap) (var6 Addr)) (or (not (and (_Glue11 var6 var6 var5 var4 var3) (and (and (and (= (getnode var3) var2) (= (|node::n| var2) var1)) (valid var5 var4)) (= var0 3)))) (Inv_Heap_exp_exp var4 var0 var1))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 node) (var3 Addr) (var4 node) (var5 HeapObject) (var6 Addr) (var7 Heap) (var8 Addr)) (or (not (and (_Glue11 var8 var8 var7 var6 var5) (and (and (and (and (= (getnode var5) var4) (= (|node::n| var4) var3)) (= (node 3 var3) var2)) (= (O_node var2) var1)) (= (write var7 var6 var1) var0)))) (inv_main554_5 var0 var8))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Heap) (var3 Addr) (var4 Int) (var5 Addr)) (or (not (and (and (Inv_Heap_exp_exp var5 var4 var3) (inv_main551_5 var2 var5)) (and (and (and (and (and (= (O_node var1) var0) (= (node var4 var3) var1)) (= (read var2 var5) var0)) (not (= var4 1))) (not (= var4 3))) (valid var2 var5)))) inv_main556_7_19)))
(assert (forall ((var0 Int) (var1 node) (var2 HeapObject) (var3 Addr) (var4 Heap)) (or (not (and (inv_main551_5 var4 var3) (and (and (and (and (and (= (read var4 var3) var2) (= (getnode var2) var1)) (= (|node::h| var1) var0)) (not (= var0 1))) (not (= var0 3))) (not (valid var4 var3))))) inv_main556_7_19)))
(check-sat)
