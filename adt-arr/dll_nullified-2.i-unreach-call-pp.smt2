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
                   ((node (|node::data_0| Int) (|node::next| Addr) (|node::data_1| Int) (|node::prev| Addr) (|node::data_2| Int)))))
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
(declare-fun inv_main608_8_28 (Heap Addr Addr Int) Bool)
(declare-fun inv_main578_3 (Heap Int Addr) Bool)
(declare-fun _Glue5 (Heap Addr Int Addr HeapObject) Bool)
(declare-fun _Glue7 (Heap Addr Int Addr HeapObject) Bool)
(declare-fun _Glue1 (Addr Int Addr Heap HeapObject) Bool)
(declare-fun _Glue20 (Addr Int Addr Heap) Bool)
(declare-fun _Glue18 (Addr Int Heap) Bool)
(declare-fun _Glue14 (Addr Int Heap) Bool)
(declare-fun _Glue16 (Addr Int Heap) Bool)
(declare-fun inv_main_13 (Heap Addr) Bool)
(declare-fun inv_main_32 () Bool)
(declare-fun _Glue15 (Heap Int Addr HeapObject) Bool)
(declare-fun _Glue19 (Heap Int Addr HeapObject) Bool)
(declare-fun _Glue11 (Heap Addr Int Addr HeapObject) Bool)
(declare-fun _Glue17 (Heap Int Addr HeapObject) Bool)
(declare-fun inv_main601_8_19 (Heap Addr Int) Bool)
(declare-fun _Glue13 (Int Addr Heap HeapObject) Bool)
(declare-fun _Glue3 (Heap Addr Int Addr HeapObject) Bool)
(declare-fun _Glue21 (Heap Addr Int Addr HeapObject) Bool)
(declare-fun _Glue9 (Heap Addr Int Addr HeapObject) Bool)
(declare-fun inv_main599_3_12 (Heap Addr) Bool)
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main608_8_28 var3 var2 var1 0) (and (= defObj var0) (valid var3 var2)))) (Inv_Heap var2 var0))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main608_8_28 var4 var3 var2 0) (and (= defObj var1) (= (write var4 var3 var1) var0)))) (inv_main_13 var0 var2))))
(assert (forall ((var0 Int) (var1 Addr) (var2 node) (var3 Addr) (var4 Int) (var5 Heap) (var6 HeapObject) (var7 Addr)) (or (not (and (and (Inv_Heap var7 var6) (inv_main_13 var5 var7)) (and (and (and (and (and (and (and (and (and (not (= var4 0)) (not (= var3 var7))) (= nullAddr var3)) (= (read var5 var7) var6)) (= (getnode var6) var2)) (= (|node::prev| var2) var1)) (= (|node::data_1| var2) var4)) (= (|node::data_0| var2) 0)) (valid var5 var7)) (= var0 1)))) (inv_main608_8_28 var5 var7 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 node) (var3 HeapObject) (var4 Addr) (var5 Int) (var6 Addr) (var7 Heap)) (or (not (and (inv_main_13 var7 var6) (and (and (and (and (and (and (and (and (and (not (= var5 0)) (not (= var4 var6))) (= nullAddr var4)) (= (read var7 var6) var3)) (= (getnode var3) var2)) (= (|node::prev| var2) var1)) (= (|node::data_1| var2) var5)) (= (|node::data_0| var2) 0)) (not (valid var7 var6))) (= var0 1)))) (inv_main608_8_28 var7 var6 var1 var0))))
(assert (not inv_main_32))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main608_8_28 var3 var2 var1 var0) (not (= var0 0)))) inv_main_32)))
(assert (forall ((var0 Addr) (var1 node) (var2 Heap) (var3 HeapObject) (var4 Addr)) (or (not (and (and (Inv_Heap var4 var3) (inv_main601_8_19 var2 var4 0)) (and (and (and (= (read var2 var4) var3) (= (getnode var3) var1)) (= (|node::next| var1) var0)) (valid var2 var4)))) (inv_main599_3_12 var2 var0))))
(assert (forall ((var0 Addr) (var1 node) (var2 HeapObject) (var3 Addr) (var4 Heap)) (or (not (and (inv_main601_8_19 var4 var3 0) (and (and (and (= (read var4 var3) var2) (= (getnode var2) var1)) (= (|node::next| var1) var0)) (not (valid var4 var3))))) (inv_main599_3_12 var4 var0))))
(assert (forall ((var0 Int) (var1 node) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap) (var6 HeapObject) (var7 Addr)) (or (not (and (and (Inv_Heap var7 var6) (inv_main599_3_12 var5 var7)) (and (and (and (and (and (and (and (and (and (and (not (= var4 0)) (not (= var3 var2))) (= (read var5 var7) var6)) (= (getnode var6) var1)) (= (|node::next| var1) var2)) (= nullAddr var3)) (= (|node::data_1| var1) 0)) (= (|node::data_0| var1) 0)) (= (|node::data_2| var1) var4)) (valid var5 var7)) (= var0 1)))) (inv_main601_8_19 var5 var7 var0))))
(assert (forall ((var0 Int) (var1 node) (var2 Addr) (var3 Addr) (var4 Heap) (var5 HeapObject) (var6 Addr)) (or (not (and (and (Inv_Heap var6 var5) (inv_main599_3_12 var4 var6)) (and (and (and (and (and (and (and (and (and (not (= var3 var2)) (= (read var4 var6) var5)) (= (getnode var5) var1)) (= (|node::next| var1) var2)) (= nullAddr var3)) (= (|node::data_1| var1) 0)) (= (|node::data_0| var1) 0)) (= (|node::data_2| var1) 0)) (valid var4 var6)) (= var0 0)))) (inv_main601_8_19 var4 var6 var0))))
(assert (forall ((var0 Int) (var1 node) (var2 HeapObject) (var3 Addr) (var4 Addr) (var5 Int) (var6 Addr) (var7 Heap)) (or (not (and (inv_main599_3_12 var7 var6) (and (and (and (and (and (and (and (and (and (and (not (= var5 0)) (not (= var4 var3))) (= (read var7 var6) var2)) (= (getnode var2) var1)) (= (|node::next| var1) var3)) (= nullAddr var4)) (= (|node::data_1| var1) 0)) (= (|node::data_0| var1) 0)) (= (|node::data_2| var1) var5)) (not (valid var7 var6))) (= var0 1)))) (inv_main601_8_19 var7 var6 var0))))
(assert (forall ((var0 Int) (var1 node) (var2 HeapObject) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main599_3_12 var6 var5) (and (and (and (and (and (and (and (and (and (not (= var4 var3)) (= (read var6 var5) var2)) (= (getnode var2) var1)) (= (|node::next| var1) var3)) (= nullAddr var4)) (= (|node::data_1| var1) 0)) (= (|node::data_0| var1) 0)) (= (|node::data_2| var1) 0)) (not (valid var6 var5))) (= var0 0)))) (inv_main601_8_19 var6 var5 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 node) (var3 Addr) (var4 Int) (var5 Heap) (var6 HeapObject) (var7 Addr)) (or (not (and (and (Inv_Heap var7 var6) (inv_main_13 var5 var7)) (and (and (and (and (and (and (and (and (not (= var4 0)) (not (= var3 var7))) (= nullAddr var3)) (= (read var5 var7) var6)) (= (getnode var6) var2)) (= (|node::prev| var2) var1)) (= (|node::data_0| var2) var4)) (valid var5 var7)) (= var0 1)))) (inv_main608_8_28 var5 var7 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 node) (var3 HeapObject) (var4 Addr) (var5 Int) (var6 Addr) (var7 Heap)) (or (not (and (inv_main_13 var7 var6) (and (and (and (and (and (and (and (and (not (= var5 0)) (not (= var4 var6))) (= nullAddr var4)) (= (read var7 var6) var3)) (= (getnode var3) var2)) (= (|node::prev| var2) var1)) (= (|node::data_0| var2) var5)) (not (valid var7 var6))) (= var0 1)))) (inv_main608_8_28 var7 var6 var1 var0))))
(assert (forall ((var0 Int) (var1 node) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap) (var6 HeapObject) (var7 Addr)) (or (not (and (and (Inv_Heap var7 var6) (inv_main599_3_12 var5 var7)) (and (and (and (and (and (and (and (and (not (= var4 0)) (not (= var3 var2))) (= (read var5 var7) var6)) (= (getnode var6) var1)) (= (|node::next| var1) var2)) (= nullAddr var3)) (= (|node::data_0| var1) var4)) (valid var5 var7)) (= var0 1)))) (inv_main601_8_19 var5 var7 var0))))
(assert (forall ((var0 Int) (var1 node) (var2 HeapObject) (var3 Addr) (var4 Addr) (var5 Int) (var6 Addr) (var7 Heap)) (or (not (and (inv_main599_3_12 var7 var6) (and (and (and (and (and (and (and (and (not (= var5 0)) (not (= var4 var3))) (= (read var7 var6) var2)) (= (getnode var2) var1)) (= (|node::next| var1) var3)) (= nullAddr var4)) (= (|node::data_0| var1) var5)) (not (valid var7 var6))) (= var0 1)))) (inv_main601_8_19 var7 var6 var0))))
(assert (forall ((var0 AllocResHeap) (var1 HeapObject) (var2 node) (var3 Addr) (var4 Int) (var5 Heap)) (or (not (and (inv_main578_3 var5 (+ var4 1) var3) (and (= (O_node var2) var1) (= (alloc var5 var1) var0)))) (Inv_Heap (newAddr var0) var1))))
(assert (forall ((var0 AllocResHeap) (var1 HeapObject) (var2 node) (var3 Heap) (var4 Addr) (var5 Int) (var6 Heap) (var7 HeapObject) (var8 Addr)) (or (not (and (and (Inv_Heap var8 var7) (inv_main578_3 var6 (+ var5 1) var4)) (and (and (and (and (and (= (read var3 var8) var7) (valid var3 var8)) true) (= (O_node var2) var1)) (= (AllocResHeap var3 var8) var0)) (= (alloc var6 var1) var0)))) (_Glue1 var4 var5 var8 var3 var7))))
(assert (forall ((var0 AllocResHeap) (var1 HeapObject) (var2 node) (var3 HeapObject) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Int) (var8 Heap)) (or (not (and (inv_main578_3 var8 (+ var7 1) var6) (and (and (and (and (= (read var5 var4) var3) (not (valid var5 var4))) (= (O_node var2) var1)) (= (AllocResHeap var5 var4) var0)) (= (alloc var8 var1) var0)))) (_Glue1 var6 var7 var4 var5 var3))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Int) (var3 Addr) (var4 Int) (var5 Addr) (var6 node) (var7 HeapObject) (var8 Heap) (var9 Addr) (var10 Int) (var11 Addr)) (or (not (and (_Glue1 var11 var10 var9 var8 var7) (and (and (and (and (and (and (and (= (getnode var7) var6) (= (|node::next| var6) var5)) (= (|node::data_1| var6) var4)) (= (|node::prev| var6) var3)) (= (|node::data_2| var6) var2)) (= (node 0 var5 var4 var3 var2) var1)) (= (O_node var1) var0)) (valid var8 var9)))) (Inv_Heap var9 var0))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Int) (var3 Addr) (var4 Int) (var5 Addr) (var6 node) (var7 Heap) (var8 HeapObject) (var9 Heap) (var10 Int) (var11 Addr) (var12 HeapObject) (var13 Addr)) (or (not (and (and (Inv_Heap var13 var12) (_Glue1 var11 var10 var13 var9 var8)) (and (and (and (and (and (and (and (and (and (and (= (read var7 var13) var12) (valid var7 var13)) true) (= (getnode var8) var6)) (= (|node::next| var6) var5)) (= (|node::data_1| var6) var4)) (= (|node::prev| var6) var3)) (= (|node::data_2| var6) var2)) (= (node 0 var5 var4 var3 var2) var1)) (= (O_node var1) var0)) (= (write var9 var13 var0) var7)))) (_Glue3 var7 var11 var10 var13 var12))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Int) (var3 Addr) (var4 Int) (var5 Addr) (var6 node) (var7 HeapObject) (var8 Heap) (var9 HeapObject) (var10 Heap) (var11 Addr) (var12 Int) (var13 Addr)) (or (not (and (_Glue1 var13 var12 var11 var10 var9) (and (and (and (and (and (and (and (and (and (= (read var8 var11) var7) (not (valid var8 var11))) (= (getnode var9) var6)) (= (|node::next| var6) var5)) (= (|node::data_1| var6) var4)) (= (|node::prev| var6) var3)) (= (|node::data_2| var6) var2)) (= (node 0 var5 var4 var3 var2) var1)) (= (O_node var1) var0)) (= (write var10 var11 var0) var8)))) (_Glue3 var8 var13 var12 var11 var7))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Int) (var3 Addr) (var4 Addr) (var5 Int) (var6 node) (var7 HeapObject) (var8 Addr) (var9 Int) (var10 Addr) (var11 Heap)) (or (not (and (_Glue3 var11 var10 var9 var8 var7) (and (and (and (and (and (and (and (= (getnode var7) var6) (= (|node::data_0| var6) var5)) (= (|node::next| var6) var4)) (= (|node::prev| var6) var3)) (= (|node::data_2| var6) var2)) (= (node var5 var4 0 var3 var2) var1)) (= (O_node var1) var0)) (valid var11 var8)))) (Inv_Heap var8 var0))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Int) (var3 Addr) (var4 Addr) (var5 Int) (var6 node) (var7 Heap) (var8 HeapObject) (var9 Int) (var10 Addr) (var11 Heap) (var12 HeapObject) (var13 Addr)) (or (not (and (and (Inv_Heap var13 var12) (_Glue3 var11 var10 var9 var13 var8)) (and (and (and (and (and (and (and (and (and (and (= (read var7 var13) var12) (valid var7 var13)) true) (= (getnode var8) var6)) (= (|node::data_0| var6) var5)) (= (|node::next| var6) var4)) (= (|node::prev| var6) var3)) (= (|node::data_2| var6) var2)) (= (node var5 var4 0 var3 var2) var1)) (= (O_node var1) var0)) (= (write var11 var13 var0) var7)))) (_Glue5 var7 var10 var9 var13 var12))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Int) (var3 Addr) (var4 Addr) (var5 Int) (var6 node) (var7 HeapObject) (var8 Heap) (var9 HeapObject) (var10 Addr) (var11 Int) (var12 Addr) (var13 Heap)) (or (not (and (_Glue3 var13 var12 var11 var10 var9) (and (and (and (and (and (and (and (and (and (= (read var8 var10) var7) (not (valid var8 var10))) (= (getnode var9) var6)) (= (|node::data_0| var6) var5)) (= (|node::next| var6) var4)) (= (|node::prev| var6) var3)) (= (|node::data_2| var6) var2)) (= (node var5 var4 0 var3 var2) var1)) (= (O_node var1) var0)) (= (write var13 var10 var0) var8)))) (_Glue5 var8 var12 var11 var10 var7))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Int) (var4 Addr) (var5 Int) (var6 node) (var7 HeapObject) (var8 Addr) (var9 Int) (var10 Addr) (var11 Heap)) (or (not (and (_Glue5 var11 var10 var9 var8 var7) (and (and (and (and (and (and (and (= (getnode var7) var6) (= (|node::data_0| var6) var5)) (= (|node::next| var6) var4)) (= (|node::data_1| var6) var3)) (= (|node::prev| var6) var2)) (= (node var5 var4 var3 var2 0) var1)) (= (O_node var1) var0)) (valid var11 var8)))) (Inv_Heap var8 var0))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Int) (var4 Addr) (var5 Int) (var6 node) (var7 Heap) (var8 HeapObject) (var9 Int) (var10 Addr) (var11 Heap) (var12 HeapObject) (var13 Addr)) (or (not (and (and (Inv_Heap var13 var12) (_Glue5 var11 var10 var9 var13 var8)) (and (and (and (and (and (and (and (and (and (and (= (read var7 var13) var12) (valid var7 var13)) true) (= (getnode var8) var6)) (= (|node::data_0| var6) var5)) (= (|node::next| var6) var4)) (= (|node::data_1| var6) var3)) (= (|node::prev| var6) var2)) (= (node var5 var4 var3 var2 0) var1)) (= (O_node var1) var0)) (= (write var11 var13 var0) var7)))) (_Glue7 var7 var10 var9 var13 var12))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Int) (var4 Addr) (var5 Int) (var6 node) (var7 HeapObject) (var8 Heap) (var9 HeapObject) (var10 Addr) (var11 Int) (var12 Addr) (var13 Heap)) (or (not (and (_Glue5 var13 var12 var11 var10 var9) (and (and (and (and (and (and (and (and (and (= (read var8 var10) var7) (not (valid var8 var10))) (= (getnode var9) var6)) (= (|node::data_0| var6) var5)) (= (|node::next| var6) var4)) (= (|node::data_1| var6) var3)) (= (|node::prev| var6) var2)) (= (node var5 var4 var3 var2 0) var1)) (= (O_node var1) var0)) (= (write var13 var10 var0) var8)))) (_Glue7 var8 var12 var11 var10 var7))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Int) (var3 Addr) (var4 Int) (var5 Int) (var6 node) (var7 HeapObject) (var8 Addr) (var9 Int) (var10 Addr) (var11 Heap)) (or (not (and (_Glue7 var11 var10 var9 var8 var7) (and (and (and (and (and (and (and (= (getnode var7) var6) (= (|node::data_0| var6) var5)) (= (|node::data_1| var6) var4)) (= (|node::prev| var6) var3)) (= (|node::data_2| var6) var2)) (= (node var5 var10 var4 var3 var2) var1)) (= (O_node var1) var0)) (valid var11 var8)))) (Inv_Heap var8 var0))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Int) (var3 Addr) (var4 Int) (var5 Int) (var6 node) (var7 Heap) (var8 HeapObject) (var9 Int) (var10 Addr) (var11 Heap) (var12 HeapObject) (var13 Addr)) (or (not (and (and (Inv_Heap var13 var12) (_Glue7 var11 var10 var9 var13 var8)) (and (and (and (and (and (and (and (and (and (and (= (read var7 var13) var12) (valid var7 var13)) true) (= (getnode var8) var6)) (= (|node::data_0| var6) var5)) (= (|node::data_1| var6) var4)) (= (|node::prev| var6) var3)) (= (|node::data_2| var6) var2)) (= (node var5 var10 var4 var3 var2) var1)) (= (O_node var1) var0)) (= (write var11 var13 var0) var7)))) (_Glue9 var7 var10 var9 var13 var12))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Int) (var3 Addr) (var4 Int) (var5 Int) (var6 node) (var7 HeapObject) (var8 Heap) (var9 HeapObject) (var10 Addr) (var11 Int) (var12 Addr) (var13 Heap)) (or (not (and (_Glue7 var13 var12 var11 var10 var9) (and (and (and (and (and (and (and (and (and (= (read var8 var10) var7) (not (valid var8 var10))) (= (getnode var9) var6)) (= (|node::data_0| var6) var5)) (= (|node::data_1| var6) var4)) (= (|node::prev| var6) var3)) (= (|node::data_2| var6) var2)) (= (node var5 var12 var4 var3 var2) var1)) (= (O_node var1) var0)) (= (write var13 var10 var0) var8)))) (_Glue9 var8 var12 var11 var10 var7))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Int) (var4 Int) (var5 Addr) (var6 Int) (var7 node) (var8 HeapObject) (var9 Addr) (var10 Int) (var11 Addr) (var12 Heap)) (or (not (and (_Glue9 var12 var11 var10 var9 var8) (and (and (and (and (and (and (and (and (and (and (and (= (getnode var8) var7) (= (|node::data_0| var7) var6)) (= (|node::next| var7) var5)) (= (|node::data_1| var7) var4)) (= (|node::data_2| var7) var3)) (<= 0 (+ (+ var10 1) (- 1)))) (= nullAddr var2)) (not (= var11 var2))) (not (= var2 var9))) (= (node var6 var5 var4 var2 var3) var1)) (= (O_node var1) var0)) (valid var12 var9)))) (Inv_Heap var9 var0))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Int) (var4 Int) (var5 Addr) (var6 Int) (var7 node) (var8 Heap) (var9 HeapObject) (var10 Addr) (var11 Int) (var12 Heap) (var13 HeapObject) (var14 Addr)) (or (not (and (and (Inv_Heap var14 var13) (_Glue9 var12 var14 var11 var10 var9)) (and (and (and (and (and (and (and (and (and (and (and (and (and (and (= (read var8 var14) var13) (valid var8 var14)) true) (= (getnode var9) var7)) (= (|node::data_0| var7) var6)) (= (|node::next| var7) var5)) (= (|node::data_1| var7) var4)) (= (|node::data_2| var7) var3)) (<= 0 (+ (+ var11 1) (- 1)))) (= nullAddr var2)) (not (= var14 var2))) (not (= var2 var10))) (= (node var6 var5 var4 var2 var3) var1)) (= (O_node var1) var0)) (= (write var12 var10 var0) var8)))) (_Glue11 var8 var14 var11 var10 var13))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Int) (var4 Int) (var5 Addr) (var6 Int) (var7 node) (var8 HeapObject) (var9 Heap) (var10 HeapObject) (var11 Addr) (var12 Int) (var13 Addr) (var14 Heap)) (or (not (and (_Glue9 var14 var13 var12 var11 var10) (and (and (and (and (and (and (and (and (and (and (and (and (and (= (read var9 var13) var8) (not (valid var9 var13))) (= (getnode var10) var7)) (= (|node::data_0| var7) var6)) (= (|node::next| var7) var5)) (= (|node::data_1| var7) var4)) (= (|node::data_2| var7) var3)) (<= 0 (+ (+ var12 1) (- 1)))) (= nullAddr var2)) (not (= var13 var2))) (not (= var2 var11))) (= (node var6 var5 var4 var2 var3) var1)) (= (O_node var1) var0)) (= (write var14 var11 var0) var9)))) (_Glue11 var9 var13 var12 var11 var8))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Int) (var3 Int) (var4 Addr) (var5 Int) (var6 node) (var7 HeapObject) (var8 Addr) (var9 Int) (var10 Addr) (var11 Heap)) (or (not (and (_Glue11 var11 var10 var9 var8 var7) (and (and (and (and (and (and (and (= (getnode var7) var6) (= (|node::data_0| var6) var5)) (= (|node::next| var6) var4)) (= (|node::data_1| var6) var3)) (= (|node::data_2| var6) var2)) (= (node var5 var4 var3 var8 var2) var1)) (= (O_node var1) var0)) (valid var11 var10)))) (Inv_Heap var10 var0))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 node) (var3 Int) (var4 Int) (var5 Addr) (var6 Int) (var7 node) (var8 HeapObject) (var9 Addr) (var10 Int) (var11 Addr) (var12 Heap)) (or (not (and (_Glue11 var12 var11 var10 var9 var8) (and (and (and (and (and (and (and (= (getnode var8) var7) (= (|node::data_0| var7) var6)) (= (|node::next| var7) var5)) (= (|node::data_1| var7) var4)) (= (|node::data_2| var7) var3)) (= (node var6 var5 var4 var9 var3) var2)) (= (O_node var2) var1)) (= (write var12 var11 var1) var0)))) (inv_main578_3 var0 var10 var9))))
(assert (forall ((var0 Addr) (var1 node) (var2 Heap) (var3 HeapObject) (var4 Addr)) (or (not (and (and (Inv_Heap var4 var3) (inv_main599_3_12 var2 var4)) (and (and (and (and (= (read var2 var4) var3) (= (getnode var3) var1)) (= (|node::next| var1) var0)) (= nullAddr var0)) (valid var2 var4)))) (inv_main_13 var2 var4))))
(assert (forall ((var0 Addr) (var1 node) (var2 HeapObject) (var3 Addr) (var4 Heap)) (or (not (and (inv_main599_3_12 var4 var3) (and (and (and (and (= (read var4 var3) var2) (= (getnode var2) var1)) (= (|node::next| var1) var0)) (= nullAddr var0)) (not (valid var4 var3))))) (inv_main_13 var4 var3))))
(assert (forall ((var0 AllocResHeap) (var1 HeapObject) (var2 node) (var3 Addr) (var4 Int) (var5 Heap)) (or (not (and (inv_main578_3 var5 (+ var4 1) var3) (and (= (O_node var2) var1) (= (alloc var5 var1) var0)))) (Inv_Heap (newAddr var0) var1))))
(assert (forall ((var0 AllocResHeap) (var1 HeapObject) (var2 node) (var3 Heap) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Int) (var8 Heap) (var9 HeapObject) (var10 Addr)) (or (not (and (and (and (Inv_Heap var10 var9) (inv_main578_3 var8 (+ var7 1) var6)) (inv_main578_3 var5 (+ var7 1) var4)) (and (and (and (and (and (and (= (read var3 var10) var9) (valid var3 var10)) true) (= (O_node var2) var1)) (= (AllocResHeap var3 var10) var0)) (= (alloc var8 var1) var0)) true))) (_Glue13 var7 var10 var3 var9))))
(assert (forall ((var0 AllocResHeap) (var1 HeapObject) (var2 node) (var3 HeapObject) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Int) (var10 Heap)) (or (not (and (and (inv_main578_3 var10 (+ var9 1) var8) (inv_main578_3 var7 (+ var9 1) var6)) (and (and (and (and (and (= (read var5 var4) var3) (not (valid var5 var4))) (= (O_node var2) var1)) (= (AllocResHeap var5 var4) var0)) (= (alloc var10 var1) var0)) true))) (_Glue13 var9 var4 var5 var3))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Int) (var3 Addr) (var4 Int) (var5 Addr) (var6 node) (var7 Addr) (var8 Heap) (var9 HeapObject) (var10 Heap) (var11 Addr) (var12 Int)) (or (not (and (and (_Glue13 var12 var11 var10 var9) (inv_main578_3 var8 (+ var12 1) var7)) (and (and (and (and (and (and (and (= (getnode var9) var6) (= (|node::next| var6) var5)) (= (|node::data_1| var6) var4)) (= (|node::prev| var6) var3)) (= (|node::data_2| var6) var2)) (= (node 0 var5 var4 var3 var2) var1)) (= (O_node var1) var0)) (valid var10 var11)))) (Inv_Heap var11 var0))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 node) (var3 Int) (var4 Addr) (var5 Int) (var6 Addr) (var7 node) (var8 Addr) (var9 Heap) (var10 HeapObject) (var11 Heap) (var12 Addr) (var13 Int)) (or (not (and (and (_Glue13 var13 var12 var11 var10) (inv_main578_3 var9 (+ var13 1) var8)) (and (and (and (and (and (and (and (= (getnode var10) var7) (= (|node::next| var7) var6)) (= (|node::data_1| var7) var5)) (= (|node::prev| var7) var4)) (= (|node::data_2| var7) var3)) (= (node 0 var6 var5 var4 var3) var2)) (= (O_node var2) var1)) (= (write var11 var12 var1) var0)))) (_Glue14 var12 var13 var0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Heap) (var3 Int) (var4 HeapObject) (var5 Addr)) (or (not (and (and (and (Inv_Heap var5 var4) (_Glue14 var5 var3 var2)) (inv_main578_3 var1 (+ var3 1) var0)) (and (= (read var2 var5) var4) (valid var2 var5)))) (_Glue15 var2 var3 var5 var4))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Heap) (var3 Heap) (var4 Int) (var5 Addr)) (or (not (and (and (_Glue14 var5 var4 var3) (inv_main578_3 var2 (+ var4 1) var1)) (and (= (read var3 var5) var0) (not (valid var3 var5))))) (_Glue15 var3 var4 var5 var0))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Int) (var3 Addr) (var4 Addr) (var5 Int) (var6 node) (var7 Addr) (var8 Heap) (var9 HeapObject) (var10 Addr) (var11 Int) (var12 Heap)) (or (not (and (and (_Glue15 var12 var11 var10 var9) (inv_main578_3 var8 (+ var11 1) var7)) (and (and (and (and (and (and (and (= (getnode var9) var6) (= (|node::data_0| var6) var5)) (= (|node::next| var6) var4)) (= (|node::prev| var6) var3)) (= (|node::data_2| var6) var2)) (= (node var5 var4 0 var3 var2) var1)) (= (O_node var1) var0)) (valid var12 var10)))) (Inv_Heap var10 var0))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 node) (var3 Int) (var4 Addr) (var5 Addr) (var6 Int) (var7 node) (var8 Addr) (var9 Heap) (var10 HeapObject) (var11 Addr) (var12 Int) (var13 Heap)) (or (not (and (and (_Glue15 var13 var12 var11 var10) (inv_main578_3 var9 (+ var12 1) var8)) (and (and (and (and (and (and (and (= (getnode var10) var7) (= (|node::data_0| var7) var6)) (= (|node::next| var7) var5)) (= (|node::prev| var7) var4)) (= (|node::data_2| var7) var3)) (= (node var6 var5 0 var4 var3) var2)) (= (O_node var2) var1)) (= (write var13 var11 var1) var0)))) (_Glue16 var11 var12 var0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Heap) (var3 Int) (var4 HeapObject) (var5 Addr)) (or (not (and (and (and (Inv_Heap var5 var4) (_Glue16 var5 var3 var2)) (inv_main578_3 var1 (+ var3 1) var0)) (and (= (read var2 var5) var4) (valid var2 var5)))) (_Glue17 var2 var3 var5 var4))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Heap) (var3 Heap) (var4 Int) (var5 Addr)) (or (not (and (and (_Glue16 var5 var4 var3) (inv_main578_3 var2 (+ var4 1) var1)) (and (= (read var3 var5) var0) (not (valid var3 var5))))) (_Glue17 var3 var4 var5 var0))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Int) (var4 Addr) (var5 Int) (var6 node) (var7 Addr) (var8 Heap) (var9 HeapObject) (var10 Addr) (var11 Int) (var12 Heap)) (or (not (and (and (_Glue17 var12 var11 var10 var9) (inv_main578_3 var8 (+ var11 1) var7)) (and (and (and (and (and (and (and (= (getnode var9) var6) (= (|node::data_0| var6) var5)) (= (|node::next| var6) var4)) (= (|node::data_1| var6) var3)) (= (|node::prev| var6) var2)) (= (node var5 var4 var3 var2 0) var1)) (= (O_node var1) var0)) (valid var12 var10)))) (Inv_Heap var10 var0))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 node) (var3 Addr) (var4 Int) (var5 Addr) (var6 Int) (var7 node) (var8 Addr) (var9 Heap) (var10 HeapObject) (var11 Addr) (var12 Int) (var13 Heap)) (or (not (and (and (_Glue17 var13 var12 var11 var10) (inv_main578_3 var9 (+ var12 1) var8)) (and (and (and (and (and (and (and (= (getnode var10) var7) (= (|node::data_0| var7) var6)) (= (|node::next| var7) var5)) (= (|node::data_1| var7) var4)) (= (|node::prev| var7) var3)) (= (node var6 var5 var4 var3 0) var2)) (= (O_node var2) var1)) (= (write var13 var11 var1) var0)))) (_Glue18 var11 var12 var0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Heap) (var3 Int) (var4 HeapObject) (var5 Addr)) (or (not (and (and (and (Inv_Heap var5 var4) (_Glue18 var5 var3 var2)) (inv_main578_3 var1 (+ var3 1) var0)) (and (= (read var2 var5) var4) (valid var2 var5)))) (_Glue19 var2 var3 var5 var4))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Heap) (var3 Heap) (var4 Int) (var5 Addr)) (or (not (and (and (_Glue18 var5 var4 var3) (inv_main578_3 var2 (+ var4 1) var1)) (and (= (read var3 var5) var0) (not (valid var3 var5))))) (_Glue19 var3 var4 var5 var0))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Int) (var3 Addr) (var4 Int) (var5 Int) (var6 node) (var7 Addr) (var8 Heap) (var9 HeapObject) (var10 Addr) (var11 Int) (var12 Heap)) (or (not (and (and (_Glue19 var12 var11 var10 var9) (inv_main578_3 var8 (+ var11 1) var7)) (and (and (and (and (and (and (and (and (and (and (= (getnode var9) var6) (= (|node::data_0| var6) var5)) (= (|node::data_1| var6) var4)) (= (|node::prev| var6) var3)) (= (|node::data_2| var6) var2)) (<= 0 (+ (+ var11 1) (- 1)))) (= nullAddr var7)) (not (= var7 var10))) (= (node var5 var7 var4 var3 var2) var1)) (= (O_node var1) var0)) (valid var12 var10)))) (Inv_Heap var10 var0))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 node) (var3 Int) (var4 Addr) (var5 Int) (var6 Int) (var7 node) (var8 Addr) (var9 Heap) (var10 HeapObject) (var11 Addr) (var12 Int) (var13 Heap)) (or (not (and (and (_Glue19 var13 var12 var11 var10) (inv_main578_3 var9 (+ var12 1) var8)) (and (and (and (and (and (and (and (and (and (and (= (getnode var10) var7) (= (|node::data_0| var7) var6)) (= (|node::data_1| var7) var5)) (= (|node::prev| var7) var4)) (= (|node::data_2| var7) var3)) (<= 0 (+ (+ var12 1) (- 1)))) (= nullAddr var8)) (not (= var8 var11))) (= (node var6 var8 var5 var4 var3) var2)) (= (O_node var2) var1)) (= (write var13 var11 var1) var0)))) (_Glue20 var11 var12 var8 var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Int) (var3 HeapObject) (var4 Addr)) (or (not (and (and (Inv_Heap var4 var3) (_Glue20 var4 var2 var1 var0)) (and (= (read var0 var4) var3) (valid var0 var4)))) (_Glue21 var0 var1 var2 var4 var3))))
(assert (forall ((var0 HeapObject) (var1 Heap) (var2 Addr) (var3 Int) (var4 Addr)) (or (not (and (_Glue20 var4 var3 var2 var1) (and (= (read var1 var4) var0) (not (valid var1 var4))))) (_Glue21 var1 var2 var3 var4 var0))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Int) (var3 Int) (var4 Addr) (var5 Int) (var6 node) (var7 HeapObject) (var8 Addr) (var9 Int) (var10 Addr) (var11 Heap)) (or (not (and (_Glue21 var11 var10 var9 var8 var7) (and (and (and (and (and (and (and (= (getnode var7) var6) (= (|node::data_0| var6) var5)) (= (|node::next| var6) var4)) (= (|node::data_1| var6) var3)) (= (|node::data_2| var6) var2)) (= (node var5 var4 var3 var10 var2) var1)) (= (O_node var1) var0)) (valid var11 var8)))) (Inv_Heap var8 var0))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 node) (var3 Int) (var4 Int) (var5 Addr) (var6 Int) (var7 node) (var8 HeapObject) (var9 Addr) (var10 Int) (var11 Addr) (var12 Heap)) (or (not (and (_Glue21 var12 var11 var10 var9 var8) (and (and (and (and (and (and (and (= (getnode var8) var7) (= (|node::data_0| var7) var6)) (= (|node::next| var7) var5)) (= (|node::data_1| var7) var4)) (= (|node::data_2| var7) var3)) (= (node var6 var5 var4 var11 var3) var2)) (= (O_node var2) var1)) (= (write var12 var9 var1) var0)))) (inv_main578_3 var0 var10 var9))))
(assert (forall ((var0 Int) (var1 Heap) (var2 Addr)) (or (not (and (and (= nullAddr var2) (= emptyHeap var1)) (= var0 5))) (inv_main578_3 var1 var0 var2))))
(assert (forall ((var0 Int) (var1 Addr) (var2 node) (var3 Addr) (var4 Int) (var5 Heap) (var6 HeapObject) (var7 Addr)) (or (not (and (and (Inv_Heap var7 var6) (inv_main_13 var5 var7)) (and (and (and (and (and (and (and (and (and (and (not (= var4 0)) (not (= var3 var7))) (= nullAddr var3)) (= (read var5 var7) var6)) (= (getnode var6) var2)) (= (|node::prev| var2) var1)) (= (|node::data_1| var2) 0)) (= (|node::data_0| var2) 0)) (= (|node::data_2| var2) var4)) (valid var5 var7)) (= var0 1)))) (inv_main608_8_28 var5 var7 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 node) (var3 Addr) (var4 Heap) (var5 HeapObject) (var6 Addr)) (or (not (and (and (Inv_Heap var6 var5) (inv_main_13 var4 var6)) (and (and (and (and (and (and (and (and (and (not (= var3 var6)) (= nullAddr var3)) (= (read var4 var6) var5)) (= (getnode var5) var2)) (= (|node::prev| var2) var1)) (= (|node::data_1| var2) 0)) (= (|node::data_0| var2) 0)) (= (|node::data_2| var2) 0)) (valid var4 var6)) (= var0 0)))) (inv_main608_8_28 var4 var6 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 node) (var3 HeapObject) (var4 Addr) (var5 Int) (var6 Addr) (var7 Heap)) (or (not (and (inv_main_13 var7 var6) (and (and (and (and (and (and (and (and (and (and (not (= var5 0)) (not (= var4 var6))) (= nullAddr var4)) (= (read var7 var6) var3)) (= (getnode var3) var2)) (= (|node::prev| var2) var1)) (= (|node::data_1| var2) 0)) (= (|node::data_0| var2) 0)) (= (|node::data_2| var2) var5)) (not (valid var7 var6))) (= var0 1)))) (inv_main608_8_28 var7 var6 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 node) (var3 HeapObject) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main_13 var6 var5) (and (and (and (and (and (and (and (and (and (not (= var4 var5)) (= nullAddr var4)) (= (read var6 var5) var3)) (= (getnode var3) var2)) (= (|node::prev| var2) var1)) (= (|node::data_1| var2) 0)) (= (|node::data_0| var2) 0)) (= (|node::data_2| var2) 0)) (not (valid var6 var5))) (= var0 0)))) (inv_main608_8_28 var6 var5 var1 var0))))
(assert (forall ((var0 Int) (var1 node) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap) (var6 HeapObject) (var7 Addr)) (or (not (and (and (Inv_Heap var7 var6) (inv_main599_3_12 var5 var7)) (and (and (and (and (and (and (and (and (and (not (= var4 0)) (not (= var3 var2))) (= (read var5 var7) var6)) (= (getnode var6) var1)) (= (|node::next| var1) var2)) (= nullAddr var3)) (= (|node::data_1| var1) var4)) (= (|node::data_0| var1) 0)) (valid var5 var7)) (= var0 1)))) (inv_main601_8_19 var5 var7 var0))))
(assert (forall ((var0 Int) (var1 node) (var2 HeapObject) (var3 Addr) (var4 Addr) (var5 Int) (var6 Addr) (var7 Heap)) (or (not (and (inv_main599_3_12 var7 var6) (and (and (and (and (and (and (and (and (and (not (= var5 0)) (not (= var4 var3))) (= (read var7 var6) var2)) (= (getnode var2) var1)) (= (|node::next| var1) var3)) (= nullAddr var4)) (= (|node::data_1| var1) var5)) (= (|node::data_0| var1) 0)) (not (valid var7 var6))) (= var0 1)))) (inv_main601_8_19 var7 var6 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap)) (or (not (and (inv_main601_8_19 var2 var1 var0) (not (= var0 0)))) inv_main_32)))
(assert (forall ((var0 Addr) (var1 Int) (var2 Heap)) (or (not (and (inv_main578_3 var2 var1 var0) (not (<= 0 (+ var1 (- 1)))))) (inv_main599_3_12 var2 var0))))
(check-sat)
