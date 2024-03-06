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

(declare-datatypes ((HeapObject 0) (internal_node 0) (sll 0))
                   (((O_Int (getInt Int)) (O_UInt (getUInt Int)) (O_Addr (getAddr Addr)) (O_AddrRange (getAddrRange AddrRange)) (O_internal_node (getinternal_node internal_node)) (O_sll (getsll sll)) (defObj))
                   ((internal_node (|internal_node::next| Addr)))
                   ((sll (|sll::next| Addr) (|sll::shared| Addr)))))
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
(declare-fun inv_main2445_9 (Heap Addr Addr) Bool)
(declare-fun _Glue15 (Heap Addr Addr Addr Addr HeapObject) Bool)
(declare-fun Inv_Heap (Addr HeapObject) Bool)
(declare-fun _Glue17 (Heap Addr Addr Addr HeapObject) Bool)
(declare-fun _Glue13 (Heap Addr Addr Addr Addr Addr HeapObject) Bool)
(declare-fun _Glue7 (Heap Addr Addr Addr HeapObject) Bool)
(declare-fun inv_main_10 (Heap Addr Addr Addr) Bool)
(declare-fun _Glue18 (Addr Addr Addr Heap Addr HeapObject) Bool)
(declare-fun inv_main2415_5 (Heap Addr Addr) Bool)
(declare-fun _Glue5 (Addr Addr Heap HeapObject) Bool)
(declare-fun _Glue9 (Heap Addr Addr HeapObject) Bool)
(declare-fun inv_main2437_9 (Heap Addr Addr Addr) Bool)
(declare-fun _Glue11 (Addr Addr Addr Addr Heap HeapObject) Bool)
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main2437_9 var5 var4 var3 var2) (and (and (and (= nullAddr var1) (not (= var2 var1))) (= defObj var0)) (valid var5 var3)))) (Inv_Heap var3 var0))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 internal_node) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Heap) (var8 HeapObject) (var9 Addr)) (or (not (and (and (Inv_Heap var9 var8) (inv_main2437_9 var7 var6 var5 var9)) (and (and (and (and (and (and (and (and (= (read var4 var9) var8) (= (getinternal_node var8) var3)) (= (|internal_node::next| var3) var2)) (valid var4 var9)) true) (= nullAddr var1)) (not (= var9 var1))) (= defObj var0)) (= (write var7 var5 var0) var4)))) (inv_main2437_9 var4 var6 var9 var2))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 internal_node) (var4 HeapObject) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main2437_9 var9 var8 var7 var6) (and (and (and (and (and (and (and (= (read var5 var6) var4) (= (getinternal_node var4) var3)) (= (|internal_node::next| var3) var2)) (not (valid var5 var6))) (= nullAddr var1)) (not (= var6 var1))) (= defObj var0)) (= (write var9 var7 var0) var5)))) (inv_main2437_9 var5 var8 var6 var2))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main2445_9 var4 var3 var2) (and (and (and (= nullAddr var1) (not (= var2 var1))) (= defObj var0)) (valid var4 var3)))) (Inv_Heap var3 var0))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 sll) (var4 Heap) (var5 Addr) (var6 Heap) (var7 HeapObject) (var8 Addr)) (or (not (and (and (Inv_Heap var8 var7) (inv_main2445_9 var6 var5 var8)) (and (and (and (and (and (and (and (and (= (read var4 var8) var7) (= (getsll var7) var3)) (= (|sll::next| var3) var2)) (valid var4 var8)) true) (= nullAddr var1)) (not (= var8 var1))) (= defObj var0)) (= (write var6 var5 var0) var4)))) (inv_main2445_9 var4 var8 var2))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 sll) (var4 HeapObject) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main2445_9 var8 var7 var6) (and (and (and (and (and (and (and (= (read var5 var6) var4) (= (getsll var4) var3)) (= (|sll::next| var3) var2)) (not (valid var5 var6))) (= nullAddr var1)) (not (= var6 var1))) (= defObj var0)) (= (write var8 var7 var0) var5)))) (inv_main2445_9 var5 var6 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 HeapObject) (var5 Addr)) (not (and (and (Inv_Heap var5 var4) (inv_main2437_9 var3 var2 var5 var1)) (and (and (and (and (not (= var5 var0)) (= (read var3 var5) var4)) (= defObj var4)) (= nullAddr var0)) (valid var3 var5))))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (not (and (inv_main2437_9 var5 var4 var3 var2) (and (and (and (and (not (= var3 var1)) (= (read var5 var3) var0)) (= defObj var0)) (= nullAddr var1)) (not (valid var5 var3)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 HeapObject) (var4 Addr)) (not (and (and (Inv_Heap var4 var3) (inv_main2445_9 var2 var4 var1)) (and (and (and (and (not (= var4 var0)) (= (read var2 var4) var3)) (= defObj var3)) (= nullAddr var0)) (valid var2 var4))))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main2445_9 var4 var3 var2) (and (and (and (and (not (= var3 var1)) (= (read var4 var3) var0)) (= defObj var0)) (= nullAddr var1)) (not (valid var4 var3)))))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main2437_9 var4 var3 var2 var1) (and (and (and (= nullAddr var1) (not (= var3 var1))) (= defObj var0)) (valid var4 var2)))) (Inv_Heap var2 var0))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 sll) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Heap) (var7 HeapObject) (var8 Addr)) (or (not (and (and (Inv_Heap var8 var7) (inv_main2437_9 var6 var8 var5 var4)) (and (and (and (and (and (and (and (and (= (read var3 var8) var7) (= (getsll var7) var2)) (= (|sll::next| var2) var1)) (valid var3 var8)) true) (= nullAddr var4)) (not (= var8 var4))) (= defObj var0)) (= (write var6 var5 var0) var3)))) (inv_main2445_9 var3 var8 var1))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 sll) (var3 HeapObject) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main2437_9 var8 var7 var6 var5) (and (and (and (and (and (and (and (= (read var4 var7) var3) (= (getsll var3) var2)) (= (|sll::next| var2) var1)) (not (valid var4 var7))) (= nullAddr var5)) (not (= var7 var5))) (= defObj var0)) (= (write var8 var6 var0) var4)))) (inv_main2445_9 var4 var7 var1))))
(assert (forall ((var0 AllocResHeap) (var1 HeapObject) (var2 sll) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main_10 var6 var5 var4 var3) (and (= (O_sll var2) var1) (= (alloc var6 var1) var0)))) (Inv_Heap (newAddr var0) var1))))
(assert (forall ((var0 AllocResHeap) (var1 HeapObject) (var2 sll) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap) (var8 HeapObject) (var9 Addr)) (or (not (and (and (Inv_Heap var9 var8) (inv_main_10 var7 var6 var5 var4)) (and (and (and (and (and (= (read var3 var9) var8) (valid var3 var9)) true) (= (O_sll var2) var1)) (= (AllocResHeap var3 var9) var0)) (= (alloc var7 var1) var0)))) (_Glue11 var4 var6 var5 var9 var3 var8))))
(assert (forall ((var0 AllocResHeap) (var1 HeapObject) (var2 sll) (var3 HeapObject) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main_10 var9 var8 var7 var6) (and (and (and (and (= (read var5 var4) var3) (not (valid var5 var4))) (= (O_sll var2) var1)) (= (AllocResHeap var5 var4) var0)) (= (alloc var9 var1) var0)))) (_Glue11 var6 var8 var7 var4 var5 var3))))
(assert (forall ((var0 HeapObject) (var1 sll) (var2 Addr) (var3 Addr) (var4 sll) (var5 HeapObject) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr)) (or (not (and (_Glue11 var10 var9 var8 var7 var6 var5) (and (and (and (and (and (= (getsll var5) var4) (= (|sll::shared| var4) var3)) (= nullAddr var2)) (= (sll var2 var3) var1)) (= (O_sll var1) var0)) (valid var6 var7)))) (Inv_Heap var7 var0))))
(assert (forall ((var0 HeapObject) (var1 sll) (var2 Addr) (var3 Addr) (var4 sll) (var5 Heap) (var6 HeapObject) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Addr) (var11 HeapObject) (var12 Addr)) (or (not (and (and (Inv_Heap var12 var11) (_Glue11 var10 var9 var8 var12 var7 var6)) (and (and (and (and (and (and (and (and (= (read var5 var12) var11) (valid var5 var12)) true) (= (getsll var6) var4)) (= (|sll::shared| var4) var3)) (= nullAddr var2)) (= (sll var2 var3) var1)) (= (O_sll var1) var0)) (= (write var7 var12 var0) var5)))) (_Glue13 var5 var2 var10 var9 var8 var12 var11))))
(assert (forall ((var0 HeapObject) (var1 sll) (var2 Addr) (var3 Addr) (var4 sll) (var5 HeapObject) (var6 Heap) (var7 HeapObject) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr)) (or (not (and (_Glue11 var12 var11 var10 var9 var8 var7) (and (and (and (and (and (and (and (= (read var6 var9) var5) (not (valid var6 var9))) (= (getsll var7) var4)) (= (|sll::shared| var4) var3)) (= nullAddr var2)) (= (sll var2 var3) var1)) (= (O_sll var1) var0)) (= (write var8 var9 var0) var6)))) (_Glue13 var6 var2 var12 var11 var10 var9 var5))))
(assert (forall ((var0 HeapObject) (var1 sll) (var2 Addr) (var3 sll) (var4 HeapObject) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (_Glue13 var10 var9 var8 var7 var6 var5 var4) (and (and (and (and (= (getsll var4) var3) (= (|sll::next| var3) var2)) (= (sll var2 var9) var1)) (= (O_sll var1) var0)) (valid var10 var5)))) (Inv_Heap var5 var0))))
(assert (forall ((var0 HeapObject) (var1 sll) (var2 Addr) (var3 sll) (var4 Heap) (var5 HeapObject) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap) (var11 HeapObject) (var12 Addr)) (or (not (and (and (Inv_Heap var12 var11) (_Glue13 var10 var9 var12 var8 var7 var6 var5)) (and (and (and (and (and (and (and (= (read var4 var12) var11) (valid var4 var12)) true) (= (getsll var5) var3)) (= (|sll::next| var3) var2)) (= (sll var2 var9) var1)) (= (O_sll var1) var0)) (= (write var10 var6 var0) var4)))) (_Glue15 var4 var12 var8 var7 var6 var11))))
(assert (forall ((var0 HeapObject) (var1 sll) (var2 Addr) (var3 sll) (var4 HeapObject) (var5 Heap) (var6 HeapObject) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Heap)) (or (not (and (_Glue13 var12 var11 var10 var9 var8 var7 var6) (and (and (and (and (and (and (= (read var5 var10) var4) (not (valid var5 var10))) (= (getsll var6) var3)) (= (|sll::next| var3) var2)) (= (sll var2 var11) var1)) (= (O_sll var1) var0)) (= (write var12 var7 var0) var5)))) (_Glue15 var5 var10 var9 var8 var7 var4))))
(assert (forall ((var0 HeapObject) (var1 sll) (var2 Addr) (var3 sll) (var4 HeapObject) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (_Glue15 var9 var8 var7 var6 var5 var4) (and (and (and (and (= (getsll var4) var3) (= (|sll::shared| var3) var2)) (= (sll var5 var2) var1)) (= (O_sll var1) var0)) (valid var9 var8)))) (Inv_Heap var8 var0))))
(assert (forall ((var0 HeapObject) (var1 sll) (var2 Addr) (var3 sll) (var4 Heap) (var5 HeapObject) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap) (var10 HeapObject) (var11 Addr)) (or (not (and (and (Inv_Heap var11 var10) (_Glue15 var9 var11 var8 var7 var6 var5)) (and (and (and (and (and (and (and (= (read var4 var11) var10) (valid var4 var11)) true) (= (getsll var5) var3)) (= (|sll::shared| var3) var2)) (= (sll var6 var2) var1)) (= (O_sll var1) var0)) (= (write var9 var11 var0) var4)))) (_Glue17 var4 var11 var8 var7 var10))))
(assert (forall ((var0 HeapObject) (var1 sll) (var2 Addr) (var3 sll) (var4 HeapObject) (var5 Heap) (var6 HeapObject) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Heap)) (or (not (and (_Glue15 var11 var10 var9 var8 var7 var6) (and (and (and (and (and (and (= (read var5 var10) var4) (not (valid var5 var10))) (= (getsll var6) var3)) (= (|sll::shared| var3) var2)) (= (sll var7 var2) var1)) (= (O_sll var1) var0)) (= (write var11 var10 var0) var5)))) (_Glue17 var5 var10 var9 var8 var4))))
(assert (forall ((var0 sll) (var1 HeapObject) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 HeapObject) (var7 Addr)) (or (not (and (and (Inv_Heap var7 var6) (_Glue17 var5 var4 var3 var2 var1)) (and (and (and (= (getsll var1) var0) (= (|sll::next| var0) var7)) (= (read var5 var7) var6)) (valid var5 var7)))) (_Glue18 var2 var3 var4 var5 var7 var6))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 sll) (var3 HeapObject) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (_Glue17 var7 var6 var5 var4 var3) (and (and (and (= (getsll var3) var2) (= (|sll::next| var2) var1)) (= (read var7 var1) var0)) (not (valid var7 var1))))) (_Glue18 var4 var5 var6 var7 var1 var0))))
(assert (forall ((var0 HeapObject) (var1 sll) (var2 Addr) (var3 sll) (var4 HeapObject) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Addr)) (or (not (and (_Glue18 var9 var8 var7 var6 var5 var4) (and (and (and (and (= (getsll var4) var3) (= (|sll::next| var3) var2)) (= (sll var2 var8) var1)) (= (O_sll var1) var0)) (valid var6 var5)))) (Inv_Heap var5 var0))))
(assert (forall ((var0 HeapObject) (var1 sll) (var2 Addr) (var3 sll) (var4 Addr) (var5 sll) (var6 Heap) (var7 HeapObject) (var8 Addr) (var9 Heap) (var10 Addr) (var11 Addr) (var12 HeapObject) (var13 Addr)) (or (not (and (and (Inv_Heap var13 var12) (_Glue18 var11 var10 var13 var9 var8 var7)) (and (and (and (and (and (and (and (and (and (= (read var6 var13) var12) (= (getsll var12) var5)) (= (|sll::next| var5) var4)) (valid var6 var13)) true) (= (getsll var7) var3)) (= (|sll::next| var3) var2)) (= (sll var2 var10) var1)) (= (O_sll var1) var0)) (= (write var9 var8 var0) var6)))) (inv_main_10 var6 var10 var11 var4))))
(assert (forall ((var0 HeapObject) (var1 sll) (var2 Addr) (var3 sll) (var4 Addr) (var5 sll) (var6 HeapObject) (var7 Heap) (var8 HeapObject) (var9 Addr) (var10 Heap) (var11 Addr) (var12 Addr) (var13 Addr)) (or (not (and (_Glue18 var13 var12 var11 var10 var9 var8) (and (and (and (and (and (and (and (and (= (read var7 var11) var6) (= (getsll var6) var5)) (= (|sll::next| var5) var4)) (not (valid var7 var11))) (= (getsll var8) var3)) (= (|sll::next| var3) var2)) (= (sll var2 var12) var1)) (= (O_sll var1) var0)) (= (write var10 var9 var0) var7)))) (inv_main_10 var7 var12 var13 var4))))
(assert (forall ((var0 Addr) (var1 sll) (var2 Addr) (var3 Addr) (var4 Heap) (var5 HeapObject) (var6 Addr)) (or (not (and (and (Inv_Heap var6 var5) (inv_main_10 var4 var3 var6 var2)) (and (and (and (and (and (not (= var6 var3)) (= (read var4 var6) var5)) (= (getsll var5) var1)) (= (|sll::next| var1) var0)) (= nullAddr var3)) (valid var4 var6)))) (inv_main2445_9 var4 var6 var0))))
(assert (forall ((var0 Addr) (var1 sll) (var2 HeapObject) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main_10 var6 var5 var4 var3) (and (and (and (and (and (not (= var4 var5)) (= (read var6 var4) var2)) (= (getsll var2) var1)) (= (|sll::next| var1) var0)) (= nullAddr var5)) (not (valid var6 var4))))) (inv_main2445_9 var6 var4 var0))))
(assert (forall ((var0 AllocResHeap) (var1 HeapObject) (var2 sll) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main2415_5 var5 var4 var3) (and (= (O_sll var2) var1) (= (alloc var5 var1) var0)))) (Inv_Heap (newAddr var0) var1))))
(assert (forall ((var0 AllocResHeap) (var1 HeapObject) (var2 sll) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Heap) (var7 HeapObject) (var8 Addr)) (or (not (and (and (Inv_Heap var8 var7) (inv_main2415_5 var6 var5 var4)) (and (and (and (and (= (read var3 var8) var7) (valid var3 var8)) (= (O_sll var2) var1)) (= (AllocResHeap var3 var8) var0)) (= (alloc var6 var1) var0)))) (_Glue5 var5 var8 var3 var7))))
(assert (forall ((var0 AllocResHeap) (var1 HeapObject) (var2 sll) (var3 HeapObject) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main2415_5 var8 var7 var6) (and (and (and (and (= (read var5 var4) var3) (not (valid var5 var4))) (= (O_sll var2) var1)) (= (AllocResHeap var5 var4) var0)) (= (alloc var8 var1) var0)))) (_Glue5 var7 var4 var5 var3))))
(assert (forall ((var0 HeapObject) (var1 sll) (var2 Addr) (var3 Addr) (var4 sll) (var5 HeapObject) (var6 Heap) (var7 Addr) (var8 Addr)) (or (not (and (_Glue5 var8 var7 var6 var5) (and (and (and (and (and (= (getsll var5) var4) (= (|sll::shared| var4) var3)) (= nullAddr var2)) (= (sll var2 var3) var1)) (= (O_sll var1) var0)) (valid var6 var7)))) (Inv_Heap var7 var0))))
(assert (forall ((var0 HeapObject) (var1 sll) (var2 Addr) (var3 Addr) (var4 sll) (var5 Heap) (var6 HeapObject) (var7 Heap) (var8 Addr) (var9 HeapObject) (var10 Addr)) (or (not (and (and (Inv_Heap var10 var9) (_Glue5 var8 var10 var7 var6)) (and (and (and (and (and (and (and (= (read var5 var10) var9) (valid var5 var10)) (= (getsll var6) var4)) (= (|sll::shared| var4) var3)) (= nullAddr var2)) (= (sll var2 var3) var1)) (= (O_sll var1) var0)) (= (write var7 var10 var0) var5)))) (_Glue7 var5 var2 var8 var10 var9))))
(assert (forall ((var0 HeapObject) (var1 sll) (var2 Addr) (var3 Addr) (var4 sll) (var5 HeapObject) (var6 Heap) (var7 HeapObject) (var8 Heap) (var9 Addr) (var10 Addr)) (or (not (and (_Glue5 var10 var9 var8 var7) (and (and (and (and (and (and (and (= (read var6 var9) var5) (not (valid var6 var9))) (= (getsll var7) var4)) (= (|sll::shared| var4) var3)) (= nullAddr var2)) (= (sll var2 var3) var1)) (= (O_sll var1) var0)) (= (write var8 var9 var0) var6)))) (_Glue7 var6 var2 var10 var9 var5))))
(assert (forall ((var0 HeapObject) (var1 sll) (var2 Addr) (var3 sll) (var4 HeapObject) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (_Glue7 var8 var7 var6 var5 var4) (and (and (and (and (= (getsll var4) var3) (= (|sll::next| var3) var2)) (= (sll var2 var7) var1)) (= (O_sll var1) var0)) (valid var8 var5)))) (Inv_Heap var5 var0))))
(assert (forall ((var0 HeapObject) (var1 sll) (var2 Addr) (var3 sll) (var4 Heap) (var5 HeapObject) (var6 Addr) (var7 Addr) (var8 Heap) (var9 HeapObject) (var10 Addr)) (or (not (and (and (Inv_Heap var10 var9) (_Glue7 var8 var7 var6 var10 var5)) (and (and (and (and (and (and (= (read var4 var10) var9) (valid var4 var10)) (= (getsll var5) var3)) (= (|sll::next| var3) var2)) (= (sll var2 var7) var1)) (= (O_sll var1) var0)) (= (write var8 var10 var0) var4)))) (_Glue9 var4 var6 var10 var9))))
(assert (forall ((var0 HeapObject) (var1 sll) (var2 Addr) (var3 sll) (var4 HeapObject) (var5 Heap) (var6 HeapObject) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (_Glue7 var10 var9 var8 var7 var6) (and (and (and (and (and (and (= (read var5 var7) var4) (not (valid var5 var7))) (= (getsll var6) var3)) (= (|sll::next| var3) var2)) (= (sll var2 var9) var1)) (= (O_sll var1) var0)) (= (write var10 var7 var0) var5)))) (_Glue9 var5 var8 var7 var4))))
(assert (forall ((var0 HeapObject) (var1 sll) (var2 Addr) (var3 sll) (var4 HeapObject) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (_Glue9 var7 var6 var5 var4) (and (and (and (and (= (getsll var4) var3) (= (|sll::next| var3) var2)) (= (sll var2 var6) var1)) (= (O_sll var1) var0)) (valid var7 var5)))) (Inv_Heap var5 var0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 HeapObject) (var3 sll) (var4 Addr) (var5 sll) (var6 HeapObject) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (_Glue9 var9 var8 var7 var6) (and (and (and (and (and (= (getsll var6) var5) (= (|sll::next| var5) var4)) (= (sll var4 var8) var3)) (= (O_sll var3) var2)) (= (write var9 var7 var2) var1)) (= var0 var7)))) (inv_main_10 var1 var8 var7 var0))))
(assert (forall ((var0 AllocResHeap) (var1 Heap) (var2 HeapObject) (var3 internal_node)) (or (not (and (and (= (O_internal_node var3) var2) (= (alloc var1 var2) var0)) (= emptyHeap var1))) (Inv_Heap (newAddr var0) var2))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 HeapObject) (var3 internal_node) (var4 AllocResHeap) (var5 Addr) (var6 Heap) (var7 HeapObject) (var8 internal_node)) (or (not (and (and (and (and (and (and (and (= (O_internal_node var8) var7) (valid var6 var5)) (= (AllocResHeap var6 var5) var4)) (= (O_internal_node var3) var2)) (= (alloc var1 var2) var4)) (= (internal_node var0) var8)) (= nullAddr var0)) (= emptyHeap var1))) (Inv_Heap var5 var7))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 HeapObject) (var4 internal_node) (var5 AllocResHeap) (var6 Heap) (var7 Addr) (var8 Heap) (var9 HeapObject) (var10 internal_node)) (or (not (and (and (and (and (and (and (and (and (= (O_internal_node var10) var9) (= (write var8 var7 var9) var6)) (= (AllocResHeap var8 var7) var5)) (= (O_internal_node var4) var3)) (= (alloc var2 var3) var5)) (= (internal_node var1) var10)) (= nullAddr var1)) (= emptyHeap var2)) (= var0 var7))) (inv_main2415_5 var6 var0 var7))))
(assert (forall ((var0 Addr) (var1 internal_node) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 HeapObject) (var7 Addr)) (or (not (and (and (Inv_Heap var7 var6) (inv_main_10 var5 var7 var4 var3)) (and (and (and (and (and (not (= var7 var2)) (= (read var5 var7) var6)) (= (getinternal_node var6) var1)) (= (|internal_node::next| var1) var0)) (= nullAddr var2)) (valid var5 var7)))) (inv_main2437_9 var5 var4 var7 var0))))
(assert (forall ((var0 Addr) (var1 internal_node) (var2 HeapObject) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main_10 var7 var6 var5 var4) (and (and (and (and (and (not (= var6 var3)) (= (read var7 var6) var2)) (= (getinternal_node var2) var1)) (= (|internal_node::next| var1) var0)) (= nullAddr var3)) (not (valid var7 var6))))) (inv_main2437_9 var7 var5 var6 var0))))
(assert (forall ((var0 AllocResHeap) (var1 HeapObject) (var2 internal_node) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main2415_5 var5 var4 var3) (and (= (O_internal_node var2) var1) (= (alloc var5 var1) var0)))) (Inv_Heap (newAddr var0) var1))))
(assert (forall ((var0 AllocResHeap) (var1 HeapObject) (var2 internal_node) (var3 Addr) (var4 Heap) (var5 HeapObject) (var6 internal_node) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main2415_5 var10 var9 var8) (and (and (and (and (and (and (= (internal_node var7) var6) (= (O_internal_node var6) var5)) (= nullAddr var7)) (valid var4 var3)) (= (O_internal_node var2) var1)) (= (AllocResHeap var4 var3) var0)) (= (alloc var10 var1) var0)))) (Inv_Heap var3 var5))))
(assert (forall ((var0 AllocResHeap) (var1 HeapObject) (var2 internal_node) (var3 Heap) (var4 HeapObject) (var5 internal_node) (var6 Addr) (var7 Addr) (var8 Heap) (var9 HeapObject) (var10 internal_node) (var11 Addr) (var12 Addr) (var13 Heap)) (or (not (and (inv_main2415_5 var13 var12 var11) (and (and (and (and (and (and (and (and (and (= (O_internal_node var10) var9) (valid var8 var11)) (= (internal_node var7) var10)) (= (internal_node var6) var5)) (= (O_internal_node var5) var4)) (= nullAddr var6)) (= (write var3 var7 var4) var8)) (= (O_internal_node var2) var1)) (= (AllocResHeap var3 var7) var0)) (= (alloc var13 var1) var0)))) (Inv_Heap var11 var9))))
(assert (forall ((var0 AllocResHeap) (var1 HeapObject) (var2 internal_node) (var3 Heap) (var4 HeapObject) (var5 internal_node) (var6 Addr) (var7 Addr) (var8 Heap) (var9 HeapObject) (var10 internal_node) (var11 Addr) (var12 internal_node) (var13 Heap) (var14 Addr) (var15 Heap) (var16 HeapObject) (var17 Addr)) (or (not (and (and (Inv_Heap var17 var16) (inv_main2415_5 var15 var14 var17)) (and (and (and (and (and (and (and (and (and (and (and (and (and (and (= (read var13 var17) var16) (= (getinternal_node var16) var12)) (= (|internal_node::next| var12) var11)) (valid var13 var17)) true) (= (O_internal_node var10) var9)) (= (write var8 var17 var9) var13)) (= (internal_node var7) var10)) (= (internal_node var6) var5)) (= (O_internal_node var5) var4)) (= nullAddr var6)) (= (write var3 var7 var4) var8)) (= (O_internal_node var2) var1)) (= (AllocResHeap var3 var7) var0)) (= (alloc var15 var1) var0)))) (inv_main2415_5 var13 var14 var11))))
(assert (forall ((var0 AllocResHeap) (var1 HeapObject) (var2 internal_node) (var3 Heap) (var4 HeapObject) (var5 internal_node) (var6 Addr) (var7 Addr) (var8 Heap) (var9 HeapObject) (var10 internal_node) (var11 Addr) (var12 internal_node) (var13 HeapObject) (var14 Heap) (var15 Addr) (var16 Addr) (var17 Heap)) (or (not (and (inv_main2415_5 var17 var16 var15) (and (and (and (and (and (and (and (and (and (and (and (and (and (= (read var14 var15) var13) (= (getinternal_node var13) var12)) (= (|internal_node::next| var12) var11)) (not (valid var14 var15))) (= (O_internal_node var10) var9)) (= (write var8 var15 var9) var14)) (= (internal_node var7) var10)) (= (internal_node var6) var5)) (= (O_internal_node var5) var4)) (= nullAddr var6)) (= (write var3 var7 var4) var8)) (= (O_internal_node var2) var1)) (= (AllocResHeap var3 var7) var0)) (= (alloc var17 var1) var0)))) (inv_main2415_5 var14 var16 var11))))
(check-sat)
