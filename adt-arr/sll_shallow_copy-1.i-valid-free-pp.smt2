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
                   ((node (|node::next| Addr)))))
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
(declare-fun _Glue4_exp (Heap Addr HeapObject) Bool)
(declare-fun _Glue10_exp (Heap HeapObject Addr Addr HeapObject) Bool)
(declare-fun _Glue13 (Heap Addr HeapObject HeapObject) Bool)
(assert (forall ((var0 AllocResHeap) (var1 Heap) (var2 HeapObject) (var3 node)) (or (not (and (and (= (O_node var3) var2) (= (alloc var1 var2) var0)) (= emptyHeap var1))) (Inv_Heap (newAddr var0) var2))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 node) (var3 AllocResHeap) (var4 AllocResHeap) (var5 Heap) (var6 Addr) (var7 Addr) (var8 HeapObject) (var9 node)) (or (not (and (and (and (and (and (and (and (and (= (O_node var9) var8) (not (= var7 var6))) (not (= var6 var7))) (= (alloc var5 var8) var4)) (= (AllocResHeap var5 var6) var3)) (= (O_node var2) var1)) (= (alloc var0 var1) var3)) (= nullAddr var7)) (= emptyHeap var0))) (Inv_Heap (newAddr var4) var8))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 node) (var3 AllocResHeap) (var4 Heap) (var5 HeapObject) (var6 node) (var7 AllocResHeap) (var8 Addr) (var9 Heap) (var10 Addr) (var11 HeapObject) (var12 node) (var13 Addr)) (or (not (and (and (and (and (and (and (and (and (and (and (and (and (and (= (node var13) var12) (= (O_node var12) var11)) (not (= var10 var13))) (valid var9 var8)) (= (AllocResHeap var9 var13) var7)) (= (O_node var6) var5)) (= (alloc var4 var5) var7)) (not (= var10 var8))) (not (= var8 var10))) (= (AllocResHeap var4 var8) var3)) (= (O_node var2) var1)) (= (alloc var0 var1) var3)) (= nullAddr var10)) (= emptyHeap var0))) (Inv_Heap var8 var11))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 node) (var3 AllocResHeap) (var4 Heap) (var5 HeapObject) (var6 node) (var7 AllocResHeap) (var8 Addr) (var9 Heap) (var10 HeapObject) (var11 node) (var12 Addr) (var13 Heap) (var14 HeapObject) (var15 Addr)) (or (not (and (Inv_Heap var15 var14) (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (= (read var13 var15) var14) (valid var13 var15)) true) (= (node var12) var11)) (= (O_node var11) var10)) (= (write var9 var15 var10) var13)) (not (= var8 var12))) (= (AllocResHeap var9 var12) var7)) (= (O_node var6) var5)) (= (alloc var4 var5) var7)) (not (= var8 var15))) (not (= var15 var8))) (= (AllocResHeap var4 var15) var3)) (= (O_node var2) var1)) (= (alloc var0 var1) var3)) (= nullAddr var8)) (= emptyHeap var0)))) (_Glue4_exp var13 var15 var14))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 node) (var3 AllocResHeap) (var4 Heap) (var5 HeapObject) (var6 node) (var7 AllocResHeap) (var8 Addr) (var9 Heap) (var10 HeapObject) (var11 node) (var12 Addr) (var13 HeapObject) (var14 Addr) (var15 Heap)) (or (not (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (= (read var15 var14) var13) (not (valid var15 var14))) (= (node var12) var11)) (= (O_node var11) var10)) (= (write var9 var14 var10) var15)) (not (= var8 var12))) (= (AllocResHeap var9 var12) var7)) (= (O_node var6) var5)) (= (alloc var4 var5) var7)) (not (= var8 var14))) (not (= var14 var8))) (= (AllocResHeap var4 var14) var3)) (= (O_node var2) var1)) (= (alloc var0 var1) var3)) (= nullAddr var8)) (= emptyHeap var0))) (_Glue4_exp var15 var14 var13))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 HeapObject) (var3 Addr) (var4 Heap)) (or (not (and (_Glue4_exp var4 var3 var2) (and (and (= (getnode var2) var1) (= (O_node var1) var0)) (valid var4 var3)))) (Inv_Heap var3 var0))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Heap) (var3 HeapObject) (var4 Heap) (var5 HeapObject) (var6 Addr)) (not (and (and (Inv_Heap var6 var5) (_Glue4_exp var4 var6 var3)) (and (and (and (and (and (and (= (read var2 var6) var5) (valid var2 var6)) (= defObj var5)) true) (= (getnode var3) var1)) (= (O_node var1) var0)) (= (write var4 var6 var0) var2))))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 HeapObject) (var3 Heap) (var4 HeapObject) (var5 Addr) (var6 Heap)) (not (and (_Glue4_exp var6 var5 var4) (and (and (and (and (and (= (read var3 var5) var2) (not (valid var3 var5))) (= defObj var2)) (= (getnode var4) var1)) (= (O_node var1) var0)) (= (write var6 var5 var0) var3))))))
(assert (forall ((var0 AllocResHeap) (var1 Heap) (var2 HeapObject) (var3 node)) (or (not (and (and (= (O_node var3) var2) (= (alloc var1 var2) var0)) (= emptyHeap var1))) (Inv_Heap (newAddr var0) var2))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 node) (var3 AllocResHeap) (var4 Addr) (var5 Addr) (var6 AllocResHeap) (var7 Heap) (var8 HeapObject) (var9 node)) (or (not (and (and (and (and (and (and (and (= (O_node var9) var8) (= (alloc var7 var8) var6)) (not (= var5 var4))) (= (AllocResHeap var7 var4) var3)) (= (O_node var2) var1)) (= (alloc var0 var1) var3)) (= nullAddr var5)) (= emptyHeap var0))) (Inv_Heap (newAddr var6) var8))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 node) (var3 AllocResHeap) (var4 Heap) (var5 HeapObject) (var6 node) (var7 AllocResHeap) (var8 Addr) (var9 Heap) (var10 Addr) (var11 HeapObject) (var12 node) (var13 Addr)) (or (not (and (and (and (and (and (and (and (and (and (and (and (and (= (node var13) var12) (= (O_node var12) var11)) (not (= var10 var13))) (valid var9 var8)) (= (AllocResHeap var9 var13) var7)) (= (O_node var6) var5)) (= (alloc var4 var5) var7)) (not (= var10 var8))) (= (AllocResHeap var4 var8) var3)) (= (O_node var2) var1)) (= (alloc var0 var1) var3)) (= nullAddr var10)) (= emptyHeap var0))) (Inv_Heap var8 var11))))
(assert (forall ((var0 HeapObject) (var1 Heap) (var2 HeapObject) (var3 node) (var4 AllocResHeap) (var5 Heap) (var6 HeapObject) (var7 node) (var8 AllocResHeap) (var9 Addr) (var10 Heap) (var11 HeapObject) (var12 node) (var13 Addr) (var14 Heap) (var15 HeapObject) (var16 Addr)) (or (not (and (Inv_Heap var16 var15) (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (= (read var14 var16) var15) (valid var14 var16)) true) (= (node var13) var12)) (= (O_node var12) var11)) (= (write var10 var16 var11) var14)) (not (= var9 var13))) (= (AllocResHeap var10 var13) var8)) (= (O_node var7) var6)) (= (alloc var5 var6) var8)) (not (= var9 var16))) (= (AllocResHeap var5 var16) var4)) (= (O_node var3) var2)) (= (alloc var1 var2) var4)) (= nullAddr var9)) (= emptyHeap var1)))) (_Glue10_exp var14 var0 var9 var16 var15))))
(assert (forall ((var0 HeapObject) (var1 Heap) (var2 HeapObject) (var3 node) (var4 AllocResHeap) (var5 Heap) (var6 HeapObject) (var7 node) (var8 AllocResHeap) (var9 Addr) (var10 Heap) (var11 HeapObject) (var12 node) (var13 Addr) (var14 HeapObject) (var15 Addr) (var16 Heap)) (or (not (and (and (and (and (and (and (and (and (and (and (and (and (and (and (= (read var16 var15) var14) (not (valid var16 var15))) (= (node var13) var12)) (= (O_node var12) var11)) (= (write var10 var15 var11) var16)) (not (= var9 var13))) (= (AllocResHeap var10 var13) var8)) (= (O_node var7) var6)) (= (alloc var5 var6) var8)) (not (= var9 var15))) (= (AllocResHeap var5 var15) var4)) (= (O_node var3) var2)) (= (alloc var1 var2) var4)) (= nullAddr var9)) (= emptyHeap var1))) (_Glue10_exp var16 var0 var9 var15 var14))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 HeapObject) (var3 Addr) (var4 Addr) (var5 HeapObject) (var6 Heap)) (or (not (and (_Glue10_exp var6 var5 var4 var3 var2) (and (and (= (getnode var2) var1) (= (O_node var1) var0)) (valid var6 var3)))) (Inv_Heap var3 var0))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Heap) (var3 HeapObject) (var4 HeapObject) (var5 Addr) (var6 Addr) (var7 HeapObject) (var8 Heap)) (or (not (and (_Glue10_exp var8 var7 var6 var5 var4) (and (and (and (and (= defObj var3) (valid var2 var5)) (= (getnode var4) var1)) (= (O_node var1) var0)) (= (write var8 var5 var0) var2)))) (Inv_Heap var5 var3))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Heap) (var3 HeapObject) (var4 Heap) (var5 HeapObject) (var6 Addr) (var7 HeapObject) (var8 Heap) (var9 HeapObject) (var10 Addr)) (or (not (and (and (Inv_Heap var10 var9) (_Glue10_exp var8 var7 var6 var10 var5)) (and (and (and (and (and (and (and (= (read var4 var10) var9) (valid var4 var10)) true) (= defObj var3)) (= (write var4 var10 var3) var2)) (= (getnode var5) var1)) (= (O_node var1) var0)) (= (write var8 var10 var0) var4)))) (_Glue13 var2 var6 var7 var9))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Heap) (var3 HeapObject) (var4 HeapObject) (var5 Heap) (var6 HeapObject) (var7 Addr) (var8 Addr) (var9 HeapObject) (var10 Heap)) (or (not (and (_Glue10_exp var10 var9 var8 var7 var6) (and (and (and (and (and (and (= (read var5 var7) var4) (not (valid var5 var7))) (= defObj var3)) (= (write var5 var7 var3) var2)) (= (getnode var6) var1)) (= (O_node var1) var0)) (= (write var10 var7 var0) var5)))) (_Glue13 var2 var8 var9 var4))))
(assert (forall ((var0 node) (var1 HeapObject) (var2 Addr) (var3 Heap) (var4 HeapObject) (var5 Addr)) (not (and (and (Inv_Heap var5 var4) (_Glue13 var3 var2 var4 var1)) (and (and (and (and (and (= defObj var4) (= (getnode var1) var0)) (= (|node::next| var0) var5)) (not (= var5 var2))) (= (read var3 var5) var4)) (valid var3 var5))))))
(assert (forall ((var0 Addr) (var1 node) (var2 HeapObject) (var3 HeapObject) (var4 Addr) (var5 Heap)) (not (and (_Glue13 var5 var4 var3 var2) (and (and (and (and (and (= defObj var3) (= (getnode var2) var1)) (= (|node::next| var1) var0)) (not (= var0 var4))) (= (read var5 var0) var3)) (not (valid var5 var0)))))))
(check-sat)
