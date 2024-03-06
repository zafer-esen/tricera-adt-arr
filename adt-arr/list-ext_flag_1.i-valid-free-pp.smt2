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
                   ((node (|node::h| Int) (|node::flag| Int) (|node::n| Addr)))))
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
(declare-fun _Glue13_exp_exp (Heap Addr Int Int Addr Addr Int Addr HeapObject) Bool)
(declare-fun inv_main_32 (Heap Addr) Bool)
(declare-fun inv_main_34 (Heap Addr Addr) Bool)
(declare-fun inv_main537_3 (Heap Addr Addr Int) Bool)
(declare-fun _Glue8 (Addr Int Addr Heap Addr HeapObject) Bool)
(declare-fun _Glue4 (Addr Addr Int Heap HeapObject) Bool)
(declare-fun _Glue11_exp_exp (Addr Int Int Addr Int Addr Int Heap Addr HeapObject) Bool)
(declare-fun inv_main_19 (Heap Addr Addr Int) Bool)
(declare-fun _Glue5 (Addr Int Addr Heap Addr HeapObject) Bool)
(declare-fun _Glue18_exp_exp (Addr Int Int Int Addr Addr Int Heap Addr HeapObject) Bool)
(declare-fun _Glue20_exp_exp (Heap Addr Int Int Addr Addr Int Addr HeapObject) Bool)
(declare-fun _Glue23 (Addr Int Addr Addr Heap HeapObject) Bool)
(declare-fun _Glue10 (Heap Addr Int Addr Addr HeapObject) Bool)
(declare-fun _Glue16 (Addr Int Addr Addr Heap HeapObject) Bool)
(declare-fun _Glue7 (Heap Addr Int Addr Addr HeapObject) Bool)
(declare-fun _Glue2 (Addr Int Heap Addr HeapObject) Bool)
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Addr) (var5 Int) (var6 Addr) (var7 Heap) (var8 HeapObject) (var9 Addr)) (or (not (and (and (Inv_Heap var9 var8) (inv_main537_3 var7 var9 var6 (+ var5 (- 1)))) (and (and (= nullAddr var4) (= (read var7 var9) var8)) (valid var7 var9)))) (_Glue11_exp_exp var4 var3 var2 var1 var0 var6 var5 var7 var9 var8))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 HeapObject) (var5 Addr) (var6 Int) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main537_3 var9 var8 var7 (+ var6 (- 1))) (and (and (= nullAddr var5) (= (read var9 var8) var4)) (not (valid var9 var8))))) (_Glue11_exp_exp var5 var3 var2 var1 var0 var7 var6 var9 var8 var4))))
(assert (forall ((var0 node) (var1 HeapObject) (var2 node) (var3 Addr) (var4 Int) (var5 HeapObject) (var6 Addr) (var7 Heap) (var8 Int) (var9 Addr) (var10 Int) (var11 Addr) (var12 Int) (var13 Int) (var14 Addr)) (or (not (and (_Glue11_exp_exp var14 var13 var12 var11 var10 var9 var8 var7 var6 var5) (and (and (and (and (and (= (node var4 var10 var3) var2) (= (O_node var2) var1)) (= (getnode var5) var0)) (= (|node::h| var0) var4)) (= (|node::n| var0) var3)) (valid var7 var6)))) (Inv_Heap var6 var1))))
(assert (forall ((var0 node) (var1 Heap) (var2 HeapObject) (var3 node) (var4 Addr) (var5 Int) (var6 HeapObject) (var7 Heap) (var8 Int) (var9 Addr) (var10 Int) (var11 Addr) (var12 Int) (var13 Int) (var14 Addr) (var15 HeapObject) (var16 Addr)) (or (not (and (and (Inv_Heap var16 var15) (_Glue11_exp_exp var14 var13 var12 var11 var10 var9 var8 var7 var16 var6)) (and (and (and (and (and (and (and (= (node var5 var10 var4) var3) (= (O_node var3) var2)) (= (read var1 var16) var15)) (= (getnode var6) var0)) (= (|node::h| var0) var5)) (= (|node::n| var0) var4)) (= (write var7 var16 var2) var1)) (valid var1 var16)))) (_Glue13_exp_exp var1 var14 var13 var12 var11 var9 var8 var16 var15))))
(assert (forall ((var0 node) (var1 HeapObject) (var2 Heap) (var3 HeapObject) (var4 node) (var5 Addr) (var6 Int) (var7 HeapObject) (var8 Addr) (var9 Heap) (var10 Int) (var11 Addr) (var12 Int) (var13 Addr) (var14 Int) (var15 Int) (var16 Addr)) (or (not (and (_Glue11_exp_exp var16 var15 var14 var13 var12 var11 var10 var9 var8 var7) (and (and (and (and (and (and (and (= (node var6 var12 var5) var4) (= (O_node var4) var3)) (= (read var2 var8) var1)) (= (getnode var7) var0)) (= (|node::h| var0) var6)) (= (|node::n| var0) var5)) (= (write var9 var8 var3) var2)) (not (valid var2 var8))))) (_Glue13_exp_exp var2 var16 var15 var14 var13 var11 var10 var8 var1))))
(assert (forall ((var0 node) (var1 HeapObject) (var2 node) (var3 Addr) (var4 Int) (var5 HeapObject) (var6 Addr) (var7 Int) (var8 Addr) (var9 Addr) (var10 Int) (var11 Int) (var12 Addr) (var13 Heap)) (or (not (and (_Glue13_exp_exp var13 var12 var11 var10 var9 var8 var7 var6 var5) (and (and (and (and (and (and (= (node 1 var4 var3) var2) (= (O_node var2) var1)) (= (getnode var5) var0)) (= (|node::flag| var0) var4)) (not (= var4 0))) (= (|node::n| var0) var3)) (valid var13 var6)))) (Inv_Heap var6 var1))))
(assert (forall ((var0 node) (var1 AllocResHeap) (var2 Heap) (var3 HeapObject) (var4 node) (var5 Addr) (var6 Int) (var7 HeapObject) (var8 node) (var9 HeapObject) (var10 Addr) (var11 Int) (var12 Addr) (var13 Addr) (var14 Int) (var15 Int) (var16 Addr) (var17 Heap)) (or (not (and (_Glue13_exp_exp var17 var16 var15 var14 var13 var12 var11 var10 var9) (and (and (and (and (and (and (and (and (and (= (O_node var8) var7) (= (node 1 var6 var5) var4)) (= (O_node var4) var3)) (= (node var15 var14 var13) var8)) (= (alloc var2 var7) var1)) (= (getnode var9) var0)) (= (|node::flag| var0) var6)) (= (|node::n| var0) var5)) (= (write var17 var10 var3) var2)) (not (= var6 0))))) (Inv_Heap (newAddr var1) var7))))
(assert (forall ((var0 node) (var1 Heap) (var2 HeapObject) (var3 node) (var4 Addr) (var5 Int) (var6 HeapObject) (var7 node) (var8 AllocResHeap) (var9 Addr) (var10 Heap) (var11 HeapObject) (var12 Int) (var13 Addr) (var14 Addr) (var15 Int) (var16 Int) (var17 Addr) (var18 Heap) (var19 HeapObject) (var20 Addr)) (or (not (and (and (Inv_Heap var20 var19) (_Glue13_exp_exp var18 var17 var16 var15 var14 var13 var12 var20 var11)) (and (and (and (and (and (and (and (and (and (and (and (and (and (= (AllocResHeap var10 var9) var8) (= (O_node var7) var6)) (= (node 1 var5 var4) var3)) (= (O_node var3) var2)) (= (node var16 var15 var14) var7)) (not (= var9 var17))) (= (read var10 var20) var19)) (valid var10 var20)) (= (alloc var1 var6) var8)) (= (getnode var11) var0)) (= (|node::flag| var0) var5)) (= (|node::n| var0) var4)) (= (write var18 var20 var2) var1)) (not (= var5 0))))) (_Glue16 var20 var12 var13 var9 var10 var19))))
(assert (forall ((var0 node) (var1 Heap) (var2 HeapObject) (var3 HeapObject) (var4 node) (var5 Addr) (var6 Int) (var7 HeapObject) (var8 node) (var9 AllocResHeap) (var10 Addr) (var11 Heap) (var12 HeapObject) (var13 Addr) (var14 Int) (var15 Addr) (var16 Addr) (var17 Int) (var18 Int) (var19 Addr) (var20 Heap)) (or (not (and (_Glue13_exp_exp var20 var19 var18 var17 var16 var15 var14 var13 var12) (and (and (and (and (and (and (and (and (and (and (and (and (and (= (AllocResHeap var11 var10) var9) (= (O_node var8) var7)) (= (node 1 var6 var5) var4)) (= (O_node var4) var3)) (= (node var18 var17 var16) var8)) (not (= var10 var19))) (= (read var11 var13) var2)) (not (valid var11 var13))) (= (alloc var1 var7) var9)) (= (getnode var12) var0)) (= (|node::flag| var0) var6)) (= (|node::n| var0) var5)) (= (write var20 var13 var3) var1)) (not (= var6 0))))) (_Glue16 var13 var14 var15 var10 var11 var2))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Int) (var3 Int) (var4 node) (var5 HeapObject) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Int) (var10 Addr)) (or (not (and (_Glue16 var10 var9 var8 var7 var6 var5) (and (and (and (and (and (= (getnode var5) var4) (= (|node::h| var4) var3)) (= (|node::flag| var4) var2)) (= (node var3 var2 var7) var1)) (= (O_node var1) var0)) (valid var6 var10)))) (Inv_Heap var10 var0))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Int) (var3 Int) (var4 node) (var5 Addr) (var6 node) (var7 Heap) (var8 HeapObject) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Int) (var13 HeapObject) (var14 Addr)) (or (not (and (and (Inv_Heap var14 var13) (_Glue16 var14 var12 var11 var10 var9 var8)) (and (and (and (and (and (and (and (and (and (and (and (= (read var7 var14) var13) (= (getnode var13) var6)) (= (|node::n| var6) var5)) (<= 0 (+ (+ 20 (* (- 1) (+ var12 (- 1)))) (- 1)))) (valid var7 var14)) true) (= (getnode var8) var4)) (= (|node::h| var4) var3)) (= (|node::flag| var4) var2)) (= (node var3 var2 var10) var1)) (= (O_node var1) var0)) (= (write var9 var14 var0) var7)))) (inv_main537_3 var7 var5 var11 var12))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Int) (var3 Int) (var4 node) (var5 Addr) (var6 node) (var7 HeapObject) (var8 Heap) (var9 HeapObject) (var10 Heap) (var11 Addr) (var12 Addr) (var13 Int) (var14 Addr)) (or (not (and (_Glue16 var14 var13 var12 var11 var10 var9) (and (and (and (and (and (and (and (and (and (and (= (read var8 var14) var7) (= (getnode var7) var6)) (= (|node::n| var6) var5)) (<= 0 (+ (+ 20 (* (- 1) (+ var13 (- 1)))) (- 1)))) (not (valid var8 var14))) (= (getnode var9) var4)) (= (|node::h| var4) var3)) (= (|node::flag| var4) var2)) (= (node var3 var2 var11) var1)) (= (O_node var1) var0)) (= (write var10 var14 var0) var8)))) (inv_main537_3 var8 var5 var12 var13))))
(assert (forall ((var0 Addr) (var1 Int) (var2 node) (var3 Int) (var4 Addr) (var5 Heap) (var6 HeapObject) (var7 Addr)) (or (not (and (and (Inv_Heap var7 var6) (inv_main_19 var5 var7 var4 (+ var3 (- 1)))) (and (and (and (and (and (and (= (read var5 var7) var6) (= (getnode var6) var2)) (= (|node::h| var2) 1)) (= (|node::flag| var2) var1)) (= (|node::n| var2) var0)) (not (= var1 0))) (valid var5 var7)))) (inv_main_19 var5 var0 var4 var3))))
(assert (forall ((var0 Addr) (var1 Int) (var2 node) (var3 HeapObject) (var4 Int) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main_19 var7 var6 var5 (+ var4 (- 1))) (and (and (and (and (and (and (= (read var7 var6) var3) (= (getnode var3) var2)) (= (|node::h| var2) 1)) (= (|node::flag| var2) var1)) (= (|node::n| var2) var0)) (not (= var1 0))) (not (valid var7 var6))))) (inv_main_19 var7 var0 var5 var4))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main_34 var3 var2 var1) (and (= defObj var0) (valid var3 var2)))) (Inv_Heap var2 var0))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 node) (var3 Heap) (var4 Addr) (var5 Heap) (var6 HeapObject) (var7 Addr)) (or (not (and (and (Inv_Heap var7 var6) (inv_main_34 var5 var4 var7)) (and (and (and (and (and (and (= (read var3 var7) var6) (= (getnode var6) var2)) (= (|node::n| var2) var1)) (valid var3 var7)) (= nullAddr var1)) (= defObj var0)) (= (write var5 var4 var0) var3)))) (inv_main_32 var3 var7))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 node) (var3 HeapObject) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main_34 var7 var6 var5) (and (and (and (and (and (and (= (read var4 var5) var3) (= (getnode var3) var2)) (= (|node::n| var2) var1)) (not (valid var4 var5))) (= nullAddr var1)) (= defObj var0)) (= (write var7 var6 var0) var4)))) (inv_main_32 var4 var5))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Int) (var4 Addr) (var5 Int) (var6 Addr) (var7 Heap) (var8 HeapObject) (var9 Addr)) (or (not (and (and (Inv_Heap var9 var8) (inv_main537_3 var7 var9 var6 (+ var5 (- 1)))) (and (and (= nullAddr var4) (= (read var7 var9) var8)) (valid var7 var9)))) (_Glue18_exp_exp var4 var3 var2 var1 var0 var6 var5 var7 var9 var8))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Int) (var4 HeapObject) (var5 Addr) (var6 Int) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main537_3 var9 var8 var7 (+ var6 (- 1))) (and (and (= nullAddr var5) (= (read var9 var8) var4)) (not (valid var9 var8))))) (_Glue18_exp_exp var5 var3 var2 var1 var0 var7 var6 var9 var8 var4))))
(assert (forall ((var0 node) (var1 HeapObject) (var2 node) (var3 Addr) (var4 Int) (var5 HeapObject) (var6 Addr) (var7 Heap) (var8 Int) (var9 Addr) (var10 Addr) (var11 Int) (var12 Int) (var13 Int) (var14 Addr)) (or (not (and (_Glue18_exp_exp var14 var13 var12 var11 var10 var9 var8 var7 var6 var5) (and (and (and (and (and (= (node var4 var13 var3) var2) (= (O_node var2) var1)) (= (getnode var5) var0)) (= (|node::h| var0) var4)) (= (|node::n| var0) var3)) (valid var7 var6)))) (Inv_Heap var6 var1))))
(assert (forall ((var0 node) (var1 Heap) (var2 HeapObject) (var3 node) (var4 Addr) (var5 Int) (var6 HeapObject) (var7 Heap) (var8 Int) (var9 Addr) (var10 Addr) (var11 Int) (var12 Int) (var13 Int) (var14 Addr) (var15 HeapObject) (var16 Addr)) (or (not (and (and (Inv_Heap var16 var15) (_Glue18_exp_exp var14 var13 var12 var11 var10 var9 var8 var7 var16 var6)) (and (and (and (and (and (and (and (= (node var5 var13 var4) var3) (= (O_node var3) var2)) (= (read var1 var16) var15)) (= (getnode var6) var0)) (= (|node::h| var0) var5)) (= (|node::n| var0) var4)) (= (write var7 var16 var2) var1)) (valid var1 var16)))) (_Glue20_exp_exp var1 var14 var12 var11 var10 var9 var8 var16 var15))))
(assert (forall ((var0 node) (var1 HeapObject) (var2 Heap) (var3 HeapObject) (var4 node) (var5 Addr) (var6 Int) (var7 HeapObject) (var8 Addr) (var9 Heap) (var10 Int) (var11 Addr) (var12 Addr) (var13 Int) (var14 Int) (var15 Int) (var16 Addr)) (or (not (and (_Glue18_exp_exp var16 var15 var14 var13 var12 var11 var10 var9 var8 var7) (and (and (and (and (and (and (and (= (node var6 var15 var5) var4) (= (O_node var4) var3)) (= (read var2 var8) var1)) (= (getnode var7) var0)) (= (|node::h| var0) var6)) (= (|node::n| var0) var5)) (= (write var9 var8 var3) var2)) (not (valid var2 var8))))) (_Glue20_exp_exp var2 var16 var14 var13 var12 var11 var10 var8 var1))))
(assert (forall ((var0 node) (var1 HeapObject) (var2 node) (var3 Addr) (var4 HeapObject) (var5 Addr) (var6 Int) (var7 Addr) (var8 Addr) (var9 Int) (var10 Int) (var11 Addr) (var12 Heap)) (or (not (and (_Glue20_exp_exp var12 var11 var10 var9 var8 var7 var6 var5 var4) (and (and (and (and (and (= (node 2 0 var3) var2) (= (O_node var2) var1)) (= (getnode var4) var0)) (= (|node::flag| var0) 0)) (= (|node::n| var0) var3)) (valid var12 var5)))) (Inv_Heap var5 var1))))
(assert (forall ((var0 node) (var1 AllocResHeap) (var2 Heap) (var3 HeapObject) (var4 node) (var5 Addr) (var6 HeapObject) (var7 node) (var8 HeapObject) (var9 Addr) (var10 Int) (var11 Addr) (var12 Addr) (var13 Int) (var14 Int) (var15 Addr) (var16 Heap)) (or (not (and (_Glue20_exp_exp var16 var15 var14 var13 var12 var11 var10 var9 var8) (and (and (and (and (and (and (and (and (= (O_node var7) var6) (= (node 2 0 var5) var4)) (= (O_node var4) var3)) (= (node var14 var13 var12) var7)) (= (alloc var2 var6) var1)) (= (getnode var8) var0)) (= (|node::flag| var0) 0)) (= (|node::n| var0) var5)) (= (write var16 var9 var3) var2)))) (Inv_Heap (newAddr var1) var6))))
(assert (forall ((var0 node) (var1 Heap) (var2 HeapObject) (var3 node) (var4 Addr) (var5 HeapObject) (var6 node) (var7 AllocResHeap) (var8 Addr) (var9 Heap) (var10 HeapObject) (var11 Int) (var12 Addr) (var13 Addr) (var14 Int) (var15 Int) (var16 Addr) (var17 Heap) (var18 HeapObject) (var19 Addr)) (or (not (and (and (Inv_Heap var19 var18) (_Glue20_exp_exp var17 var16 var15 var14 var13 var12 var11 var19 var10)) (and (and (and (and (and (and (and (and (and (and (and (and (= (AllocResHeap var9 var8) var7) (= (O_node var6) var5)) (= (node 2 0 var4) var3)) (= (O_node var3) var2)) (= (node var15 var14 var13) var6)) (not (= var8 var16))) (= (read var9 var19) var18)) (valid var9 var19)) (= (alloc var1 var5) var7)) (= (getnode var10) var0)) (= (|node::flag| var0) 0)) (= (|node::n| var0) var4)) (= (write var17 var19 var2) var1)))) (_Glue23 var19 var11 var12 var8 var9 var18))))
(assert (forall ((var0 node) (var1 Heap) (var2 HeapObject) (var3 HeapObject) (var4 node) (var5 Addr) (var6 HeapObject) (var7 node) (var8 AllocResHeap) (var9 Addr) (var10 Heap) (var11 HeapObject) (var12 Addr) (var13 Int) (var14 Addr) (var15 Addr) (var16 Int) (var17 Int) (var18 Addr) (var19 Heap)) (or (not (and (_Glue20_exp_exp var19 var18 var17 var16 var15 var14 var13 var12 var11) (and (and (and (and (and (and (and (and (and (and (and (and (= (AllocResHeap var10 var9) var8) (= (O_node var7) var6)) (= (node 2 0 var5) var4)) (= (O_node var4) var3)) (= (node var17 var16 var15) var7)) (not (= var9 var18))) (= (read var10 var12) var2)) (not (valid var10 var12))) (= (alloc var1 var6) var8)) (= (getnode var11) var0)) (= (|node::flag| var0) 0)) (= (|node::n| var0) var5)) (= (write var19 var12 var3) var1)))) (_Glue23 var12 var13 var14 var9 var10 var2))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Int) (var3 Int) (var4 node) (var5 HeapObject) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Int) (var10 Addr)) (or (not (and (_Glue23 var10 var9 var8 var7 var6 var5) (and (and (and (and (and (= (getnode var5) var4) (= (|node::h| var4) var3)) (= (|node::flag| var4) var2)) (= (node var3 var2 var7) var1)) (= (O_node var1) var0)) (valid var6 var10)))) (Inv_Heap var10 var0))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Int) (var3 Int) (var4 node) (var5 Addr) (var6 node) (var7 Heap) (var8 HeapObject) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Int) (var13 HeapObject) (var14 Addr)) (or (not (and (and (Inv_Heap var14 var13) (_Glue23 var14 var12 var11 var10 var9 var8)) (and (and (and (and (and (and (and (and (and (and (and (= (read var7 var14) var13) (= (getnode var13) var6)) (= (|node::n| var6) var5)) (<= 0 (+ (+ 20 (* (- 1) (+ var12 (- 1)))) (- 1)))) (valid var7 var14)) true) (= (getnode var8) var4)) (= (|node::h| var4) var3)) (= (|node::flag| var4) var2)) (= (node var3 var2 var10) var1)) (= (O_node var1) var0)) (= (write var9 var14 var0) var7)))) (inv_main537_3 var7 var5 var11 var12))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Int) (var3 Int) (var4 node) (var5 Addr) (var6 node) (var7 HeapObject) (var8 Heap) (var9 HeapObject) (var10 Heap) (var11 Addr) (var12 Addr) (var13 Int) (var14 Addr)) (or (not (and (_Glue23 var14 var13 var12 var11 var10 var9) (and (and (and (and (and (and (and (and (and (and (= (read var8 var14) var7) (= (getnode var7) var6)) (= (|node::n| var6) var5)) (<= 0 (+ (+ 20 (* (- 1) (+ var13 (- 1)))) (- 1)))) (not (valid var8 var14))) (= (getnode var9) var4)) (= (|node::h| var4) var3)) (= (|node::flag| var4) var2)) (= (node var3 var2 var11) var1)) (= (O_node var1) var0)) (= (write var10 var14 var0) var8)))) (inv_main537_3 var8 var5 var12 var13))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Heap) (var4 HeapObject) (var5 Addr)) (or (not (and (and (Inv_Heap var5 var4) (inv_main537_3 var3 var5 var2 var1)) (and (= (read var3 var5) var4) (valid var3 var5)))) (_Glue8 var0 var1 var2 var3 var5 var4))))
(assert (forall ((var0 Addr) (var1 HeapObject) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main537_3 var5 var4 var3 var2) (and (= (read var5 var4) var1) (not (valid var5 var4))))) (_Glue8 var0 var2 var3 var5 var4 var1))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Int) (var4 node) (var5 HeapObject) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Int) (var10 Addr)) (or (not (and (_Glue8 var10 var9 var8 var7 var6 var5) (and (and (and (and (and (= (getnode var5) var4) (= (|node::flag| var4) var3)) (= (|node::n| var4) var2)) (= (node 3 var3 var2) var1)) (= (O_node var1) var0)) (valid var7 var6)))) (Inv_Heap var6 var0))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Int) (var4 node) (var5 Heap) (var6 HeapObject) (var7 Heap) (var8 Addr) (var9 Int) (var10 Addr) (var11 HeapObject) (var12 Addr)) (or (not (and (and (Inv_Heap var12 var11) (_Glue8 var10 var9 var8 var7 var12 var6)) (and (and (and (and (and (and (and (= (read var5 var12) var11) (valid var5 var12)) (= (getnode var6) var4)) (= (|node::flag| var4) var3)) (= (|node::n| var4) var2)) (= (node 3 var3 var2) var1)) (= (O_node var1) var0)) (= (write var7 var12 var0) var5)))) (_Glue10 var5 var10 var9 var8 var12 var11))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Int) (var4 node) (var5 HeapObject) (var6 Heap) (var7 HeapObject) (var8 Addr) (var9 Heap) (var10 Addr) (var11 Int) (var12 Addr)) (or (not (and (_Glue8 var12 var11 var10 var9 var8 var7) (and (and (and (and (and (and (and (= (read var6 var8) var5) (not (valid var6 var8))) (= (getnode var7) var4)) (= (|node::flag| var4) var3)) (= (|node::n| var4) var2)) (= (node 3 var3 var2) var1)) (= (O_node var1) var0)) (= (write var9 var8 var0) var6)))) (_Glue10 var6 var12 var11 var10 var8 var5))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Int) (var3 Int) (var4 node) (var5 HeapObject) (var6 Addr) (var7 Int) (var8 Addr) (var9 Heap)) (or (not (and (_Glue10 var9 var8 var7 var8 var6 var5) (and (and (and (and (and (and (= (getnode var5) var4) (= (|node::h| var4) var3)) (= (|node::flag| var4) var2)) (= (node var3 var2 0) var1)) (= (O_node var1) var0)) (<= 0 (+ (+ 20 (* (- 1) var7)) (- 1)))) (valid var9 var6)))) (Inv_Heap var6 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 HeapObject) (var4 node) (var5 Int) (var6 Int) (var7 node) (var8 HeapObject) (var9 Addr) (var10 Int) (var11 Addr) (var12 Heap)) (or (not (and (_Glue10 var12 var11 var10 var11 var9 var8) (and (and (and (and (and (and (and (and (= (getnode var8) var7) (= (|node::h| var7) var6)) (= (|node::flag| var7) var5)) (= (node var6 var5 0) var4)) (= (O_node var4) var3)) (= (write var12 var9 var3) var2)) (<= 0 (+ (+ 20 (* (- 1) var10)) (- 1)))) (= var1 var11)) (= var0 0)))) (inv_main_19 var2 var1 var11 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Heap) (var4 HeapObject) (var5 Addr)) (or (not (and (and (Inv_Heap var5 var4) (inv_main_19 var3 var5 var2 var1)) (and (and (= nullAddr var0) (= (read var3 var5) var4)) (valid var3 var5)))) (_Glue2 var0 var1 var3 var2 var4))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main_19 var5 var4 var3 var2) (and (and (= nullAddr var1) (= (read var5 var4) var0)) (not (valid var5 var4))))) (_Glue2 var1 var2 var5 var3 var0))))
(assert (forall ((var0 Addr) (var1 node) (var2 node) (var3 HeapObject) (var4 Heap) (var5 Int) (var6 Addr) (var7 HeapObject) (var8 Addr)) (or (not (and (and (Inv_Heap var8 var7) (_Glue2 var6 var5 var4 var8 var3)) (and (and (and (and (and (and (and (= (getnode var3) var2) (= (|node::h| var2) 3)) (= (read var4 var8) var7)) (= (getnode var7) var1)) (= (|node::n| var1) var0)) (not (= var0 var6))) (not (<= 0 (+ (+ (- 20) var5) (- 1))))) (valid var4 var8)))) (inv_main_34 var4 var8 var0))))
(assert (forall ((var0 Addr) (var1 node) (var2 HeapObject) (var3 node) (var4 HeapObject) (var5 Addr) (var6 Heap) (var7 Int) (var8 Addr)) (or (not (and (_Glue2 var8 var7 var6 var5 var4) (and (and (and (and (and (and (and (= (getnode var4) var3) (= (|node::h| var3) 3)) (= (read var6 var5) var2)) (= (getnode var2) var1)) (= (|node::n| var1) var0)) (not (= var0 var8))) (not (<= 0 (+ (+ (- 20) var7) (- 1))))) (not (valid var6 var5))))) (inv_main_34 var6 var5 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Heap) (var4 HeapObject) (var5 Addr)) (or (not (and (and (Inv_Heap var5 var4) (inv_main_19 var3 var5 var2 var1)) (and (and (= nullAddr var0) (= (read var3 var5) var4)) (valid var3 var5)))) (_Glue4 var2 var0 var1 var3 var4))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main_19 var5 var4 var3 var2) (and (and (= nullAddr var1) (= (read var5 var4) var0)) (not (valid var5 var4))))) (_Glue4 var3 var1 var2 var5 var0))))
(assert (forall ((var0 node) (var1 node) (var2 HeapObject) (var3 Heap) (var4 Int) (var5 Addr) (var6 HeapObject) (var7 Addr)) (or (not (and (and (Inv_Heap var7 var6) (_Glue4 var7 var5 var4 var3 var2)) (and (and (and (and (and (and (= (getnode var2) var1) (= (|node::h| var1) 3)) (= (read var3 var7) var6)) (= (getnode var6) var0)) (= (|node::n| var0) var5)) (not (<= 0 (+ (+ (- 20) var4) (- 1))))) (valid var3 var7)))) (inv_main_32 var3 var7))))
(assert (forall ((var0 node) (var1 HeapObject) (var2 node) (var3 HeapObject) (var4 Heap) (var5 Int) (var6 Addr) (var7 Addr)) (or (not (and (_Glue4 var7 var6 var5 var4 var3) (and (and (and (and (and (and (= (getnode var3) var2) (= (|node::h| var2) 3)) (= (read var4 var7) var1)) (= (getnode var1) var0)) (= (|node::n| var0) var6)) (not (<= 0 (+ (+ (- 20) var5) (- 1))))) (not (valid var4 var7))))) (inv_main_32 var4 var7))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 HeapObject) (var4 Addr)) (not (and (and (Inv_Heap var4 var3) (inv_main_34 var2 var4 var1)) (and (and (and (and (not (= var4 var0)) (= (read var2 var4) var3)) (= defObj var3)) (= nullAddr var0)) (valid var2 var4))))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main_34 var4 var3 var2) (and (and (and (and (not (= var3 var1)) (= (read var4 var3) var0)) (= defObj var0)) (= nullAddr var1)) (not (valid var4 var3)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 HeapObject) (var3 Addr)) (not (and (and (Inv_Heap var3 var2) (inv_main_32 var1 var3)) (and (and (and (and (not (= var3 var0)) (= (read var1 var3) var2)) (= defObj var2)) (= nullAddr var0)) (valid var1 var3))))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_32 var3 var2) (and (and (and (and (not (= var2 var1)) (= (read var3 var2) var0)) (= defObj var0)) (= nullAddr var1)) (not (valid var3 var2)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 AllocResHeap) (var3 Heap) (var4 HeapObject) (var5 node)) (or (not (and (and (and (and (and (= (O_node var5) var4) (= (alloc var3 var4) var2)) (= (newAddr var2) var1)) (not (= var1 var0))) (= nullAddr var0)) (= emptyHeap var3))) (Inv_Heap (newAddr var2) var4))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 AllocResHeap) (var6 Heap) (var7 HeapObject) (var8 node)) (or (not (and (and (and (and (and (and (and (and (= (O_node var8) var7) (= (alloc var6 var7) var5)) (= (newHeap var5) var4)) (= (newAddr var5) var3)) (not (= var3 var2))) (= nullAddr var2)) (= emptyHeap var6)) (= var1 var3)) (= var0 0))) (inv_main537_3 var4 var1 var3 var0))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main_34 var3 var2 var1) (and (= defObj var0) (valid var3 var2)))) (Inv_Heap var2 var0))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 node) (var4 Heap) (var5 Addr) (var6 Heap) (var7 HeapObject) (var8 Addr)) (or (not (and (and (Inv_Heap var8 var7) (inv_main_34 var6 var5 var8)) (and (and (and (and (and (and (and (and (= (read var4 var8) var7) (= (getnode var7) var3)) (= (|node::n| var3) var2)) (not (= var2 var1))) (valid var4 var8)) true) (= nullAddr var1)) (= defObj var0)) (= (write var6 var5 var0) var4)))) (inv_main_34 var4 var8 var2))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 node) (var4 HeapObject) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main_34 var8 var7 var6) (and (and (and (and (and (and (and (= (read var5 var6) var4) (= (getnode var4) var3)) (= (|node::n| var3) var2)) (not (= var2 var1))) (not (valid var5 var6))) (= nullAddr var1)) (= defObj var0)) (= (write var8 var7 var0) var5)))) (inv_main_34 var5 var6 var2))))
(assert (forall ((var0 Addr) (var1 node) (var2 Int) (var3 Addr) (var4 Heap) (var5 HeapObject) (var6 Addr)) (or (not (and (and (Inv_Heap var6 var5) (inv_main_19 var4 var6 var3 (+ var2 (- 1)))) (and (and (and (and (and (= (|node::flag| var1) 0) (= (read var4 var6) var5)) (= (getnode var5) var1)) (= (|node::h| var1) 2)) (= (|node::n| var1) var0)) (valid var4 var6)))) (inv_main_19 var4 var0 var3 var2))))
(assert (forall ((var0 Addr) (var1 HeapObject) (var2 node) (var3 Int) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main_19 var6 var5 var4 (+ var3 (- 1))) (and (and (and (and (and (= (|node::flag| var2) 0) (= (read var6 var5) var1)) (= (getnode var1) var2)) (= (|node::h| var2) 2)) (= (|node::n| var2) var0)) (not (valid var6 var5))))) (inv_main_19 var6 var0 var4 var3))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Heap) (var4 HeapObject) (var5 Addr)) (or (not (and (and (Inv_Heap var5 var4) (inv_main537_3 var3 var5 var2 var1)) (and (= (read var3 var5) var4) (valid var3 var5)))) (_Glue5 var0 var1 var2 var3 var5 var4))))
(assert (forall ((var0 Addr) (var1 HeapObject) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main537_3 var5 var4 var3 var2) (and (= (read var5 var4) var1) (not (valid var5 var4))))) (_Glue5 var0 var2 var3 var5 var4 var1))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Int) (var4 node) (var5 HeapObject) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Int) (var10 Addr)) (or (not (and (_Glue5 var10 var9 var8 var7 var6 var5) (and (and (and (and (and (= (getnode var5) var4) (= (|node::flag| var4) var3)) (= (|node::n| var4) var2)) (= (node 3 var3 var2) var1)) (= (O_node var1) var0)) (valid var7 var6)))) (Inv_Heap var6 var0))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Int) (var4 node) (var5 Heap) (var6 HeapObject) (var7 Heap) (var8 Addr) (var9 Int) (var10 Addr) (var11 HeapObject) (var12 Addr)) (or (not (and (and (Inv_Heap var12 var11) (_Glue5 var10 var9 var8 var7 var12 var6)) (and (and (and (and (and (and (and (= (read var5 var12) var11) (valid var5 var12)) (= (getnode var6) var4)) (= (|node::flag| var4) var3)) (= (|node::n| var4) var2)) (= (node 3 var3 var2) var1)) (= (O_node var1) var0)) (= (write var7 var12 var0) var5)))) (_Glue7 var5 var10 var9 var8 var12 var11))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 Int) (var4 node) (var5 HeapObject) (var6 Heap) (var7 HeapObject) (var8 Addr) (var9 Heap) (var10 Addr) (var11 Int) (var12 Addr)) (or (not (and (_Glue5 var12 var11 var10 var9 var8 var7) (and (and (and (and (and (and (and (= (read var6 var8) var5) (not (valid var6 var8))) (= (getnode var7) var4)) (= (|node::flag| var4) var3)) (= (|node::n| var4) var2)) (= (node 3 var3 var2) var1)) (= (O_node var1) var0)) (= (write var9 var8 var0) var6)))) (_Glue7 var6 var12 var11 var10 var8 var5))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Int) (var3 Int) (var4 node) (var5 HeapObject) (var6 Addr) (var7 Int) (var8 Addr) (var9 Heap)) (or (not (and (_Glue7 var9 var8 var7 var8 var6 var5) (and (and (and (and (and (and (= (getnode var5) var4) (= (|node::h| var4) var3)) (= (|node::flag| var4) var2)) (= (node var3 var2 0) var1)) (= (O_node var1) var0)) (not (<= 0 (+ (+ 20 (* (- 1) var7)) (- 1))))) (valid var9 var6)))) (Inv_Heap var6 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 HeapObject) (var4 node) (var5 Int) (var6 Int) (var7 node) (var8 HeapObject) (var9 Addr) (var10 Int) (var11 Addr) (var12 Heap)) (or (not (and (_Glue7 var12 var11 var10 var11 var9 var8) (and (and (and (and (and (and (and (and (= (getnode var8) var7) (= (|node::h| var7) var6)) (= (|node::flag| var7) var5)) (= (node var6 var5 0) var4)) (= (O_node var4) var3)) (= (write var12 var9 var3) var2)) (not (<= 0 (+ (+ 20 (* (- 1) var10)) (- 1))))) (= var1 var11)) (= var0 0)))) (inv_main_19 var2 var1 var11 var0))))
(check-sat)
