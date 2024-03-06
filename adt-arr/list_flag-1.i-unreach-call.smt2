(set-logic HORN)
(set-info :source |
    Benchmark: C_VC
    Output by Princess (http://www.philipp.ruemmer.org/princess.shtml)
|)
(set-info :status unsat)
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
(declare-fun inv_main532_3 (Heap) Bool)
(declare-fun inv_main535_15 (Heap Int Addr Addr Addr Int) Bool)
(declare-fun inv_main544_17 (Heap Int Addr Addr Addr Int) Bool)
(declare-fun inv_main551_5 (Heap Int Addr Addr Addr) Bool)
(declare-fun inv_main554_5 (Heap Int Addr Addr Addr) Bool)
(declare-fun inv_main556_7_19 (Heap Int Addr Addr Addr) Bool)
(declare-fun inv_main_4 (Heap Int Addr Addr Addr) Bool)
(assert (forall ((var0 Heap)) (or (not (= var0 emptyHeap)) (inv_main532_3 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Int) (var8 Int) (var9 Heap) (var10 Heap) (var11 Int) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Int) (var16 Heap)) (or (not (and (inv_main551_5 var16 var15 var14 var13 var12) (and (and (not (= var11 3)) (and (and (and (and (and (= var10 var9) (= var8 var7)) (= var6 var5)) (= var4 var3)) (= var2 var1)) (= var11 (|node::h| (getnode (read var9 var5)))))) (and (not (= var0 2)) (and (and (and (and (and (= var9 var16) (= var7 var15)) (= var5 var14)) (= var3 var13)) (= var1 var12)) (= var0 (|node::h| (getnode (read var16 var14))))))))) (inv_main556_7_19 var10 var8 var6 var4 var2))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Int) (var8 Int) (var9 Heap) (var10 Heap) (var11 Int) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Int) (var16 Heap)) (or (not (and (inv_main554_5 var16 var15 var14 var13 var12) (and (and (not (= var11 3)) (and (and (and (and (and (= var10 var9) (= var8 var7)) (= var6 var5)) (= var4 var3)) (= var2 var1)) (= var11 (|node::h| (getnode (read var9 var5)))))) (and (not (= var0 1)) (and (and (and (and (and (= var9 var16) (= var7 var15)) (= var5 var14)) (= var3 var13)) (= var1 var12)) (= var0 (|node::h| (getnode (read var16 var14))))))))) (inv_main556_7_19 var10 var8 var6 var4 var2))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap)) (or (not (inv_main535_15 var5 var4 var3 var2 var1 var0)) (inv_main535_15 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Int) (var8 Int) (var9 node) (var10 Heap) (var11 Addr) (var12 Heap)) (or (not (and (inv_main532_3 var12) (and (and (= var11 nullAddr) (and (and (and (and (and (= var10 (newHeap (alloc var12 (O_node var9)))) (= var8 var7)) (= var6 var5)) (= var4 var3)) (= var2 var1)) (= var11 (newAddr (alloc var12 (O_node var9)))))) (= var0 1)))) (inv_main535_15 var10 var8 var6 var11 var2 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Int) (var6 node) (var7 Heap) (var8 Addr) (var9 Int) (var10 Addr) (var11 Addr) (var12 Heap) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Int) (var21 Int) (var22 Heap) (var23 Heap) (var24 Addr) (var25 Addr) (var26 Addr) (var27 Int) (var28 Heap)) (or (not (and (inv_main_4 var28 var27 var26 var25 var24) (and (and (and (and (and (and (and (= var23 var22) (= var21 var20)) (= var19 var18)) (= var17 var16)) (= var15 var14)) (= var13 (|node::n| (getnode (read var22 var18))))) (and (and (and (and (= var22 (write var12 var11 (O_node (node (|node::h| (getnode (read var12 var11))) var10)))) (= var20 var9)) (= var18 var11)) (= var16 var8)) (= var14 var10))) (and (and (and (not (= var10 nullAddr)) (and (and (and (and (and (= var12 (newHeap (alloc var7 (O_node var6)))) (= var9 var5)) (= var11 var4)) (= var8 var3)) (= var2 var1)) (= var10 (newAddr (alloc var7 (O_node var6)))))) (and (not (= var27 0)) (not (= var0 0)))) (and (and (and (and (= var7 (write var28 var26 (O_node (node 1 (|node::n| (getnode (read var28 var26))))))) (= var5 var27)) (= var4 var26)) (= var3 var25)) (= var1 var24)))))) (inv_main_4 var23 var21 var13 var17 var15))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Int) (var6 node) (var7 Heap) (var8 Addr) (var9 Int) (var10 Addr) (var11 Addr) (var12 Heap) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Int) (var21 Int) (var22 Heap) (var23 Heap) (var24 Addr) (var25 Addr) (var26 Addr) (var27 Int) (var28 Heap)) (or (not (and (inv_main_4 var28 var27 var26 var25 var24) (and (and (and (and (and (and (and (= var23 var22) (= var21 var20)) (= var19 var18)) (= var17 var16)) (= var15 var14)) (= var13 (|node::n| (getnode (read var22 var18))))) (and (and (and (and (= var22 (write var12 var11 (O_node (node (|node::h| (getnode (read var12 var11))) var10)))) (= var20 var9)) (= var18 var11)) (= var16 var8)) (= var14 var10))) (and (and (and (not (= var10 nullAddr)) (and (and (and (and (and (= var12 (newHeap (alloc var7 (O_node var6)))) (= var9 var5)) (= var11 var4)) (= var8 var3)) (= var2 var1)) (= var10 (newAddr (alloc var7 (O_node var6)))))) (and (= var27 0) (not (= var0 0)))) (and (and (and (and (= var7 (write var28 var26 (O_node (node 2 (|node::n| (getnode (read var28 var26))))))) (= var5 var27)) (= var4 var26)) (= var3 var25)) (= var1 var24)))))) (inv_main_4 var23 var21 var13 var17 var15))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Int) (var7 Int) (var8 node) (var9 Heap) (var10 Addr) (var11 Heap)) (or (not (and (inv_main532_3 var11) (and (not (= var10 nullAddr)) (and (and (and (and (and (= var9 (newHeap (alloc var11 (O_node var8)))) (= var7 var6)) (= var5 var4)) (= var3 var2)) (= var1 var0)) (= var10 (newAddr (alloc var11 (O_node var8)))))))) (inv_main_4 var9 var7 var10 var10 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap)) (or (not (inv_main544_17 var5 var4 var3 var2 var1 var0)) (inv_main544_17 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Int) (var9 Int) (var10 node) (var11 Heap) (var12 Heap) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Int) (var18 Heap)) (or (not (and (inv_main_4 var18 var17 var16 var15 var14) (and (and (and (and (= var13 nullAddr) (and (and (and (and (and (= var12 (newHeap (alloc var11 (O_node var10)))) (= var9 var8)) (= var7 var6)) (= var5 var4)) (= var3 var2)) (= var13 (newAddr (alloc var11 (O_node var10)))))) (and (not (= var17 0)) (not (= var1 0)))) (and (and (and (and (= var11 (write var18 var16 (O_node (node 1 (|node::n| (getnode (read var18 var16))))))) (= var8 var17)) (= var6 var16)) (= var4 var15)) (= var2 var14))) (= var0 1)))) (inv_main544_17 var12 var9 var7 var5 var13 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Int) (var9 Int) (var10 node) (var11 Heap) (var12 Heap) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Int) (var18 Heap)) (or (not (and (inv_main_4 var18 var17 var16 var15 var14) (and (and (and (and (= var13 nullAddr) (and (and (and (and (and (= var12 (newHeap (alloc var11 (O_node var10)))) (= var9 var8)) (= var7 var6)) (= var5 var4)) (= var3 var2)) (= var13 (newAddr (alloc var11 (O_node var10)))))) (and (= var17 0) (not (= var1 0)))) (and (and (and (and (= var11 (write var18 var16 (O_node (node 2 (|node::n| (getnode (read var18 var16))))))) (= var8 var17)) (= var6 var16)) (= var4 var15)) (= var2 var14))) (= var0 1)))) (inv_main544_17 var12 var9 var7 var5 var13 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Int) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Int) (var10 Heap)) (or (not (and (inv_main_4 var10 var9 var8 var7 var6) (and (= var5 0) (and (= var4 0) (and (and (and (and (= var3 (write var10 var8 (O_node (node 3 (|node::n| (getnode (read var10 var8))))))) (= var5 var9)) (= var2 var8)) (= var1 var7)) (= var0 var6)))))) (inv_main554_5 var3 var5 var1 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Int) (var9 Int) (var10 Heap) (var11 Heap) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Int) (var16 Heap)) (or (not (and (inv_main554_5 var16 var15 var14 var13 var12) (and (and (and (and (and (and (= var11 var10) (= var9 var8)) (= var7 var6)) (= var5 var4)) (= var3 var2)) (= var1 (|node::n| (getnode (read var10 var6))))) (and (= var0 1) (and (and (and (and (and (= var10 var16) (= var8 var15)) (= var6 var14)) (= var4 var13)) (= var2 var12)) (= var0 (|node::h| (getnode (read var16 var14))))))))) (inv_main554_5 var11 var9 var1 var5 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Int) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Int) (var10 Heap)) (or (not (and (inv_main_4 var10 var9 var8 var7 var6) (and (not (= var5 0)) (and (= var4 0) (and (and (and (and (= var3 (write var10 var8 (O_node (node 3 (|node::n| (getnode (read var10 var8))))))) (= var5 var9)) (= var2 var8)) (= var1 var7)) (= var0 var6)))))) (inv_main551_5 var3 var5 var1 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Int) (var9 Int) (var10 Heap) (var11 Heap) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Int) (var16 Heap)) (or (not (and (inv_main551_5 var16 var15 var14 var13 var12) (and (and (and (and (and (and (= var11 var10) (= var9 var8)) (= var7 var6)) (= var5 var4)) (= var3 var2)) (= var1 (|node::n| (getnode (read var10 var6))))) (and (= var0 2) (and (and (and (and (and (= var10 var16) (= var8 var15)) (= var6 var14)) (= var4 var13)) (= var2 var12)) (= var0 (|node::h| (getnode (read var16 var14))))))))) (inv_main551_5 var11 var9 var1 var5 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap)) (not (inv_main556_7_19 var4 var3 var2 var1 var0))))
(check-sat)
