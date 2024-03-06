(set-logic HORN)
(set-info :source |
    Benchmark: C_VC
    Output by Princess (http://www.philipp.ruemmer.org/princess.shtml)
|)
(set-info :status sat)
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
(declare-fun inv_main533_15 (Heap Addr Int) Bool)
(declare-fun inv_main535_3 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main539_17 (Heap Addr Addr Addr Int) Bool)
(declare-fun inv_main546_17 (Heap Addr Addr Addr Int) Bool)
(declare-fun inv_main556_6_28 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main_22 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main_23 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main_3 (Heap Addr Addr Addr) Bool)
(assert (forall ((var0 Heap)) (or (not (= var0 emptyHeap)) (inv_main532_3 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Heap) (var9 Int) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Heap)) (or (not (and (inv_main_23 var13 var12 var11 var10) (and (and (not (= var9 3)) (and (and (and (and (= var8 var7) (= var6 var5)) (= var4 var3)) (= var2 var1)) (= var9 (|node::h| (getnode (read var7 var1)))))) (and (not (= var0 2)) (and (and (and (and (= var7 var13) (= var5 var12)) (= var3 var11)) (= var1 var10)) (= var0 (|node::h| (getnode (read var13 var10))))))))) (inv_main556_6_28 var8 var6 var4 var2))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap)) (or (not (inv_main533_15 var2 var1 var0)) (inv_main533_15 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 node) (var2 Heap) (var3 Addr) (var4 Heap)) (or (not (and (inv_main532_3 var4) (and (and (= var3 nullAddr) (and (= var2 (newHeap (alloc var4 (O_node var1)))) (= var3 (newAddr (alloc var4 (O_node var1)))))) (= var0 1)))) (inv_main533_15 var2 var3 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main535_3 var4 var3 var2 var1) (= var0 0))) (inv_main_3 var4 var3 var2 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 node) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Heap) (var19 Heap) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Heap)) (or (not (and (inv_main_3 var23 var22 var21 var20) (and (and (and (and (and (and (= var19 var18) (= var17 var16)) (= var15 var14)) (= var13 var12)) (= var11 (|node::n| (getnode (read var18 var12))))) (and (and (and (= var18 (write var10 var9 (O_node (node (|node::h| (getnode (read var10 var9))) var8)))) (= var16 var7)) (= var14 var8)) (= var12 var9))) (and (not (= var8 nullAddr)) (and (and (and (and (and (and (= var10 (newHeap (alloc var6 (O_node var5)))) (= var7 var4)) (= var3 var2)) (= var9 var1)) (= var8 (newAddr (alloc var6 (O_node var5))))) (not (= var0 0))) (and (and (and (= var6 (write var23 var20 (O_node (node 2 (|node::n| (getnode (read var23 var20))))))) (= var4 var22)) (= var2 var21)) (= var1 var20))))))) (inv_main_3 var19 var17 var15 var11))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main_22 var8 var7 var6 var5) (and (not (= var4 1)) (and (and (and (and (= var3 var8) (= var2 var7)) (= var1 var6)) (= var0 var5)) (= var4 (|node::h| (getnode (read var8 var5)))))))) (inv_main_23 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Heap)) (or (not (and (inv_main_23 var13 var12 var11 var10) (and (and (and (and (and (= var9 var8) (= var7 var6)) (= var5 var4)) (= var3 var2)) (= var1 (|node::n| (getnode (read var8 var2))))) (and (= var0 2) (and (and (and (and (= var8 var13) (= var6 var12)) (= var4 var11)) (= var2 var10)) (= var0 (|node::h| (getnode (read var13 var10))))))))) (inv_main_23 var9 var7 var5 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (inv_main546_17 var4 var3 var2 var1 var0)) (inv_main546_17 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 node) (var9 Heap) (var10 Heap) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Heap)) (or (not (and (inv_main_3 var15 var14 var13 var12) (and (and (= var11 nullAddr) (and (and (and (and (and (and (= var10 (newHeap (alloc var9 (O_node var8)))) (= var7 var6)) (= var5 var4)) (= var3 var2)) (= var11 (newAddr (alloc var9 (O_node var8))))) (not (= var1 0))) (and (and (and (= var9 (write var15 var12 (O_node (node 2 (|node::n| (getnode (read var15 var12))))))) (= var6 var14)) (= var4 var13)) (= var2 var12)))) (= var0 1)))) (inv_main546_17 var10 var7 var11 var3 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (inv_main539_17 var4 var3 var2 var1 var0)) (inv_main539_17 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 node) (var9 Heap) (var10 Heap) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Heap)) (or (not (and (inv_main535_3 var15 var14 var13 var12) (and (and (= var11 nullAddr) (and (and (and (and (and (and (= var10 (newHeap (alloc var9 (O_node var8)))) (= var7 var6)) (= var5 var4)) (= var3 var2)) (= var11 (newAddr (alloc var9 (O_node var8))))) (not (= var1 0))) (and (and (and (= var9 (write var15 var12 (O_node (node 1 (|node::n| (getnode (read var15 var12))))))) (= var6 var14)) (= var4 var13)) (= var2 var12)))) (= var0 1)))) (inv_main539_17 var10 var7 var11 var3 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main_3 var8 var7 var6 var5) (and (= var4 0) (and (and (and (= var3 (write var8 var5 (O_node (node 3 (|node::n| (getnode (read var8 var5))))))) (= var2 var7)) (= var1 var6)) (= var0 var5))))) (inv_main_22 var3 var2 var1 var2))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Heap)) (or (not (and (inv_main_22 var13 var12 var11 var10) (and (and (and (and (and (= var9 var8) (= var7 var6)) (= var5 var4)) (= var3 var2)) (= var1 (|node::n| (getnode (read var8 var2))))) (and (= var0 1) (and (and (and (and (= var8 var13) (= var6 var12)) (= var4 var11)) (= var2 var10)) (= var0 (|node::h| (getnode (read var13 var10))))))))) (inv_main_22 var9 var7 var5 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 node) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Heap) (var19 Heap) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Heap)) (or (not (and (inv_main535_3 var23 var22 var21 var20) (and (and (and (and (and (and (= var19 var18) (= var17 var16)) (= var15 var14)) (= var13 var12)) (= var11 (|node::n| (getnode (read var18 var12))))) (and (and (and (= var18 (write var10 var9 (O_node (node (|node::h| (getnode (read var10 var9))) var8)))) (= var16 var7)) (= var14 var8)) (= var12 var9))) (and (not (= var8 nullAddr)) (and (and (and (and (and (and (= var10 (newHeap (alloc var6 (O_node var5)))) (= var7 var4)) (= var3 var2)) (= var9 var1)) (= var8 (newAddr (alloc var6 (O_node var5))))) (not (= var0 0))) (and (and (and (= var6 (write var23 var20 (O_node (node 1 (|node::n| (getnode (read var23 var20))))))) (= var4 var22)) (= var2 var21)) (= var1 var20))))))) (inv_main535_3 var19 var17 var15 var11))))
(assert (forall ((var0 Addr) (var1 node) (var2 Heap) (var3 Addr) (var4 Heap)) (or (not (and (inv_main532_3 var4) (and (not (= var3 nullAddr)) (and (= var2 (newHeap (alloc var4 (O_node var1)))) (= var3 (newAddr (alloc var4 (O_node var1)))))))) (inv_main535_3 var2 var3 var0 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (inv_main556_6_28 var3 var2 var1 var0))))
(check-sat)
