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
(declare-fun inv_main533_3 (Heap Int) Bool)
(declare-fun inv_main534_15 (Heap Int Addr Int) Bool)
(declare-fun inv_main536_3 (Heap Int Addr Addr Addr) Bool)
(declare-fun inv_main546_17 (Heap Int Addr Addr Addr Int) Bool)
(declare-fun inv_main_16 (Heap Int Addr Addr Addr) Bool)
(declare-fun inv_main_26 (Heap Int Addr Addr Addr) Bool)
(declare-fun inv_main_31 (Heap Int Addr Addr Addr) Bool)
(assert (forall ((var0 Int) (var1 Heap)) (or (not (and (= var1 emptyHeap) (= var0 1))) (inv_main533_3 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap) (var6 Int) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Int) (var11 Heap)) (or (not (and (inv_main536_3 var11 var10 var9 var8 var7) (and (and (= var6 0) (and (and (and (and (= var5 (write var11 var7 (O_node (node 3 (|node::n| (getnode (read var11 var7))))))) (= var4 var10)) (= var3 var9)) (= var2 var8)) (= var1 var7))) (= var0 1)))) (inv_main_16 var5 var0 var3 var2 var3))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Int) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Int) (var15 Int) (var16 Heap) (var17 Heap) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Int) (var22 Heap)) (or (not (and (inv_main_16 var22 var21 var20 var19 var18) (and (and (and (and (and (and (= var17 var16) (= var15 var14)) (= var13 var12)) (= var11 var10)) (= var9 var8)) (= var7 (|node::n| (getnode (read var16 var8))))) (and (and (= var6 1) (and (and (and (and (and (= var16 var5) (= var14 0)) (= var12 var4)) (= var10 var3)) (= var8 var2)) (= var6 (|node::h| (getnode (read var5 var2)))))) (and (not (= var1 0)) (and (not (= var0 3)) (and (and (and (and (and (= var5 var22) (= var1 var21)) (= var4 var20)) (= var3 var19)) (= var2 var18)) (= var0 (|node::h| (getnode (read var22 var18))))))))))) (inv_main_16 var17 var15 var13 var11 var7))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Int) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Int) (var15 Int) (var16 Heap) (var17 Heap) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Int) (var22 Heap)) (or (not (and (inv_main_16 var22 var21 var20 var19 var18) (and (and (and (and (and (and (= var17 var16) (= var15 var14)) (= var13 var12)) (= var11 var10)) (= var9 var8)) (= var7 (|node::n| (getnode (read var16 var8))))) (and (and (= var6 2) (and (and (and (and (and (= var16 var5) (= var14 1)) (= var12 var4)) (= var10 var3)) (= var8 var2)) (= var6 (|node::h| (getnode (read var5 var2)))))) (and (= var1 0) (and (not (= var0 3)) (and (and (and (and (and (= var5 var22) (= var1 var21)) (= var4 var20)) (= var3 var19)) (= var2 var18)) (= var0 (|node::h| (getnode (read var22 var18))))))))))) (inv_main_16 var17 var15 var13 var11 var7))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Int) (var9 Heap) (var10 Heap) (var11 Int) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Int) (var16 Heap)) (or (not (and (inv_main_16 var16 var15 var14 var13 var12) (and (and (not (= var11 1)) (and (and (and (and (and (= var10 var9) (= var8 0)) (= var7 var6)) (= var5 var4)) (= var3 var2)) (= var11 (|node::h| (getnode (read var9 var2)))))) (and (not (= var1 0)) (and (not (= var0 3)) (and (and (and (and (and (= var9 var16) (= var1 var15)) (= var6 var14)) (= var4 var13)) (= var2 var12)) (= var0 (|node::h| (getnode (read var16 var12)))))))))) (inv_main_31 var10 var8 var7 var5 var3))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Int) (var9 Heap) (var10 Heap) (var11 Int) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Int) (var16 Heap)) (or (not (and (inv_main_16 var16 var15 var14 var13 var12) (and (and (not (= var11 2)) (and (and (and (and (and (= var10 var9) (= var8 1)) (= var7 var6)) (= var5 var4)) (= var3 var2)) (= var11 (|node::h| (getnode (read var9 var2)))))) (and (= var1 0) (and (not (= var0 3)) (and (and (and (and (and (= var9 var16) (= var1 var15)) (= var6 var14)) (= var4 var13)) (= var2 var12)) (= var0 (|node::h| (getnode (read var16 var12)))))))))) (inv_main_31 var10 var8 var7 var5 var3))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 node) (var7 Heap) (var8 Addr) (var9 Int) (var10 Addr) (var11 Addr) (var12 Heap) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Int) (var21 Int) (var22 Heap) (var23 Heap) (var24 Addr) (var25 Addr) (var26 Addr) (var27 Int) (var28 Heap)) (or (not (and (inv_main536_3 var28 var27 var26 var25 var24) (and (and (and (and (and (and (and (= var23 var22) (= var21 var20)) (= var19 var18)) (= var17 var16)) (= var15 var14)) (= var13 (|node::n| (getnode (read var22 var14))))) (and (and (and (and (= var22 (write var12 var11 (O_node (node (|node::h| (getnode (read var12 var11))) var10)))) (= var20 var9)) (= var18 var8)) (= var16 var10)) (= var14 var11))) (and (and (not (= var10 nullAddr)) (and (and (and (and (and (= var12 (newHeap (alloc var7 (O_node var6)))) (= var9 0)) (= var8 var5)) (= var4 var3)) (= var11 var2)) (= var10 (newAddr (alloc var7 (O_node var6)))))) (and (and (not (= var27 0)) (not (= var1 0))) (and (and (and (and (= var7 (write var28 var24 (O_node (node 2 (|node::n| (getnode (read var28 var24))))))) (= var0 var27)) (= var5 var26)) (= var3 var25)) (= var2 var24))))))) (inv_main536_3 var23 var21 var19 var17 var13))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 node) (var7 Heap) (var8 Addr) (var9 Int) (var10 Addr) (var11 Addr) (var12 Heap) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Int) (var21 Int) (var22 Heap) (var23 Heap) (var24 Addr) (var25 Addr) (var26 Addr) (var27 Int) (var28 Heap)) (or (not (and (inv_main536_3 var28 var27 var26 var25 var24) (and (and (and (and (and (and (and (= var23 var22) (= var21 var20)) (= var19 var18)) (= var17 var16)) (= var15 var14)) (= var13 (|node::n| (getnode (read var22 var14))))) (and (and (and (and (= var22 (write var12 var11 (O_node (node (|node::h| (getnode (read var12 var11))) var10)))) (= var20 var9)) (= var18 var8)) (= var16 var10)) (= var14 var11))) (and (and (not (= var10 nullAddr)) (and (and (and (and (and (= var12 (newHeap (alloc var7 (O_node var6)))) (= var9 1)) (= var8 var5)) (= var4 var3)) (= var11 var2)) (= var10 (newAddr (alloc var7 (O_node var6)))))) (and (and (= var27 0) (not (= var1 0))) (and (and (and (and (= var7 (write var28 var24 (O_node (node 1 (|node::n| (getnode (read var28 var24))))))) (= var0 var27)) (= var5 var26)) (= var3 var25)) (= var2 var24))))))) (inv_main536_3 var23 var21 var19 var17 var13))))
(assert (forall ((var0 Addr) (var1 Int) (var2 node) (var3 Heap) (var4 Addr) (var5 Int) (var6 Heap)) (or (not (and (inv_main533_3 var6 var5) (and (not (= var4 nullAddr)) (and (and (= var3 (newHeap (alloc var6 (O_node var2)))) (= var1 var5)) (= var4 (newAddr (alloc var6 (O_node var2)))))))) (inv_main536_3 var3 var1 var4 var0 var4))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap) (var5 Int) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Int) (var10 Heap)) (or (not (and (inv_main_16 var10 var9 var8 var7 var6) (and (= var5 3) (and (and (and (and (and (= var4 var10) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var0 var6)) (= var5 (|node::h| (getnode (read var10 var6)))))))) (inv_main_26 var4 var3 var2 var1 var2))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Int) (var11 Int) (var12 Heap) (var13 Heap) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Int) (var18 Heap)) (or (not (and (inv_main_26 var18 var17 var16 var15 var14) (and (and (and (and (and (and (and (and (= var13 var12) (= var11 var10)) (= var9 var8)) (= var7 var6)) (= var5 var4)) (= var3 var4)) (= var2 (|node::n| (getnode (read var12 var4))))) (and (not (= var1 3)) (and (and (and (and (and (= var12 var18) (= var10 var17)) (= var8 var16)) (= var6 var15)) (= var4 var14)) (= var1 (|node::h| (getnode (read var18 var14))))))) (= var0 (write var13 var3 defObj))))) (inv_main_26 var0 var11 var9 var7 var2))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Heap)) (or (not (inv_main534_15 var3 var2 var1 var0)) (inv_main534_15 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 node) (var3 Heap) (var4 Addr) (var5 Int) (var6 Heap)) (or (not (and (inv_main533_3 var6 var5) (and (and (= var4 nullAddr) (and (and (= var3 (newHeap (alloc var6 (O_node var2)))) (= var1 var5)) (= var4 (newAddr (alloc var6 (O_node var2)))))) (= var0 1)))) (inv_main534_15 var3 var1 var4 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap)) (or (not (inv_main546_17 var5 var4 var3 var2 var1 var0)) (inv_main546_17 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Int) (var10 node) (var11 Heap) (var12 Heap) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Int) (var18 Heap)) (or (not (and (inv_main536_3 var18 var17 var16 var15 var14) (and (and (and (= var13 nullAddr) (and (and (and (and (and (= var12 (newHeap (alloc var11 (O_node var10)))) (= var9 0)) (= var8 var7)) (= var6 var5)) (= var4 var3)) (= var13 (newAddr (alloc var11 (O_node var10)))))) (and (and (not (= var17 0)) (not (= var2 0))) (and (and (and (and (= var11 (write var18 var14 (O_node (node 2 (|node::n| (getnode (read var18 var14))))))) (= var1 var17)) (= var7 var16)) (= var5 var15)) (= var3 var14)))) (= var0 1)))) (inv_main546_17 var12 var9 var8 var13 var4 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Int) (var10 node) (var11 Heap) (var12 Heap) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Int) (var18 Heap)) (or (not (and (inv_main536_3 var18 var17 var16 var15 var14) (and (and (and (= var13 nullAddr) (and (and (and (and (and (= var12 (newHeap (alloc var11 (O_node var10)))) (= var9 1)) (= var8 var7)) (= var6 var5)) (= var4 var3)) (= var13 (newAddr (alloc var11 (O_node var10)))))) (and (and (= var17 0) (not (= var2 0))) (and (and (and (and (= var11 (write var18 var14 (O_node (node 1 (|node::n| (getnode (read var18 var14))))))) (= var1 var17)) (= var7 var16)) (= var5 var15)) (= var3 var14)))) (= var0 1)))) (inv_main546_17 var12 var9 var8 var13 var4 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap)) (not (inv_main_31 var4 var3 var2 var1 var0))))
(check-sat)
