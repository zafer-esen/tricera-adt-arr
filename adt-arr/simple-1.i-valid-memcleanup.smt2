(set-logic HORN)
(set-info :source |
    Benchmark: C_VC
    Output by Princess (http://www.philipp.ruemmer.org/princess.shtml)
|)
(set-info :status unsat)
(declare-datatype bool ((true) (false)))
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
(declare-fun inv_exit (Heap Addr) Bool)
(declare-fun inv_main532_3 (Heap Addr) Bool)
(declare-fun inv_main533_15 (Heap Addr Addr Int) Bool)
(declare-fun inv_main540_17 (Heap Addr Addr Addr Addr Int) Bool)
(declare-fun inv_main553_10 (Heap Addr Int) Bool)
(declare-fun inv_main_15 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main_3 (Heap Addr Addr Addr Addr) Bool)
(assert (forall ((var0 Addr) (var1 Heap)) (or (not (and (= var1 emptyHeap) (= var0 nullAddr))) (inv_main532_3 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap) (var10 Int) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Heap)) (or (not (and (inv_main_3 var15 var14 var13 var12 var11) (and (and (= var10 0) (and (and (and (and (= var9 (write var15 var11 (O_node (node 2 (|node::n| (getnode (read var15 var11))))))) (= var8 var14)) (= var7 var13)) (= var6 var12)) (= var5 var11))) (and (and (and (and (= var4 (write var9 var5 (O_node (node (|node::h| (getnode (read var9 var5))) 0)))) (= var3 var8)) (= var2 var7)) (= var1 var6)) (= var0 var5))))) (inv_main_15 var4 var3 var2 var1 var2))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap) (var11 Heap) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Heap)) (or (not (and (inv_main_15 var16 var15 var14 var13 var12) (and (and (and (and (and (and (= var11 var10) (= var9 var8)) (= var7 var6)) (= var5 var4)) (= var3 var2)) (= var1 (|node::n| (getnode (read var10 var2))))) (and (and (= var0 2) (and (and (and (and (and (= var10 var16) (= var8 var15)) (= var6 var14)) (= var4 var13)) (= var2 var12)) (= var0 (|node::h| (getnode (read var16 var12)))))) (not (= var12 nullAddr)))))) (inv_main_15 var11 var9 var7 var5 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Bool) (var7 node) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Heap) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Heap) (var24 Heap) (var25 Addr) (var26 Addr) (var27 Addr) (var28 Addr) (var29 Heap)) (or (not (and (inv_main_3 var29 var28 var27 var26 var25) (and (and (and (and (and (and (and (= var24 var23) (= var22 var21)) (= var20 var19)) (= var18 var17)) (= var16 var15)) (= var14 (|node::n| (getnode (read var23 var15))))) (and (and (and (and (= var23 (write var13 var12 (O_node (node (|node::h| (getnode (read var13 var12))) var11)))) (= var21 var10)) (= var19 var9)) (= var17 var11)) (= var15 var12))) (and (not (= var11 nullAddr)) (and (and (and (and (and (and (and (= var13 (newHeap (alloc var8 (O_node var7)))) (or (and var6 (= var10 (newAddr (alloc var8 (O_node var7))))) (and (not var6) (= var10 var5)))) (= var9 var4)) (= var3 var2)) (= var12 var1)) (= var11 (newAddr (alloc var8 (O_node var7))))) (not (= var0 0))) (and (and (and (and (= var8 (write var29 var25 (O_node (node 1 (|node::n| (getnode (read var29 var25))))))) (= var5 var28)) (= var4 var27)) (= var2 var26)) (= var1 var25))))))) (inv_main_3 var24 var22 var20 var18 var14))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Bool) (var3 Addr) (var4 node) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main532_3 var8 var7) (and (and (not (= var6 nullAddr)) (and (and (= var5 (newHeap (alloc var8 (O_node var4)))) (or (and var2 (= var3 (newAddr (alloc var8 (O_node var4))))) (and (not var2) (= var3 var7)))) (= var6 (newAddr (alloc var8 (O_node var4)))))) (= var1 (write var5 var6 (O_node (node 2 (|node::n| (getnode (read var5 var6)))))))))) (inv_main_3 var1 var3 var6 var0 var6))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Int) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main_15 var10 var9 var8 var7 var6) (and (and (not (= var5 2)) (and (and (and (and (and (= var4 var10) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var0 var6)) (= var5 (|node::h| (getnode (read var10 var6)))))) (not (= var6 nullAddr))))) (inv_exit var4 var3))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (inv_main540_17 var5 var4 var3 var2 var1 var0)) (inv_main540_17 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Bool) (var10 Addr) (var11 node) (var12 Heap) (var13 Heap) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Heap)) (or (not (and (inv_main_3 var19 var18 var17 var16 var15) (and (and (= var14 nullAddr) (and (and (and (and (and (and (and (= var13 (newHeap (alloc var12 (O_node var11)))) (or (and var9 (= var10 (newAddr (alloc var12 (O_node var11))))) (and (not var9) (= var10 var8)))) (= var7 var6)) (= var5 var4)) (= var3 var2)) (= var14 (newAddr (alloc var12 (O_node var11))))) (not (= var1 0))) (and (and (and (and (= var12 (write var19 var15 (O_node (node 1 (|node::n| (getnode (read var19 var15))))))) (= var8 var18)) (= var6 var17)) (= var4 var16)) (= var2 var15)))) (= var0 1)))) (inv_main540_17 var13 var10 var7 var14 var3 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main_15 var5 var4 var3 var2 var1) (and (= var1 nullAddr) (= var0 0)))) (inv_main553_10 var5 var4 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (inv_main533_15 var3 var2 var1 var0)) (inv_main533_15 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Bool) (var2 Addr) (var3 node) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main532_3 var7 var6) (and (and (= var5 nullAddr) (and (and (= var4 (newHeap (alloc var7 (O_node var3)))) (or (and var1 (= var2 (newAddr (alloc var7 (O_node var3))))) (and (not var1) (= var2 var6)))) (= var5 (newAddr (alloc var7 (O_node var3)))))) (= var0 1)))) (inv_main533_15 var4 var2 var5 var0))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_exit var1 var0) (not (= var0 nullAddr))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap)) (not (and (inv_main553_10 var2 var1 var0) (not (= var1 nullAddr))))))
(check-sat)
