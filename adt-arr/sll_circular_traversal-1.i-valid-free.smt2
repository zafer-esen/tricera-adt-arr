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
                   ((node (|node::next| Addr) (|node::data| Int)))))
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
(declare-fun inv_main577_5 (Heap Int Int Int Int Addr Int) Bool)
(declare-fun inv_main581_3 (Heap Int Int Int Int Addr Addr) Bool)
(declare-fun inv_main585_7 (Heap Int Int Int Int Addr Addr Addr Int) Bool)
(declare-fun inv_main598_3 (Heap Int Int) Bool)
(declare-fun inv_main600_3 (Heap Int Int Addr Int Addr) Bool)
(declare-fun inv_main615_9 (Heap Int Int Addr Int Addr Addr) Bool)
(declare-fun inv_main_20 (Heap Int Int Addr Int Addr) Bool)
(declare-fun inv_main_21 (Heap Int Int Addr Int Addr) Bool)
(assert (forall ((var0 Int) (var1 Int) (var2 Heap)) (or (not (and (and (= var2 emptyHeap) (= var1 5)) (= var0 1))) (inv_main598_3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Int) (var6 Int) (var7 Int) (var8 Heap)) (or (not (inv_main585_7 var8 var7 var6 var5 var4 var3 var2 var1 var0)) (inv_main585_7 var8 var7 var6 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 node) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Int) (var13 Int) (var14 Int) (var15 Int) (var16 Heap)) (or (not (and (inv_main581_3 var16 var15 var14 var13 var12 var11 var10) (and (and (and (= nullAddr var9) (and (and (and (and (and (and (and (= var8 (newHeap (alloc var16 (O_node var7)))) (= var6 var15)) (= var5 var14)) (= var4 var13)) (= var3 var12)) (= var2 var11)) (= var1 var10)) (= var9 (newAddr (alloc var16 (O_node var7)))))) (<= 0 (+ (+ var13 (- 1)) (- 1)))) (= var0 1)))) (inv_main585_7 var8 var6 var5 var4 var3 var2 var1 var9 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Heap)) (or (not (inv_main577_5 var6 var5 var4 var3 var2 var1 var0)) (inv_main577_5 var6 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Int) (var4 Int) (var5 node) (var6 Heap) (var7 Addr) (var8 Int) (var9 Int) (var10 Heap)) (or (not (and (inv_main598_3 var10 var9 var8) (and (and (= nullAddr var7) (and (and (and (and (and (= var6 (newHeap (alloc var10 (O_node var5)))) (= var4 var9)) (= var3 var8)) (= var2 var9)) (= var1 var8)) (= var7 (newAddr (alloc var10 (O_node var5)))))) (= var0 1)))) (inv_main577_5 var6 var4 var3 var2 var1 var7 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Int) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Int) (var9 Addr) (var10 Int) (var11 Int) (var12 Heap)) (or (not (and (inv_main_20 var12 var11 var10 var9 var8 var7) (and (and (not (= var6 var5)) (and (and (and (and (and (and (= var4 var12) (= var3 var11)) (= var2 var10)) (= var5 var9)) (= var1 var8)) (= var6 var7)) (= var0 (|node::next| (getnode (read var12 var7)))))) (= var8 (|node::data| (getnode (read var12 var7))))))) (inv_main615_9 var4 var3 var2 var5 var1 var6 var0))))
(assert (forall ((var0 Int) (var1 node) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Int) (var6 Int) (var7 Int) (var8 Int) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Int) (var15 Int) (var16 Int) (var17 Int) (var18 Int) (var19 Int) (var20 Int) (var21 Int) (var22 Addr) (var23 Addr) (var24 Heap) (var25 Heap) (var26 Addr) (var27 Addr) (var28 Int) (var29 Int) (var30 Int) (var31 Int) (var32 Heap)) (or (not (and (inv_main581_3 var32 var31 var30 var29 var28 var27 var26) (and (and (and (and (and (and (and (and (and (and (and (= var25 (write var24 var23 (O_node (node var22 (|node::data| (getnode (read var24 var23))))))) (= var21 var20)) (= var19 var18)) (= var17 var16)) (= var15 var14)) (= var13 var12)) (= var11 var22)) (= var10 var23)) (and (and (and (and (and (and (and (= var9 (write var25 var10 (O_node (node (|node::next| (getnode (read var25 var10))) var15)))) (= var8 var21)) (= var7 var19)) (= var6 var17)) (= var5 var15)) (= var4 var13)) (= var3 var11)) (= var2 var10))) (and (not (= nullAddr var23)) (and (and (and (and (and (and (and (= var24 (newHeap (alloc var32 (O_node var1)))) (= var20 var31)) (= var18 var30)) (= var16 var29)) (= var14 var28)) (= var12 var27)) (= var22 var26)) (= var23 (newAddr (alloc var32 (O_node var1))))))) (<= 0 (+ (+ var29 (- 1)) (- 1)))) (= var0 (+ var6 (- 1)))))) (inv_main581_3 var9 var8 var7 var0 var5 var4 var2))))
(assert (forall ((var0 node) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Heap) (var7 Addr) (var8 Int) (var9 Int) (var10 Int) (var11 Int) (var12 Int) (var13 Int) (var14 Int) (var15 Int) (var16 Addr) (var17 Heap) (var18 Heap) (var19 Int) (var20 Int) (var21 Heap)) (or (not (and (inv_main598_3 var21 var20 var19) (and (and (and (and (and (and (and (= var18 (write var17 var16 (O_node (node var16 (|node::data| (getnode (read var17 var16))))))) (= var15 var14)) (= var13 var12)) (= var11 var10)) (= var9 var8)) (= var7 var16)) (and (and (and (and (and (= var6 (write var18 var7 (O_node (node (|node::next| (getnode (read var18 var7))) var9)))) (= var5 var15)) (= var4 var13)) (= var3 var11)) (= var2 var9)) (= var1 var7))) (and (not (= nullAddr var16)) (and (and (and (and (and (= var17 (newHeap (alloc var21 (O_node var0)))) (= var14 var20)) (= var12 var19)) (= var10 var20)) (= var8 var19)) (= var16 (newAddr (alloc var21 (O_node var0))))))))) (inv_main581_3 var6 var5 var4 var3 var2 var1 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Addr) (var6 Int) (var7 Int) (var8 Int) (var9 Int) (var10 Heap) (var11 Heap) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Int) (var16 Addr) (var17 Int) (var18 Int) (var19 Heap)) (or (not (and (inv_main600_3 var19 var18 var17 var16 var15 var14) (and (and (not (= var13 var12)) (and (and (and (and (and (and (and (and (= var11 var10) (= var9 var8)) (= var7 var6)) (= var12 var5)) (= var4 var3)) (= var2 var1)) (= var13 (|node::next| (getnode (read var10 var1))))) (= var17 (|node::data| (getnode (read var19 var14))))) (and (and (and (and (and (= var10 (write var19 var14 (O_node (node (|node::next| (getnode (read var19 var14))) var15)))) (= var8 var18)) (= var6 var17)) (= var5 var16)) (= var3 var15)) (= var1 var14)))) (= var0 (+ var4 1))))) (inv_main600_3 var11 var9 var7 var12 var0 var13))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Int) (var11 Int) (var12 Int) (var13 Int) (var14 Heap)) (or (not (and (inv_main581_3 var14 var13 var12 var11 var10 var9 var8) (and (and (not (<= 0 (+ (+ var11 (- 1)) (- 1)))) (and (and (and (and (and (and (= var7 (write var14 var9 (O_node (node var8 (|node::data| (getnode (read var14 var9))))))) (= var6 var13)) (= var5 var12)) (= var4 var11)) (= var3 var10)) (= var2 var9)) (= var1 var8))) (= var0 1)))) (inv_main600_3 var7 var6 var5 var1 var0 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Addr) (var6 Int) (var7 Int) (var8 Int) (var9 Int) (var10 Heap) (var11 Heap) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Int) (var16 Addr) (var17 Int) (var18 Int) (var19 Heap)) (or (not (and (inv_main600_3 var19 var18 var17 var16 var15 var14) (and (and (= var13 var12) (and (and (and (and (and (and (and (and (= var11 var10) (= var9 var8)) (= var7 var6)) (= var12 var5)) (= var4 var3)) (= var2 var1)) (= var13 (|node::next| (getnode (read var10 var1))))) (= var17 (|node::data| (getnode (read var19 var14))))) (and (and (and (and (and (= var10 (write var19 var14 (O_node (node (|node::next| (getnode (read var19 var14))) var15)))) (= var8 var18)) (= var6 var17)) (= var5 var16)) (= var3 var15)) (= var1 var14)))) (= var0 (+ (+ var4 1) (* (- 1) var9)))))) (inv_main_20 var11 var9 var7 var12 var0 var13))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Int) (var11 Addr) (var12 Int) (var13 Int) (var14 Heap)) (or (not (and (inv_main615_9 var14 var13 var12 var11 var10 var9 var8) (and (and (not (= var7 var6)) (and (and (and (and (and (and (= var5 (write var14 var9 defObj)) (= var4 var13)) (= var3 var12)) (= var6 var11)) (= var2 var10)) (= var1 var9)) (= var7 var8))) (= var0 (+ var2 1))))) (inv_main_20 var5 var4 var3 var6 var0 var7))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Int) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Int) (var10 Addr) (var11 Int) (var12 Int) (var13 Heap)) (or (not (and (inv_main_20 var13 var12 var11 var10 var9 var8) (and (and (not (= var7 var6)) (and (and (= var5 var6) (and (and (and (and (and (and (= var4 var13) (= var3 var12)) (= var2 var11)) (= var6 var10)) (= var1 var9)) (= var5 var8)) (= var7 (|node::next| (getnode (read var13 var8)))))) (= var9 (|node::data| (getnode (read var13 var8)))))) (= var0 (+ var1 1))))) (inv_main_20 var4 var3 var2 var6 var0 var7))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Int) (var11 Addr) (var12 Int) (var13 Int) (var14 Heap)) (or (not (and (inv_main615_9 var14 var13 var12 var11 var10 var9 var8) (and (and (= var7 var6) (and (and (and (and (and (and (= var5 (write var14 var9 defObj)) (= var4 var13)) (= var3 var12)) (= var6 var11)) (= var2 var10)) (= var1 var9)) (= var7 var8))) (= var0 (+ var2 1))))) (inv_main_21 var5 var4 var3 var6 var0 var7))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Int) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Int) (var10 Addr) (var11 Int) (var12 Int) (var13 Heap)) (or (not (and (inv_main_20 var13 var12 var11 var10 var9 var8) (and (and (= var7 var6) (and (and (= var5 var6) (and (and (and (and (and (and (= var4 var13) (= var3 var12)) (= var2 var11)) (= var6 var10)) (= var1 var9)) (= var5 var8)) (= var7 (|node::next| (getnode (read var13 var8)))))) (= var9 (|node::data| (getnode (read var13 var8)))))) (= var0 (+ var1 1))))) (inv_main_21 var4 var3 var2 var6 var0 var7))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Int) (var5 Int) (var6 Heap)) (not (and (inv_main615_9 var6 var5 var4 var3 var2 var1 var0) (and (not (= var1 nullAddr)) (= (read var6 var1) defObj))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Int) (var4 Int) (var5 Heap)) (not (and (inv_main_21 var5 var4 var3 var2 var1 var0) (and (not (= var2 nullAddr)) (= (read var5 var2) defObj))))))
(check-sat)
