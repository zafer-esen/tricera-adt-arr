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
                   ((node (|node::data| Int) (|node::next| Addr)))))
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
(declare-fun inv_main577_5 (Heap Int Int Int Int Addr Int Addr Int) Bool)
(declare-fun inv_main585_7 (Heap Int Int Int Int Addr) Bool)
(declare-fun inv_main600_3 (Heap Int Int) Bool)
(declare-fun inv_main602_7 (Heap Int Int Addr Int) Bool)
(declare-fun inv_main_15 (Heap Int Int Addr Int) Bool)
(assert (forall ((var0 Int) (var1 Int) (var2 Heap)) (or (not (and (and (= var2 emptyHeap) (= var1 2)) (= var0 1))) (inv_main600_3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Heap) (var8 node) (var9 Addr) (var10 Int) (var11 Addr) (var12 Int) (var13 Int) (var14 Int) (var15 Int) (var16 Heap) (var17 Addr) (var18 Int) (var19 Int) (var20 Addr) (var21 Addr) (var22 Int) (var23 Int) (var24 Int) (var25 Int) (var26 Int) (var27 Int) (var28 Int) (var29 Int) (var30 Addr) (var31 Heap) (var32 Heap) (var33 Addr) (var34 Int) (var35 Int) (var36 Int) (var37 Int) (var38 Heap)) (or (not (and (inv_main585_7 var38 var37 var36 var35 var34 var33) (and (and (and (and (and (and (and (and (and (and (and (and (= var32 (write var31 var30 (O_node (node (|node::data| (getnode (read var31 var30))) nullAddr)))) (= var29 var28)) (= var27 var26)) (= var25 var24)) (= var23 var22)) (= var21 var20)) (= var19 var18)) (= var17 var30)) (and (and (and (and (and (and (and (= var16 (write var32 var17 (O_node (node var19 (|node::next| (getnode (read var32 var17))))))) (= var15 var29)) (= var14 var27)) (= var13 var25)) (= var12 var23)) (= var11 var21)) (= var10 var19)) (= var9 var17))) (and (not (= nullAddr var30)) (and (and (and (and (and (and (and (= var31 (newHeap (alloc var38 (O_node var8)))) (= var28 var37)) (= var26 var36)) (= var24 var35)) (= var22 var34)) (= var20 var33)) (= var18 var34)) (= var30 (newAddr (alloc var38 (O_node var8))))))) (and (and (and (and (and (and (= var7 (write var16 var9 (O_node (node (|node::data| (getnode (read var16 var9))) var11)))) (= var6 var15)) (= var5 var14)) (= var4 var13)) (= var3 var12)) (= var2 var11)) (= var1 var9))) (<= 0 (+ var35 (- 1)))) (= var0 (+ var4 (- 1)))))) (inv_main585_7 var7 var6 var5 var0 var3 var1))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Int) (var4 Int) (var5 Heap) (var6 Int) (var7 Int) (var8 Heap)) (or (not (and (inv_main600_3 var8 var7 var6) (and (and (and (and (and (= var5 var8) (= var4 var7)) (= var3 var6)) (= var2 var7)) (= var1 var6)) (= var0 nullAddr)))) (inv_main585_7 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Addr) (var4 Int) (var5 Int) (var6 Int) (var7 Int) (var8 Heap)) (or (not (inv_main577_5 var8 var7 var6 var5 var4 var3 var2 var1 var0)) (inv_main577_5 var8 var7 var6 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 node) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Int) (var12 Int) (var13 Int) (var14 Int) (var15 Heap)) (or (not (and (inv_main585_7 var15 var14 var13 var12 var11 var10) (and (and (and (= nullAddr var9) (and (and (and (and (and (and (and (= var8 (newHeap (alloc var15 (O_node var7)))) (= var6 var14)) (= var5 var13)) (= var4 var12)) (= var3 var11)) (= var2 var10)) (= var1 var11)) (= var9 (newAddr (alloc var15 (O_node var7)))))) (<= 0 (+ var12 (- 1)))) (= var0 1)))) (inv_main577_5 var8 var6 var5 var4 var3 var2 var1 var9 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Addr) (var5 Int) (var6 Int) (var7 Heap) (var8 Addr) (var9 Int) (var10 Int) (var11 Addr) (var12 Int) (var13 Int) (var14 Heap) (var15 Int) (var16 Addr) (var17 Int) (var18 Int) (var19 Heap)) (or (not (and (inv_main602_7 var19 var18 var17 var16 var15) (and (and (and (and (and (and (and (and (and (= var14 var19) (= var13 var18)) (= var12 var17)) (= var11 var16)) (= var10 var15)) (= var9 3)) (= var8 (|node::next| (getnode (read var19 var16))))) (and (and (and (and (and (and (= var7 (write var14 var11 defObj)) (= var6 var13)) (= var5 var12)) (= var4 var11)) (= var3 var10)) (= var2 var9)) (= var1 var8))) (<= 0 var15)) (= var0 (+ var3 (- 1)))))) (inv_main602_7 var7 var6 var5 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Heap)) (or (not (and (inv_main585_7 var6 var5 var4 var3 var2 var1) (and (not (<= 0 (+ var3 (- 1)))) (= var0 (+ var5 (- 1)))))) (inv_main602_7 var6 var5 var4 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Heap)) (or (not (and (inv_main602_7 var4 var3 var2 var1 var0) (and (not (= nullAddr var1)) (not (<= 0 var0))))) (inv_main_15 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Heap)) (not (inv_main_15 var4 var3 var2 var1 var0))))
(check-sat)
