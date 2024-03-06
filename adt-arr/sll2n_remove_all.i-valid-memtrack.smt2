(set-logic HORN)
(set-info :source |
    Benchmark: C_VC
    Output by Princess (http://www.philipp.ruemmer.org/princess.shtml)
|)
(set-info :status unknown)
(declare-datatype bool ((true) (false)))
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
(declare-fun inv_exit (Heap Addr) Bool)
(declare-fun inv_main577_5 (Heap Addr Int Int Int Int Addr Int Addr Int) Bool)
(declare-fun inv_main585_7 (Heap Addr Int Int Int Int Addr) Bool)
(declare-fun inv_main600_3 (Heap Addr Int Int) Bool)
(declare-fun inv_main602_7 (Heap Addr Int Int Addr Int) Bool)
(declare-fun inv_main610_10 (Heap Addr Int) Bool)
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Heap)) (or (not (and (and (and (= var3 emptyHeap) (= var2 nullAddr)) (= var1 2)) (= var0 1))) (inv_main600_3 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Addr) (var5 Int) (var6 Int) (var7 Addr) (var8 Heap) (var9 Addr) (var10 Int) (var11 Int) (var12 Addr) (var13 Int) (var14 Int) (var15 Addr) (var16 Heap) (var17 Int) (var18 Addr) (var19 Int) (var20 Int) (var21 Addr) (var22 Heap)) (or (not (and (inv_main602_7 var22 var21 var20 var19 var18 var17) (and (and (and (and (and (and (and (and (and (and (= var16 var22) (= var15 var21)) (= var14 var20)) (= var13 var19)) (= var12 var18)) (= var11 var17)) (= var10 4)) (= var9 (|node::next| (getnode (read var22 var18))))) (and (and (and (and (and (and (and (= var8 (write var16 var12 defObj)) (or (and (= var15 var12) (= var7 nullAddr)) (and (not (= var15 var12)) (= var7 var15)))) (= var6 var14)) (= var5 var13)) (= var4 var12)) (= var3 var11)) (= var2 var10)) (= var1 var9))) (<= 0 var17)) (= var0 (+ var3 (- 1)))))) (inv_main602_7 var8 var7 var6 var5 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Addr) (var7 Heap)) (or (not (and (inv_main585_7 var7 var6 var5 var4 var3 var2 var1) (and (not (<= 0 (+ var3 (- 1)))) (= var0 (+ var5 (- 1)))))) (inv_main602_7 var7 var6 var5 var4 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Addr) (var8 Heap) (var9 Bool) (var10 node) (var11 Addr) (var12 Int) (var13 Addr) (var14 Int) (var15 Int) (var16 Int) (var17 Int) (var18 Addr) (var19 Heap) (var20 Addr) (var21 Int) (var22 Int) (var23 Addr) (var24 Addr) (var25 Int) (var26 Int) (var27 Int) (var28 Int) (var29 Int) (var30 Int) (var31 Int) (var32 Int) (var33 Addr) (var34 Addr) (var35 Addr) (var36 Heap) (var37 Heap) (var38 Addr) (var39 Int) (var40 Int) (var41 Int) (var42 Int) (var43 Addr) (var44 Heap)) (or (not (and (inv_main585_7 var44 var43 var42 var41 var40 var39 var38) (and (and (and (and (and (and (and (and (and (and (and (and (and (= var37 (write var36 var35 (O_node (node (|node::data| (getnode (read var36 var35))) nullAddr)))) (= var34 var33)) (= var32 var31)) (= var30 var29)) (= var28 var27)) (= var26 var25)) (= var24 var23)) (= var22 var21)) (= var20 var35)) (and (and (and (and (and (and (and (and (= var19 (write var37 var20 (O_node (node var22 (|node::next| (getnode (read var37 var20))))))) (= var18 var34)) (= var17 var32)) (= var16 var30)) (= var15 var28)) (= var14 var26)) (= var13 var24)) (= var12 var22)) (= var11 var20))) (and (not (= nullAddr var35)) (and (and (and (and (and (and (and (and (= var36 (newHeap (alloc var44 (O_node var10)))) (or (and var9 (= var33 (newAddr (alloc var44 (O_node var10))))) (and (not var9) (= var33 var43)))) (= var31 var42)) (= var29 var41)) (= var27 var40)) (= var25 var39)) (= var23 var38)) (= var21 var39)) (= var35 (newAddr (alloc var44 (O_node var10))))))) (and (and (and (and (and (and (and (= var8 (write var19 var11 (O_node (node (|node::data| (getnode (read var19 var11))) var13)))) (= var7 var18)) (= var6 var17)) (= var5 var16)) (= var4 var15)) (= var3 var14)) (= var2 var13)) (= var1 var11))) (<= 0 (+ var40 (- 1)))) (= var0 (+ var4 (- 1)))))) (inv_main585_7 var8 var7 var6 var5 var0 var3 var1))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Int) (var4 Int) (var5 Addr) (var6 Heap) (var7 Int) (var8 Int) (var9 Addr) (var10 Heap)) (or (not (and (inv_main600_3 var10 var9 var8 var7) (and (and (and (and (and (and (= var6 var10) (= var5 var9)) (= var4 var8)) (= var3 var7)) (= var2 var8)) (= var1 var7)) (= var0 nullAddr)))) (inv_main585_7 var6 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Addr) (var5 Heap)) (or (not (and (inv_main602_7 var5 var4 var3 var2 var1 var0) (and (not (= nullAddr var1)) (not (<= 0 var0))))) (inv_exit var5 var4))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Addr) (var4 Int) (var5 Int) (var6 Int) (var7 Int) (var8 Addr) (var9 Heap)) (or (not (inv_main577_5 var9 var8 var7 var6 var5 var4 var3 var2 var1 var0)) (inv_main577_5 var9 var8 var7 var6 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Bool) (var8 Addr) (var9 node) (var10 Heap) (var11 Addr) (var12 Addr) (var13 Int) (var14 Int) (var15 Int) (var16 Int) (var17 Addr) (var18 Heap)) (or (not (and (inv_main585_7 var18 var17 var16 var15 var14 var13 var12) (and (and (and (= nullAddr var11) (and (and (and (and (and (and (and (and (= var10 (newHeap (alloc var18 (O_node var9)))) (or (and var7 (= var8 (newAddr (alloc var18 (O_node var9))))) (and (not var7) (= var8 var17)))) (= var6 var16)) (= var5 var15)) (= var4 var14)) (= var3 var13)) (= var2 var12)) (= var1 var13)) (= var11 (newAddr (alloc var18 (O_node var9)))))) (<= 0 (+ var14 (- 1)))) (= var0 1)))) (inv_main577_5 var10 var8 var6 var5 var4 var3 var2 var1 var11 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Int) (var4 Int) (var5 Addr) (var6 Heap)) (or (not (and (inv_main602_7 var6 var5 var4 var3 var2 var1) (and (and (= nullAddr var2) (not (<= 0 var1))) (= var0 0)))) (inv_main610_10 var6 var5 var0))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_exit var1 var0) (not (= var0 nullAddr))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap)) (not (and (inv_main610_10 var2 var1 var0) (not (= var1 nullAddr))))))
(check-sat)
