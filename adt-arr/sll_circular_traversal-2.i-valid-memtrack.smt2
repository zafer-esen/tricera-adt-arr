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
(declare-fun inv_exit (Heap Addr) Bool)
(declare-fun inv_main577_5 (Heap Addr Int Int Int Int Addr Int) Bool)
(declare-fun inv_main581_3 (Heap Addr Int Int Int Int Addr Addr) Bool)
(declare-fun inv_main585_7 (Heap Addr Int Int Int Int Addr Addr Addr Int) Bool)
(declare-fun inv_main598_3 (Heap Addr Int Int) Bool)
(declare-fun inv_main600_3 (Heap Addr Int Int Addr Int Addr) Bool)
(declare-fun inv_main621_10 (Heap Addr Int) Bool)
(declare-fun inv_main_20 (Heap Addr Int Int Addr Int Addr) Bool)
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Heap)) (or (not (and (and (and (= var3 emptyHeap) (= var2 nullAddr)) (= var1 5)) (= var0 1))) (inv_main598_3 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Bool) (var2 node) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Int) (var7 Int) (var8 Int) (var9 Int) (var10 Addr) (var11 Heap) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Int) (var17 Int) (var18 Int) (var19 Int) (var20 Int) (var21 Int) (var22 Int) (var23 Int) (var24 Addr) (var25 Addr) (var26 Addr) (var27 Addr) (var28 Heap) (var29 Heap) (var30 Addr) (var31 Addr) (var32 Int) (var33 Int) (var34 Int) (var35 Int) (var36 Addr) (var37 Heap)) (or (not (and (inv_main581_3 var37 var36 var35 var34 var33 var32 var31 var30) (and (and (and (and (and (and (and (and (and (and (and (and (= var29 (write var28 var27 (O_node (node var26 (|node::data| (getnode (read var28 var27))))))) (= var25 var24)) (= var23 var22)) (= var21 var20)) (= var19 var18)) (= var17 var16)) (= var15 var14)) (= var13 var26)) (= var12 var27)) (and (and (and (and (and (and (and (and (= var11 (write var29 var12 (O_node (node (|node::next| (getnode (read var29 var12))) var17)))) (= var10 var25)) (= var9 var23)) (= var8 var21)) (= var7 var19)) (= var6 var17)) (= var5 var15)) (= var4 var13)) (= var3 var12))) (and (not (= nullAddr var27)) (and (and (and (and (and (and (and (and (= var28 (newHeap (alloc var37 (O_node var2)))) (or (and var1 (= var24 (newAddr (alloc var37 (O_node var2))))) (and (not var1) (= var24 var36)))) (= var22 var35)) (= var20 var34)) (= var18 var33)) (= var16 var32)) (= var14 var31)) (= var26 var30)) (= var27 (newAddr (alloc var37 (O_node var2))))))) (<= 0 (+ (+ var33 (- 1)) (- 1)))) (= var0 (+ var7 (- 1)))))) (inv_main581_3 var11 var10 var9 var8 var0 var6 var5 var3))))
(assert (forall ((var0 Bool) (var1 node) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Addr) (var8 Heap) (var9 Addr) (var10 Int) (var11 Int) (var12 Int) (var13 Int) (var14 Int) (var15 Int) (var16 Int) (var17 Int) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Heap) (var22 Heap) (var23 Int) (var24 Int) (var25 Addr) (var26 Heap)) (or (not (and (inv_main598_3 var26 var25 var24 var23) (and (and (and (and (and (and (and (and (= var22 (write var21 var20 (O_node (node var20 (|node::data| (getnode (read var21 var20))))))) (= var19 var18)) (= var17 var16)) (= var15 var14)) (= var13 var12)) (= var11 var10)) (= var9 var20)) (and (and (and (and (and (and (= var8 (write var22 var9 (O_node (node (|node::next| (getnode (read var22 var9))) var11)))) (= var7 var19)) (= var6 var17)) (= var5 var15)) (= var4 var13)) (= var3 var11)) (= var2 var9))) (and (not (= nullAddr var20)) (and (and (and (and (and (and (= var21 (newHeap (alloc var26 (O_node var1)))) (or (and var0 (= var18 (newAddr (alloc var26 (O_node var1))))) (and (not var0) (= var18 var25)))) (= var16 var24)) (= var14 var23)) (= var12 var24)) (= var10 var23)) (= var20 (newAddr (alloc var26 (O_node var1))))))))) (inv_main581_3 var8 var7 var6 var5 var4 var3 var2 var2))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Addr) (var7 Heap)) (or (not (inv_main577_5 var7 var6 var5 var4 var3 var2 var1 var0)) (inv_main577_5 var7 var6 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Int) (var4 Int) (var5 Bool) (var6 Addr) (var7 node) (var8 Heap) (var9 Addr) (var10 Int) (var11 Int) (var12 Addr) (var13 Heap)) (or (not (and (inv_main598_3 var13 var12 var11 var10) (and (and (= nullAddr var9) (and (and (and (and (and (and (= var8 (newHeap (alloc var13 (O_node var7)))) (or (and var5 (= var6 (newAddr (alloc var13 (O_node var7))))) (and (not var5) (= var6 var12)))) (= var4 var11)) (= var3 var10)) (= var2 var11)) (= var1 var10)) (= var9 (newAddr (alloc var13 (O_node var7)))))) (= var0 1)))) (inv_main577_5 var8 var6 var4 var3 var2 var1 var9 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Addr) (var6 Int) (var7 Int) (var8 Int) (var9 Int) (var10 Addr) (var11 Addr) (var12 Heap) (var13 Heap) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Int) (var18 Addr) (var19 Int) (var20 Int) (var21 Addr) (var22 Heap)) (or (not (and (inv_main600_3 var22 var21 var20 var19 var18 var17 var16) (and (and (= var15 var14) (and (and (and (and (and (and (and (and (and (= var13 var12) (= var11 var10)) (= var9 var8)) (= var7 var6)) (= var14 var5)) (= var4 var3)) (= var2 var1)) (= var15 (|node::next| (getnode (read var12 var1))))) (= var19 (|node::data| (getnode (read var22 var16))))) (and (and (and (and (and (and (= var12 (write var22 var16 (O_node (node (|node::next| (getnode (read var22 var16))) var17)))) (= var10 var21)) (= var8 var20)) (= var6 var19)) (= var5 var18)) (= var3 var17)) (= var1 var16)))) (= var0 (+ (+ var4 1) (* (- 1) var9)))))) (inv_main_20 var13 var11 var9 var7 var14 var0 var15))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Addr) (var4 Int) (var5 Int) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Int) (var11 Addr) (var12 Int) (var13 Int) (var14 Addr) (var15 Heap) (var16 Addr) (var17 Addr) (var18 Int) (var19 Addr) (var20 Int) (var21 Int) (var22 Addr) (var23 Heap)) (or (not (and (inv_main_20 var23 var22 var21 var20 var19 var18 var17) (and (and (not (= var16 nullAddr)) (and (and (and (and (and (and (and (and (and (= var15 var23) (= var14 var22)) (= var13 var21)) (= var12 var20)) (= var11 var19)) (= var10 var18)) (= var9 var17)) (= var8 (|node::next| (getnode (read var23 var17))))) (and (and (and (and (and (and (and (= var7 (write var15 var9 defObj)) (or (and (= var14 var9) (= var6 nullAddr)) (and (not (= var14 var9)) (= var6 var14)))) (= var5 var13)) (= var4 var12)) (= var3 var11)) (= var2 var10)) (= var1 var9)) (= var16 var8))) (= var18 (|node::data| (getnode (read var23 var17)))))) (= var0 (+ var2 1))))) (inv_main_20 var7 var6 var5 var4 var3 var0 var16))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Addr) (var6 Int) (var7 Int) (var8 Int) (var9 Int) (var10 Addr) (var11 Addr) (var12 Heap) (var13 Heap) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Int) (var18 Addr) (var19 Int) (var20 Int) (var21 Addr) (var22 Heap)) (or (not (and (inv_main600_3 var22 var21 var20 var19 var18 var17 var16) (and (and (not (= var15 var14)) (and (and (and (and (and (and (and (and (and (= var13 var12) (= var11 var10)) (= var9 var8)) (= var7 var6)) (= var14 var5)) (= var4 var3)) (= var2 var1)) (= var15 (|node::next| (getnode (read var12 var1))))) (= var19 (|node::data| (getnode (read var22 var16))))) (and (and (and (and (and (and (= var12 (write var22 var16 (O_node (node (|node::next| (getnode (read var22 var16))) var17)))) (= var10 var21)) (= var8 var20)) (= var6 var19)) (= var5 var18)) (= var3 var17)) (= var1 var16)))) (= var0 (+ var4 1))))) (inv_main600_3 var13 var11 var9 var7 var14 var0 var15))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Addr) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Int) (var12 Int) (var13 Int) (var14 Int) (var15 Addr) (var16 Heap)) (or (not (and (inv_main581_3 var16 var15 var14 var13 var12 var11 var10 var9) (and (and (not (<= 0 (+ (+ var12 (- 1)) (- 1)))) (and (and (and (and (and (and (and (= var8 (write var16 var10 (O_node (node var9 (|node::data| (getnode (read var16 var10))))))) (= var7 var15)) (= var6 var14)) (= var5 var13)) (= var4 var12)) (= var3 var11)) (= var2 var10)) (= var1 var9))) (= var0 1)))) (inv_main600_3 var8 var7 var6 var5 var1 var0 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Addr) (var4 Int) (var5 Int) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Int) (var11 Addr) (var12 Int) (var13 Int) (var14 Addr) (var15 Heap) (var16 Addr) (var17 Addr) (var18 Int) (var19 Addr) (var20 Int) (var21 Int) (var22 Addr) (var23 Heap)) (or (not (and (inv_main_20 var23 var22 var21 var20 var19 var18 var17) (and (and (= var16 nullAddr) (and (and (and (and (and (and (and (and (and (= var15 var23) (= var14 var22)) (= var13 var21)) (= var12 var20)) (= var11 var19)) (= var10 var18)) (= var9 var17)) (= var8 (|node::next| (getnode (read var23 var17))))) (and (and (and (and (and (and (and (= var7 (write var15 var9 defObj)) (or (and (= var14 var9) (= var6 nullAddr)) (and (not (= var14 var9)) (= var6 var14)))) (= var5 var13)) (= var4 var12)) (= var3 var11)) (= var2 var10)) (= var1 var9)) (= var16 var8))) (= var18 (|node::data| (getnode (read var23 var17)))))) (= var0 0)))) (inv_main621_10 var7 var6 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Int) (var4 Int) (var5 Addr) (var6 Heap)) (or (not (and (inv_main600_3 var6 var5 var4 var3 var2 var1 var0) (not (= var3 (|node::data| (getnode (read var6 var0))))))) (inv_exit var6 var5))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Int) (var4 Int) (var5 Addr) (var6 Heap)) (or (not (and (inv_main_20 var6 var5 var4 var3 var2 var1 var0) (not (= var1 (|node::data| (getnode (read var6 var0))))))) (inv_exit var6 var5))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Int) (var6 Int) (var7 Int) (var8 Addr) (var9 Heap)) (or (not (inv_main585_7 var9 var8 var7 var6 var5 var4 var3 var2 var1 var0)) (inv_main585_7 var9 var8 var7 var6 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Bool) (var8 Addr) (var9 node) (var10 Heap) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Int) (var15 Int) (var16 Int) (var17 Int) (var18 Addr) (var19 Heap)) (or (not (and (inv_main581_3 var19 var18 var17 var16 var15 var14 var13 var12) (and (and (and (= nullAddr var11) (and (and (and (and (and (and (and (and (= var10 (newHeap (alloc var19 (O_node var9)))) (or (and var7 (= var8 (newAddr (alloc var19 (O_node var9))))) (and (not var7) (= var8 var18)))) (= var6 var17)) (= var5 var16)) (= var4 var15)) (= var3 var14)) (= var2 var13)) (= var1 var12)) (= var11 (newAddr (alloc var19 (O_node var9)))))) (<= 0 (+ (+ var15 (- 1)) (- 1)))) (= var0 1)))) (inv_main585_7 var10 var8 var6 var5 var4 var3 var2 var1 var11 var0))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_exit var1 var0) (not (= var0 nullAddr))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap)) (not (and (inv_main621_10 var2 var1 var0) (not (= var1 nullAddr))))))
(check-sat)
