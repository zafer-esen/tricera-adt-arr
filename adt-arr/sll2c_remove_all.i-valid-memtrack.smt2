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
(declare-fun inv_main577_5 (Heap Addr Int Int Int Int Int Addr Int) Bool)
(declare-fun inv_main577_5_11 (Heap Addr Int Int Int Int Addr Addr Int Addr Int) Bool)
(declare-fun inv_main585_3 (Heap Addr Int Int Int Int Addr Addr) Bool)
(declare-fun inv_main601_5 (Heap Addr Int Int Addr Int Int Addr Addr) Bool)
(declare-fun inv_main613_3 (Heap Addr Int Int) Bool)
(declare-fun inv_main614_3 (Heap Addr Int Int Addr Int) Bool)
(declare-fun inv_main624_10 (Heap Addr Int) Bool)
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Heap)) (or (not (and (and (and (= var3 emptyHeap) (= var2 nullAddr)) (= var1 2)) (= var0 1))) (inv_main613_3 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Int) (var7 Int) (var8 Int) (var9 Int) (var10 Addr) (var11 Addr) (var12 Int) (var13 Int) (var14 Int) (var15 Int) (var16 Addr) (var17 Addr) (var18 Heap) (var19 Heap) (var20 Addr) (var21 Addr) (var22 Int) (var23 Int) (var24 Addr) (var25 Int) (var26 Int) (var27 Addr) (var28 Heap)) (or (not (and (inv_main601_5 var28 var27 var26 var25 var24 var23 var22 var21 var20) (and (and (and (and (and (and (and (and (and (and (= var19 var18) (= var17 var16)) (= var15 var14)) (= var13 var12)) (= var11 var10)) (= var9 var8)) (= var7 var6)) (= var5 var4)) (= var3 var2)) (= var1 (|node::next| (getnode (read var18 var2))))) (and (not (= var0 var10)) (and (and (and (and (and (and (and (and (and (= var18 var28) (= var16 var27)) (= var14 var26)) (= var12 var25)) (= var10 var24)) (= var8 var23)) (= var6 var22)) (= var4 var21)) (= var2 var20)) (= var0 (|node::next| (getnode (read var28 var20))))))))) (inv_main601_5 var19 var17 var15 var13 var11 var9 var7 var5 var1))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Int) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Int) (var9 Addr) (var10 Int) (var11 Int) (var12 Addr) (var13 Heap)) (or (not (and (inv_main614_3 var13 var12 var11 var10 var9 var8) (and (and (not (= var7 var6)) (and (and (and (and (and (and (and (= var5 var13) (= var4 var12)) (= var3 var11)) (= var2 var10)) (= var6 var9)) (= var1 var8)) (= var0 4)) (= var7 (|node::next| (getnode (read var13 var9)))))) (<= 0 (+ (+ var11 (* (- 1) var8)) (- 1)))))) (inv_main601_5 var5 var4 var3 var2 var6 var1 var0 var7 var6))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Addr) (var5 Heap)) (or (not (and (inv_main614_3 var5 var4 var3 var2 var1 var0) (and (not (= nullAddr var1)) (not (<= 0 (+ (+ var3 (* (- 1) var0)) (- 1))))))) (inv_exit var5 var4))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Int) (var4 Int) (var5 Addr) (var6 Heap)) (or (not (and (inv_main614_3 var6 var5 var4 var3 var2 var1) (and (and (= nullAddr var2) (not (<= 0 (+ (+ var4 (* (- 1) var1)) (- 1))))) (= var0 0)))) (inv_main624_10 var6 var5 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Int) (var6 Int) (var7 Int) (var8 Addr) (var9 Heap) (var10 Bool) (var11 node) (var12 Addr) (var13 Int) (var14 Addr) (var15 Addr) (var16 Int) (var17 Int) (var18 Int) (var19 Int) (var20 Addr) (var21 Heap) (var22 Addr) (var23 Int) (var24 Int) (var25 Addr) (var26 Addr) (var27 Addr) (var28 Addr) (var29 Int) (var30 Int) (var31 Int) (var32 Int) (var33 Int) (var34 Int) (var35 Int) (var36 Int) (var37 Addr) (var38 Addr) (var39 Addr) (var40 Heap) (var41 Heap) (var42 Addr) (var43 Addr) (var44 Int) (var45 Int) (var46 Int) (var47 Int) (var48 Addr) (var49 Heap)) (or (not (and (inv_main585_3 var49 var48 var47 var46 var45 var44 var43 var42) (and (and (and (and (and (and (and (and (and (and (and (and (and (and (= var41 (write var40 var39 (O_node (node nullAddr (|node::data| (getnode (read var40 var39))))))) (= var38 var37)) (= var36 var35)) (= var34 var33)) (= var32 var31)) (= var30 var29)) (= var28 var27)) (= var26 var25)) (= var24 var23)) (= var22 var39)) (and (and (and (and (and (and (and (and (and (= var21 (write var41 var22 (O_node (node (|node::next| (getnode (read var41 var22))) var24)))) (= var20 var38)) (= var19 var36)) (= var18 var34)) (= var17 var32)) (= var16 var30)) (= var15 var28)) (= var14 var26)) (= var13 var24)) (= var12 var22))) (and (not (= nullAddr var39)) (and (and (and (and (and (and (and (and (and (= var40 (newHeap (alloc var49 (O_node var11)))) (or (and var10 (= var37 (newAddr (alloc var49 (O_node var11))))) (and (not var10) (= var37 var48)))) (= var35 var47)) (= var33 var46)) (= var31 var45)) (= var29 var44)) (= var27 var43)) (= var25 var42)) (= var23 var44)) (= var39 (newAddr (alloc var49 (O_node var11))))))) (and (and (and (and (and (and (and (and (= var9 (write var21 var12 (O_node (node var15 (|node::data| (getnode (read var21 var12))))))) (= var8 var20)) (= var7 var19)) (= var6 var18)) (= var5 var17)) (= var4 var16)) (= var3 var15)) (= var2 var14)) (= var1 var12))) (<= 0 (+ (+ var45 (- 1)) (- 1)))) (= var0 (+ var5 (- 1)))))) (inv_main585_3 var9 var8 var7 var6 var0 var4 var1 var2))))
(assert (forall ((var0 Bool) (var1 node) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Int) (var8 Addr) (var9 Heap) (var10 Addr) (var11 Int) (var12 Int) (var13 Int) (var14 Int) (var15 Int) (var16 Int) (var17 Int) (var18 Int) (var19 Int) (var20 Int) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Heap) (var25 Heap) (var26 Int) (var27 Int) (var28 Addr) (var29 Heap)) (or (not (and (inv_main613_3 var29 var28 var27 var26) (and (and (and (and (and (and (and (and (and (= var25 (write var24 var23 (O_node (node nullAddr (|node::data| (getnode (read var24 var23))))))) (= var22 var21)) (= var20 var19)) (= var18 var17)) (= var16 var15)) (= var14 var13)) (= var12 var11)) (= var10 var23)) (and (and (and (and (and (and (and (= var9 (write var25 var10 (O_node (node (|node::next| (getnode (read var25 var10))) var12)))) (= var8 var22)) (= var7 var20)) (= var6 var18)) (= var5 var16)) (= var4 var14)) (= var3 var12)) (= var2 var10))) (and (not (= nullAddr var23)) (and (and (and (and (and (and (and (= var24 (newHeap (alloc var29 (O_node var1)))) (or (and var0 (= var21 (newAddr (alloc var29 (O_node var1))))) (and (not var0) (= var21 var28)))) (= var19 var27)) (= var17 var26)) (= var15 var27)) (= var13 var26)) (= var11 var26)) (= var23 (newAddr (alloc var29 (O_node var1))))))))) (inv_main585_3 var9 var8 var7 var6 var5 var4 var2 var2))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Addr) (var8 Heap)) (or (not (inv_main577_5 var8 var7 var6 var5 var4 var3 var2 var1 var0)) (inv_main577_5 var8 var7 var6 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Bool) (var7 Addr) (var8 node) (var9 Heap) (var10 Addr) (var11 Int) (var12 Int) (var13 Addr) (var14 Heap)) (or (not (and (inv_main613_3 var14 var13 var12 var11) (and (and (= nullAddr var10) (and (and (and (and (and (and (and (= var9 (newHeap (alloc var14 (O_node var8)))) (or (and var6 (= var7 (newAddr (alloc var14 (O_node var8))))) (and (not var6) (= var7 var13)))) (= var5 var12)) (= var4 var11)) (= var3 var12)) (= var2 var11)) (= var1 var11)) (= var10 (newAddr (alloc var14 (O_node var8)))))) (= var0 1)))) (inv_main577_5 var9 var7 var5 var4 var3 var2 var1 var10 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Addr) (var6 Int) (var7 Int) (var8 Addr) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Int) (var13 Int) (var14 Addr) (var15 Int) (var16 Int) (var17 Addr) (var18 Heap) (var19 Addr) (var20 Addr) (var21 Int) (var22 Int) (var23 Int) (var24 Int) (var25 Addr) (var26 Heap) (var27 Addr) (var28 Addr) (var29 Addr) (var30 Addr) (var31 Int) (var32 Int) (var33 Addr) (var34 Int) (var35 Int) (var36 Addr) (var37 Heap)) (or (not (and (inv_main601_5 var37 var36 var35 var34 var33 var32 var31 var30 var29) (and (and (and (and (= var28 var27) (and (and (and (and (and (and (and (and (and (= var26 var37) (= var25 var36)) (= var24 var35)) (= var23 var34)) (= var27 var33)) (= var22 var32)) (= var21 var31)) (= var20 var30)) (= var19 var29)) (= var28 (|node::next| (getnode (read var37 var29)))))) (and (and (and (and (and (and (and (and (= var18 (write var26 var19 (O_node (node var20 (|node::data| (getnode (read var26 var19))))))) (= var17 var25)) (= var16 var24)) (= var15 var23)) (= var14 var27)) (= var13 var22)) (= var12 var21)) (= var11 var20)) (= var10 var19))) (and (and (and (and (and (and (and (and (= var9 (write var18 var14 defObj)) (or (and (= var17 var14) (= var8 nullAddr)) (and (not (= var17 var14)) (= var8 var17)))) (= var7 var16)) (= var6 var15)) (= var5 var14)) (= var4 var13)) (= var3 var12)) (= var2 var11)) (= var1 var10))) (= var0 (+ var4 1))))) (inv_main614_3 var9 var8 var7 var6 var2 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Int) (var5 Int) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Int) (var10 Int) (var11 Addr) (var12 Int) (var13 Int) (var14 Addr) (var15 Heap) (var16 Int) (var17 Int) (var18 Int) (var19 Int) (var20 Addr) (var21 Heap) (var22 Addr) (var23 Addr) (var24 Int) (var25 Addr) (var26 Int) (var27 Int) (var28 Addr) (var29 Heap)) (or (not (and (inv_main614_3 var29 var28 var27 var26 var25 var24) (and (and (and (and (and (= var23 var22) (and (and (and (and (and (and (and (= var21 var29) (= var20 var28)) (= var19 var27)) (= var18 var26)) (= var22 var25)) (= var17 var24)) (= var16 4)) (= var23 (|node::next| (getnode (read var29 var25)))))) (and (and (and (and (and (and (and (= var15 (write var21 var22 defObj)) (or (and (= var20 var22) (= var14 nullAddr)) (and (not (= var20 var22)) (= var14 var20)))) (= var13 var19)) (= var12 var18)) (= var11 var22)) (= var10 var17)) (= var9 var16)) (= var8 var23))) (and (and (and (and (and (and (= var7 var15) (= var6 var14)) (= var5 var13)) (= var4 var12)) (= var3 nullAddr)) (= var2 var10)) (= var1 var9))) (<= 0 (+ (+ var27 (* (- 1) var24)) (- 1)))) (= var0 (+ var2 1))))) (inv_main614_3 var7 var6 var5 var4 var3 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Addr) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Int) (var12 Int) (var13 Int) (var14 Int) (var15 Addr) (var16 Heap)) (or (not (and (inv_main585_3 var16 var15 var14 var13 var12 var11 var10 var9) (and (and (not (<= 0 (+ (+ var12 (- 1)) (- 1)))) (and (and (and (and (and (and (and (= var8 (write var16 var9 (O_node (node var10 (|node::data| (getnode (read var16 var9))))))) (= var7 var15)) (= var6 var14)) (= var5 var13)) (= var4 var12)) (= var3 var11)) (= var2 var10)) (= var1 var9))) (= var0 0)))) (inv_main614_3 var8 var7 var6 var5 var2 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Int) (var6 Int) (var7 Int) (var8 Int) (var9 Addr) (var10 Heap)) (or (not (inv_main577_5_11 var10 var9 var8 var7 var6 var5 var4 var3 var2 var1 var0)) (inv_main577_5_11 var10 var9 var8 var7 var6 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Int) (var5 Int) (var6 Int) (var7 Int) (var8 Bool) (var9 Addr) (var10 node) (var11 Heap) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Int) (var16 Int) (var17 Int) (var18 Int) (var19 Addr) (var20 Heap)) (or (not (and (inv_main585_3 var20 var19 var18 var17 var16 var15 var14 var13) (and (and (and (= nullAddr var12) (and (and (and (and (and (and (and (and (and (= var11 (newHeap (alloc var20 (O_node var10)))) (or (and var8 (= var9 (newAddr (alloc var20 (O_node var10))))) (and (not var8) (= var9 var19)))) (= var7 var18)) (= var6 var17)) (= var5 var16)) (= var4 var15)) (= var3 var14)) (= var2 var13)) (= var1 var15)) (= var12 (newAddr (alloc var20 (O_node var10)))))) (<= 0 (+ (+ var16 (- 1)) (- 1)))) (= var0 1)))) (inv_main577_5_11 var11 var9 var7 var6 var5 var4 var3 var2 var1 var12 var0))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_exit var1 var0) (not (= var0 nullAddr))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap)) (not (and (inv_main624_10 var2 var1 var0) (not (= var1 nullAddr))))))
(check-sat)
