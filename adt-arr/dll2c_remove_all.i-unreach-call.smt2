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
                   ((node (|node::next| Addr) (|node::prev| Addr) (|node::data| Int)))))
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
(declare-fun inv_main578_5 (Heap Int Int Int Int Int Addr Int) Bool)
(declare-fun inv_main578_5_12 (Heap Int Int Int Int Addr Addr Int Addr Int) Bool)
(declare-fun inv_main587_3 (Heap Int Int Int Int Addr Addr) Bool)
(declare-fun inv_main617_3 (Heap Int Int) Bool)
(declare-fun inv_main618_3 (Heap Int Int Addr Int) Bool)
(declare-fun inv_main_34 (Heap Int Int Addr Int) Bool)
(assert (forall ((var0 Int) (var1 Int) (var2 Heap)) (or (not (and (and (= var2 emptyHeap) (= var1 2)) (= var0 1))) (inv_main617_3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Addr) (var6 Int) (var7 Int) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Int) (var12 Int) (var13 Addr) (var14 Int) (var15 Int) (var16 Heap) (var17 Addr) (var18 Addr) (var19 Int) (var20 Int) (var21 Addr) (var22 Int) (var23 Int) (var24 Heap) (var25 Addr) (var26 Addr) (var27 Addr) (var28 Int) (var29 Int) (var30 Int) (var31 Int) (var32 Addr) (var33 Addr) (var34 Int) (var35 Int) (var36 Int) (var37 Int) (var38 Heap) (var39 Heap) (var40 Int) (var41 Addr) (var42 Int) (var43 Int) (var44 Heap)) (or (not (and (inv_main618_3 var44 var43 var42 var41 var40) (and (and (and (and (and (and (and (and (and (and (and (and (and (= var39 var38) (= var37 var36)) (= var35 var34)) (= var33 var32)) (= var31 var30)) (= var29 var28)) (= var27 var26)) (= var25 (|node::prev| (getnode (read var38 var32))))) (and (and (and (and (and (and (and (= var24 (write var39 var27 (O_node (node (|node::next| (getnode (read var39 var27))) var25 (|node::data| (getnode (read var39 var27))))))) (= var23 var37)) (= var22 var35)) (= var21 var33)) (= var20 var31)) (= var19 var29)) (= var18 var27)) (= var17 var25))) (and (and (and (and (and (and (and (= var16 (write var24 var17 (O_node (node var18 (|node::prev| (getnode (read var24 var17))) (|node::data| (getnode (read var24 var17))))))) (= var15 var23)) (= var14 var22)) (= var13 var21)) (= var12 var20)) (= var11 var19)) (= var10 var18)) (= var9 var17))) (and (and (and (and (and (and (and (= var8 (write var16 var13 defObj)) (= var7 var15)) (= var6 var14)) (= var5 var13)) (= var4 var12)) (= var3 var11)) (= var2 var10)) (= var1 var9))) (and (not (= var26 var32)) (and (and (and (and (and (and (= var38 var44) (= var36 var43)) (= var34 var42)) (= var32 var41)) (= var30 var40)) (= var28 3)) (= var26 (|node::next| (getnode (read var44 var41))))))) (<= 0 (+ (+ var43 (* (- 1) var40)) (- 1)))) (= var0 (+ var4 1))))) (inv_main618_3 var8 var7 var6 var2 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Int) (var5 Int) (var6 Heap) (var7 Addr) (var8 Int) (var9 Int) (var10 Addr) (var11 Int) (var12 Int) (var13 Heap) (var14 Int) (var15 Int) (var16 Int) (var17 Int) (var18 Heap) (var19 Addr) (var20 Addr) (var21 Int) (var22 Addr) (var23 Int) (var24 Int) (var25 Heap)) (or (not (and (inv_main618_3 var25 var24 var23 var22 var21) (and (and (and (and (and (= var20 var19) (and (and (and (and (and (and (= var18 var25) (= var17 var24)) (= var16 var23)) (= var19 var22)) (= var15 var21)) (= var14 3)) (= var20 (|node::next| (getnode (read var25 var22)))))) (and (and (and (and (and (and (= var13 (write var18 var19 defObj)) (= var12 var17)) (= var11 var16)) (= var10 var19)) (= var9 var15)) (= var8 var14)) (= var7 var20))) (and (and (and (and (and (= var6 var13) (= var5 var12)) (= var4 var11)) (= var3 nullAddr)) (= var2 var9)) (= var1 var8))) (<= 0 (+ (+ var24 (* (- 1) var21)) (- 1)))) (= var0 (+ var2 1))))) (inv_main618_3 var6 var5 var4 var3 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Int) (var11 Int) (var12 Int) (var13 Int) (var14 Heap) (var15 Addr) (var16 Addr) (var17 Int) (var18 Int) (var19 Int) (var20 Int) (var21 Heap)) (or (not (and (inv_main587_3 var21 var20 var19 var18 var17 var16 var15) (and (and (and (not (<= 0 (+ (+ var18 (- 1)) (- 1)))) (and (and (and (and (and (and (= var14 (write var21 var15 (O_node (node var16 (|node::prev| (getnode (read var21 var15))) (|node::data| (getnode (read var21 var15))))))) (= var13 var20)) (= var12 var19)) (= var11 var18)) (= var10 var17)) (= var9 var16)) (= var8 var15))) (and (and (and (and (and (and (= var7 (write var14 var9 (O_node (node (|node::next| (getnode (read var14 var9))) var8 (|node::data| (getnode (read var14 var9))))))) (= var6 var13)) (= var5 var12)) (= var4 var11)) (= var3 var10)) (= var2 var9)) (= var1 var8))) (= var0 0)))) (inv_main618_3 var7 var6 var5 var2 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Heap)) (or (not (inv_main578_5 var7 var6 var5 var4 var3 var2 var1 var0)) (inv_main578_5 var7 var6 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 node) (var7 Heap) (var8 Addr) (var9 Int) (var10 Int) (var11 Heap)) (or (not (and (inv_main617_3 var11 var10 var9) (and (and (= nullAddr var8) (and (and (and (and (and (and (= var7 (newHeap (alloc var11 (O_node var6)))) (= var5 var10)) (= var4 var9)) (= var3 var10)) (= var2 var9)) (= var1 var9)) (= var8 (newAddr (alloc var11 (O_node var6)))))) (= var0 1)))) (inv_main578_5 var7 var5 var4 var3 var2 var1 var8 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Int) (var6 Int) (var7 Int) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Int) (var12 Int) (var13 Int) (var14 Int) (var15 Heap) (var16 node) (var17 Addr) (var18 Int) (var19 Addr) (var20 Addr) (var21 Int) (var22 Int) (var23 Int) (var24 Int) (var25 Heap) (var26 Addr) (var27 Int) (var28 Addr) (var29 Addr) (var30 Int) (var31 Int) (var32 Int) (var33 Int) (var34 Heap) (var35 Addr) (var36 Int) (var37 Int) (var38 Addr) (var39 Addr) (var40 Addr) (var41 Addr) (var42 Int) (var43 Int) (var44 Int) (var45 Int) (var46 Int) (var47 Int) (var48 Int) (var49 Int) (var50 Addr) (var51 Heap) (var52 Heap) (var53 Addr) (var54 Addr) (var55 Addr) (var56 Int) (var57 Int) (var58 Int) (var59 Int) (var60 Heap)) (or (not (and (inv_main587_3 var60 var59 var58 var57 var56 var55 var54) (and (and (and (and (and (not (= var53 nullAddr)) (and (and (and (and (and (and (and (and (and (and (and (= var52 (write var51 var50 (O_node (node nullAddr (|node::prev| (getnode (read var51 var50))) (|node::data| (getnode (read var51 var50))))))) (= var49 var48)) (= var47 var46)) (= var45 var44)) (= var43 var42)) (= var41 var40)) (= var39 var38)) (= var37 var36)) (= var35 var50)) (and (and (and (and (and (and (and (and (= var34 (write var52 var35 (O_node (node (|node::next| (getnode (read var52 var35))) nullAddr (|node::data| (getnode (read var52 var35))))))) (= var33 var49)) (= var32 var47)) (= var31 var45)) (= var30 var43)) (= var29 var41)) (= var28 var39)) (= var27 var37)) (= var26 var35))) (and (and (and (and (and (and (and (and (= var25 (write var34 var26 (O_node (node (|node::next| (getnode (read var34 var26))) (|node::prev| (getnode (read var34 var26))) var27)))) (= var24 var33)) (= var23 var32)) (= var22 var31)) (= var21 var30)) (= var20 var29)) (= var19 var28)) (= var18 var27)) (= var17 var26))) (and (not (= nullAddr var50)) (and (and (and (and (and (and (and (and (= var51 (newHeap (alloc var60 (O_node var16)))) (= var48 var59)) (= var46 var58)) (= var44 var57)) (= var42 var56)) (= var40 var55)) (= var38 var54)) (= var36 var56)) (= var50 (newAddr (alloc var60 (O_node var16)))))))) (and (and (and (and (and (and (and (= var15 (write var25 var17 (O_node (node var20 (|node::prev| (getnode (read var25 var17))) (|node::data| (getnode (read var25 var17))))))) (= var14 var24)) (= var13 var23)) (= var12 var22)) (= var11 var21)) (= var53 var20)) (= var10 var19)) (= var9 var17))) (and (and (and (and (and (and (and (= var8 (write var15 var53 (O_node (node (|node::next| (getnode (read var15 var53))) var9 (|node::data| (getnode (read var15 var53))))))) (= var7 var14)) (= var6 var13)) (= var5 var12)) (= var4 var11)) (= var3 var53)) (= var2 var10)) (= var1 var9))) (<= 0 (+ (+ var57 (- 1)) (- 1)))) (= var0 (+ var5 (- 1)))))) (inv_main587_3 var8 var7 var6 var0 var4 var1 var2))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Heap) (var8 node) (var9 Addr) (var10 Int) (var11 Addr) (var12 Addr) (var13 Int) (var14 Int) (var15 Int) (var16 Int) (var17 Heap) (var18 Addr) (var19 Int) (var20 Addr) (var21 Addr) (var22 Int) (var23 Int) (var24 Int) (var25 Int) (var26 Heap) (var27 Addr) (var28 Int) (var29 Int) (var30 Addr) (var31 Addr) (var32 Addr) (var33 Addr) (var34 Int) (var35 Int) (var36 Int) (var37 Int) (var38 Int) (var39 Int) (var40 Int) (var41 Int) (var42 Addr) (var43 Heap) (var44 Heap) (var45 Addr) (var46 Addr) (var47 Addr) (var48 Int) (var49 Int) (var50 Int) (var51 Int) (var52 Heap)) (or (not (and (inv_main587_3 var52 var51 var50 var49 var48 var47 var46) (and (and (and (and (= var45 nullAddr) (and (and (and (and (and (and (and (and (and (and (and (= var44 (write var43 var42 (O_node (node nullAddr (|node::prev| (getnode (read var43 var42))) (|node::data| (getnode (read var43 var42))))))) (= var41 var40)) (= var39 var38)) (= var37 var36)) (= var35 var34)) (= var33 var32)) (= var31 var30)) (= var29 var28)) (= var27 var42)) (and (and (and (and (and (and (and (and (= var26 (write var44 var27 (O_node (node (|node::next| (getnode (read var44 var27))) nullAddr (|node::data| (getnode (read var44 var27))))))) (= var25 var41)) (= var24 var39)) (= var23 var37)) (= var22 var35)) (= var21 var33)) (= var20 var31)) (= var19 var29)) (= var18 var27))) (and (and (and (and (and (and (and (and (= var17 (write var26 var18 (O_node (node (|node::next| (getnode (read var26 var18))) (|node::prev| (getnode (read var26 var18))) var19)))) (= var16 var25)) (= var15 var24)) (= var14 var23)) (= var13 var22)) (= var12 var21)) (= var11 var20)) (= var10 var19)) (= var9 var18))) (and (not (= nullAddr var42)) (and (and (and (and (and (and (and (and (= var43 (newHeap (alloc var52 (O_node var8)))) (= var40 var51)) (= var38 var50)) (= var36 var49)) (= var34 var48)) (= var32 var47)) (= var30 var46)) (= var28 var48)) (= var42 (newAddr (alloc var52 (O_node var8)))))))) (and (and (and (and (and (and (and (= var7 (write var17 var9 (O_node (node var12 (|node::prev| (getnode (read var17 var9))) (|node::data| (getnode (read var17 var9))))))) (= var6 var16)) (= var5 var15)) (= var4 var14)) (= var3 var13)) (= var45 var12)) (= var2 var11)) (= var1 var9))) (<= 0 (+ (+ var49 (- 1)) (- 1)))) (= var0 (+ var4 (- 1)))))) (inv_main587_3 var7 var6 var5 var0 var3 var1 var2))))
(assert (forall ((var0 node) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Heap) (var8 Addr) (var9 Int) (var10 Int) (var11 Int) (var12 Int) (var13 Int) (var14 Heap) (var15 Addr) (var16 Int) (var17 Int) (var18 Int) (var19 Int) (var20 Int) (var21 Int) (var22 Int) (var23 Int) (var24 Int) (var25 Int) (var26 Addr) (var27 Heap) (var28 Heap) (var29 Int) (var30 Int) (var31 Heap)) (or (not (and (inv_main617_3 var31 var30 var29) (and (and (and (and (and (and (and (and (and (= var28 (write var27 var26 (O_node (node nullAddr (|node::prev| (getnode (read var27 var26))) (|node::data| (getnode (read var27 var26))))))) (= var25 var24)) (= var23 var22)) (= var21 var20)) (= var19 var18)) (= var17 var16)) (= var15 var26)) (and (and (and (and (and (and (= var14 (write var28 var15 (O_node (node (|node::next| (getnode (read var28 var15))) nullAddr (|node::data| (getnode (read var28 var15))))))) (= var13 var25)) (= var12 var23)) (= var11 var21)) (= var10 var19)) (= var9 var17)) (= var8 var15))) (and (and (and (and (and (and (= var7 (write var14 var8 (O_node (node (|node::next| (getnode (read var14 var8))) (|node::prev| (getnode (read var14 var8))) var9)))) (= var6 var13)) (= var5 var12)) (= var4 var11)) (= var3 var10)) (= var2 var9)) (= var1 var8))) (and (not (= nullAddr var26)) (and (and (and (and (and (and (= var27 (newHeap (alloc var31 (O_node var0)))) (= var24 var30)) (= var22 var29)) (= var20 var30)) (= var18 var29)) (= var16 var29)) (= var26 (newAddr (alloc var31 (O_node var0))))))))) (inv_main587_3 var7 var6 var5 var4 var3 var1 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Heap)) (or (not (and (inv_main618_3 var4 var3 var2 var1 var0) (and (not (= nullAddr var1)) (not (<= 0 (+ (+ var3 (* (- 1) var0)) (- 1))))))) (inv_main_34 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Int) (var6 Int) (var7 Int) (var8 Int) (var9 Heap)) (or (not (inv_main578_5_12 var9 var8 var7 var6 var5 var4 var3 var2 var1 var0)) (inv_main578_5_12 var9 var8 var7 var6 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Int) (var5 Int) (var6 Int) (var7 Int) (var8 node) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Int) (var14 Int) (var15 Int) (var16 Int) (var17 Heap)) (or (not (and (inv_main587_3 var17 var16 var15 var14 var13 var12 var11) (and (and (and (= nullAddr var10) (and (and (and (and (and (and (and (and (= var9 (newHeap (alloc var17 (O_node var8)))) (= var7 var16)) (= var6 var15)) (= var5 var14)) (= var4 var13)) (= var3 var12)) (= var2 var11)) (= var1 var13)) (= var10 (newAddr (alloc var17 (O_node var8)))))) (<= 0 (+ (+ var14 (- 1)) (- 1)))) (= var0 1)))) (inv_main578_5_12 var9 var7 var6 var5 var4 var3 var2 var1 var10 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Heap)) (not (inv_main_34 var4 var3 var2 var1 var0))))
(check-sat)
