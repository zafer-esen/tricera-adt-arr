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
(declare-fun inv_main533_3 (Heap Int) Bool)
(declare-fun inv_main534_15 (Heap Int Addr Int) Bool)
(declare-fun inv_main540_3 (Heap Int Addr Addr Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main550_17 (Heap Int Addr Addr Addr Addr Addr Addr Addr Int) Bool)
(declare-fun inv_main_21 (Heap Int Addr Addr Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main_30 (Heap Int Addr Addr Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main_36 (Heap Int Addr Addr Addr Addr Addr Addr Addr) Bool)
(assert (forall ((var0 Int) (var1 Heap)) (or (not (and (= var1 emptyHeap) (= var0 1))) (inv_main533_3 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Int) (var8 Heap)) (or (not (and (inv_main_30 var8 var7 var6 var5 var4 var3 var2 var1 var0) (= var0 nullAddr))) (inv_main_36 var8 var7 var6 var5 var4 var3 var2 var1 var3))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Int) (var17 Int) (var18 Heap) (var19 Heap) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Addr) (var25 Addr) (var26 Addr) (var27 Int) (var28 Heap)) (or (not (and (inv_main_36 var28 var27 var26 var25 var24 var23 var22 var21 var20) (and (and (and (and (and (and (and (and (and (and (= var19 var18) (= var17 var16)) (= var15 var14)) (= var13 var12)) (= var11 var10)) (= var9 var8)) (= var7 var6)) (= var5 var4)) (= var3 var2)) (= var1 (|node::n| (getnode (read var18 var2))))) (and (and (= var0 2) (and (and (and (and (and (and (and (and (and (= var18 var28) (= var16 var27)) (= var14 var26)) (= var12 var25)) (= var10 var24)) (= var8 var23)) (= var6 var22)) (= var4 var21)) (= var2 var20)) (= var0 (|node::h| (getnode (read var28 var20)))))) (not (= var20 nullAddr)))))) (inv_main_36 var19 var17 var15 var13 var11 var9 var7 var5 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Heap)) (or (not (inv_main534_15 var3 var2 var1 var0)) (inv_main534_15 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 node) (var3 Heap) (var4 Addr) (var5 Int) (var6 Heap)) (or (not (and (inv_main533_3 var6 var5) (and (and (= var4 nullAddr) (and (and (= var3 (newHeap (alloc var6 (O_node var2)))) (= var1 var5)) (= var4 (newAddr (alloc var6 (O_node var2)))))) (= var0 1)))) (inv_main534_15 var3 var1 var4 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 node) (var11 Heap) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Int) (var18 Addr) (var19 Addr) (var20 Heap) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Addr) (var25 Addr) (var26 Addr) (var27 Addr) (var28 Addr) (var29 Addr) (var30 Addr) (var31 Addr) (var32 Addr) (var33 Addr) (var34 Addr) (var35 Addr) (var36 Int) (var37 Int) (var38 Heap) (var39 Heap) (var40 Addr) (var41 Addr) (var42 Addr) (var43 Addr) (var44 Addr) (var45 Addr) (var46 Addr) (var47 Int) (var48 Heap)) (or (not (and (inv_main540_3 var48 var47 var46 var45 var44 var43 var42 var41 var40) (and (and (and (and (and (and (and (and (and (and (and (= var39 var38) (= var37 var36)) (= var35 var34)) (= var33 var32)) (= var31 var30)) (= var29 var28)) (= var27 var26)) (= var25 var24)) (= var23 var22)) (= var21 (|node::n| (getnode (read var38 var22))))) (and (and (and (and (and (and (and (and (= var38 (write var20 var19 (O_node (node (|node::h| (getnode (read var20 var19))) var18)))) (= var36 var17)) (= var34 var16)) (= var32 var18)) (= var30 var15)) (= var28 var14)) (= var26 var13)) (= var24 var12)) (= var22 var19))) (and (and (not (= var18 nullAddr)) (and (and (and (and (and (and (and (and (and (= var20 (newHeap (alloc var11 (O_node var10)))) (= var17 0)) (= var16 var9)) (= var8 var7)) (= var15 var6)) (= var14 var5)) (= var13 var4)) (= var12 var3)) (= var19 var2)) (= var18 (newAddr (alloc var11 (O_node var10)))))) (and (and (not (= var47 0)) (not (= var1 0))) (and (and (and (and (and (and (and (and (= var11 (write var48 var40 (O_node (node 1 (|node::n| (getnode (read var48 var40))))))) (= var0 var47)) (= var9 var46)) (= var7 var45)) (= var6 var44)) (= var5 var43)) (= var4 var42)) (= var3 var41)) (= var2 var40))))))) (inv_main540_3 var39 var37 var35 var33 var31 var29 var27 var25 var21))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 node) (var11 Heap) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Int) (var18 Addr) (var19 Addr) (var20 Heap) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Addr) (var25 Addr) (var26 Addr) (var27 Addr) (var28 Addr) (var29 Addr) (var30 Addr) (var31 Addr) (var32 Addr) (var33 Addr) (var34 Addr) (var35 Addr) (var36 Int) (var37 Int) (var38 Heap) (var39 Heap) (var40 Addr) (var41 Addr) (var42 Addr) (var43 Addr) (var44 Addr) (var45 Addr) (var46 Addr) (var47 Int) (var48 Heap)) (or (not (and (inv_main540_3 var48 var47 var46 var45 var44 var43 var42 var41 var40) (and (and (and (and (and (and (and (and (and (and (and (= var39 var38) (= var37 var36)) (= var35 var34)) (= var33 var32)) (= var31 var30)) (= var29 var28)) (= var27 var26)) (= var25 var24)) (= var23 var22)) (= var21 (|node::n| (getnode (read var38 var22))))) (and (and (and (and (and (and (and (and (= var38 (write var20 var19 (O_node (node (|node::h| (getnode (read var20 var19))) var18)))) (= var36 var17)) (= var34 var16)) (= var32 var18)) (= var30 var15)) (= var28 var14)) (= var26 var13)) (= var24 var12)) (= var22 var19))) (and (and (not (= var18 nullAddr)) (and (and (and (and (and (and (and (and (and (= var20 (newHeap (alloc var11 (O_node var10)))) (= var17 1)) (= var16 var9)) (= var8 var7)) (= var15 var6)) (= var14 var5)) (= var13 var4)) (= var12 var3)) (= var19 var2)) (= var18 (newAddr (alloc var11 (O_node var10)))))) (and (and (= var47 0) (not (= var1 0))) (and (and (and (and (and (and (and (and (= var11 (write var48 var40 (O_node (node 2 (|node::n| (getnode (read var48 var40))))))) (= var0 var47)) (= var9 var46)) (= var7 var45)) (= var6 var44)) (= var5 var43)) (= var4 var42)) (= var3 var41)) (= var2 var40))))))) (inv_main540_3 var39 var37 var35 var33 var31 var29 var27 var25 var21))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Int) (var6 node) (var7 Heap) (var8 Addr) (var9 Int) (var10 Heap)) (or (not (and (inv_main533_3 var10 var9) (and (not (= var8 nullAddr)) (and (and (= var7 (newHeap (alloc var10 (O_node var6)))) (= var5 var9)) (= var8 (newAddr (alloc var10 (O_node var6)))))))) (inv_main540_3 var7 var5 var8 var4 var3 var2 var1 var0 var8))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Int) (var8 Heap) (var9 Int) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Int) (var18 Heap)) (or (not (and (inv_main_21 var18 var17 var16 var15 var14 var13 var12 var11 var10) (and (= var9 3) (and (and (and (and (and (and (and (and (and (= var8 var18) (= var7 var17)) (= var6 var16)) (= var5 var15)) (= var4 var14)) (= var3 var13)) (= var2 var12)) (= var1 var11)) (= var0 var10)) (= var9 (|node::h| (getnode (read var18 var10)))))))) (inv_main_30 var8 var7 var6 var5 var4 var3 var2 var1 var4))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Int) (var17 Int) (var18 Heap) (var19 Heap) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Addr) (var25 Addr) (var26 Addr) (var27 Int) (var28 Heap)) (or (not (and (inv_main_30 var28 var27 var26 var25 var24 var23 var22 var21 var20) (and (and (and (and (and (and (and (and (and (and (= var19 var18) (= var17 var16)) (= var15 var14)) (= var13 var12)) (= var11 var10)) (= var9 var8)) (= var7 var6)) (= var5 var4)) (= var3 var2)) (= var1 (|node::n| (getnode (read var18 var2))))) (and (and (= var0 1) (and (and (and (and (and (and (and (and (and (= var18 var28) (= var16 var27)) (= var14 var26)) (= var12 var25)) (= var10 var24)) (= var8 var23)) (= var6 var22)) (= var4 var21)) (= var2 var20)) (= var0 (|node::h| (getnode (read var28 var20)))))) (not (= var20 nullAddr)))))) (inv_main_30 var19 var17 var15 var13 var11 var9 var7 var5 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Int) (var9 Heap)) (or (not (inv_main550_17 var9 var8 var7 var6 var5 var4 var3 var2 var1 var0)) (inv_main550_17 var9 var8 var7 var6 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Int) (var18 node) (var19 Heap) (var20 Heap) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Addr) (var25 Addr) (var26 Addr) (var27 Addr) (var28 Addr) (var29 Int) (var30 Heap)) (or (not (and (inv_main540_3 var30 var29 var28 var27 var26 var25 var24 var23 var22) (and (and (and (= var21 nullAddr) (and (and (and (and (and (and (and (and (and (= var20 (newHeap (alloc var19 (O_node var18)))) (= var17 0)) (= var16 var15)) (= var14 var13)) (= var12 var11)) (= var10 var9)) (= var8 var7)) (= var6 var5)) (= var4 var3)) (= var21 (newAddr (alloc var19 (O_node var18)))))) (and (and (not (= var29 0)) (not (= var2 0))) (and (and (and (and (and (and (and (and (= var19 (write var30 var22 (O_node (node 1 (|node::n| (getnode (read var30 var22))))))) (= var1 var29)) (= var15 var28)) (= var13 var27)) (= var11 var26)) (= var9 var25)) (= var7 var24)) (= var5 var23)) (= var3 var22)))) (= var0 1)))) (inv_main550_17 var20 var17 var16 var21 var12 var10 var8 var6 var4 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Int) (var18 node) (var19 Heap) (var20 Heap) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Addr) (var25 Addr) (var26 Addr) (var27 Addr) (var28 Addr) (var29 Int) (var30 Heap)) (or (not (and (inv_main540_3 var30 var29 var28 var27 var26 var25 var24 var23 var22) (and (and (and (= var21 nullAddr) (and (and (and (and (and (and (and (and (and (= var20 (newHeap (alloc var19 (O_node var18)))) (= var17 1)) (= var16 var15)) (= var14 var13)) (= var12 var11)) (= var10 var9)) (= var8 var7)) (= var6 var5)) (= var4 var3)) (= var21 (newAddr (alloc var19 (O_node var18)))))) (and (and (= var29 0) (not (= var2 0))) (and (and (and (and (and (and (and (and (= var19 (write var30 var22 (O_node (node 2 (|node::n| (getnode (read var30 var22))))))) (= var1 var29)) (= var15 var28)) (= var13 var27)) (= var11 var26)) (= var9 var25)) (= var7 var24)) (= var5 var23)) (= var3 var22)))) (= var0 1)))) (inv_main550_17 var20 var17 var16 var21 var12 var10 var8 var6 var4 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Int) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Int) (var17 Heap) (var18 Int) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Addr) (var25 Addr) (var26 Addr) (var27 Addr) (var28 Addr) (var29 Addr) (var30 Addr) (var31 Addr) (var32 Addr) (var33 Int) (var34 Int) (var35 Heap) (var36 Heap) (var37 Int) (var38 Addr) (var39 Addr) (var40 Addr) (var41 Addr) (var42 Addr) (var43 Addr) (var44 Addr) (var45 Int) (var46 Heap)) (or (not (and (inv_main540_3 var46 var45 var44 var43 var42 var41 var40 var39 var38) (and (and (and (and (and (not (= var37 3)) (and (and (and (and (and (and (and (and (and (= var36 var35) (= var34 var33)) (= var32 var31)) (= var30 var29)) (= var28 var27)) (= var26 var25)) (= var24 var23)) (= var22 var21)) (= var20 var19)) (= var37 (|node::h| (getnode (read var35 var31)))))) (= var18 0)) (and (and (and (and (and (and (and (and (= var35 (write var46 var38 (O_node (node 3 (|node::n| (getnode (read var46 var38))))))) (= var33 var45)) (= var31 var44)) (= var29 var43)) (= var27 var42)) (= var25 var41)) (= var23 var40)) (= var21 var39)) (= var19 var38))) (and (and (and (and (and (and (and (and (= var17 var36) (= var16 1)) (= var15 var32)) (= var14 var30)) (= var13 nullAddr)) (= var12 var26)) (= var11 var24)) (= var10 var22)) (= var9 var20))) (and (and (and (and (and (and (and (and (= var8 var17) (= var7 var16)) (= var6 var15)) (= var5 var14)) (= var4 var13)) (= var3 nullAddr)) (= var2 var11)) (= var1 var10)) (= var0 var9))))) (inv_main_21 var8 var7 var6 var5 var4 var3 var2 var1 var6))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Int) (var9 Heap) (var10 Addr) (var11 Int) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Addr) (var25 Addr) (var26 Int) (var27 Heap) (var28 Heap) (var29 Int) (var30 Addr) (var31 Addr) (var32 Addr) (var33 Addr) (var34 Addr) (var35 Addr) (var36 Addr) (var37 Int) (var38 Heap)) (or (not (and (inv_main_21 var38 var37 var36 var35 var34 var33 var32 var31 var30) (and (and (and (not (= var29 0)) (and (and (and (and (and (and (and (and (and (and (= var28 var27) (= var29 var26)) (= var25 var24)) (= var23 var22)) (= var21 var20)) (= var19 var18)) (= var17 var16)) (= var15 var14)) (= var13 var22)) (= var12 (|node::n| (getnode (read var27 var22))))) (and (not (= var11 3)) (and (and (and (and (and (and (and (and (and (= var27 var38) (= var26 var37)) (= var24 var36)) (= var10 var35)) (= var20 var34)) (= var18 var33)) (= var16 var32)) (= var14 var31)) (= var22 var30)) (= var11 (|node::h| (getnode (read var38 var30)))))))) (and (and (and (and (and (and (and (and (= var9 (write var28 var23 (O_node (node (|node::h| (getnode (read var28 var23))) var21)))) (= var8 var29)) (= var7 var25)) (= var6 var23)) (= var5 var21)) (= var4 var19)) (= var3 var17)) (= var2 var15)) (= var1 var12))) (= var0 0)))) (inv_main_21 var9 var0 var7 var6 var6 var4 var3 var2 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Int) (var9 Heap) (var10 Addr) (var11 Int) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Addr) (var25 Addr) (var26 Int) (var27 Heap) (var28 Heap) (var29 Int) (var30 Addr) (var31 Addr) (var32 Addr) (var33 Addr) (var34 Addr) (var35 Addr) (var36 Addr) (var37 Int) (var38 Heap)) (or (not (and (inv_main_21 var38 var37 var36 var35 var34 var33 var32 var31 var30) (and (and (and (= var29 0) (and (and (and (and (and (and (and (and (and (and (= var28 var27) (= var29 var26)) (= var25 var24)) (= var23 var22)) (= var21 var20)) (= var19 var18)) (= var17 var16)) (= var15 var14)) (= var13 var22)) (= var12 (|node::n| (getnode (read var27 var22))))) (and (not (= var11 3)) (and (and (and (and (and (and (and (and (and (= var27 var38) (= var26 var37)) (= var24 var36)) (= var10 var35)) (= var20 var34)) (= var18 var33)) (= var16 var32)) (= var14 var31)) (= var22 var30)) (= var11 (|node::h| (getnode (read var38 var30)))))))) (and (and (and (and (and (and (and (and (= var9 (write var28 var23 (O_node (node (|node::h| (getnode (read var28 var23))) var19)))) (= var8 var29)) (= var7 var25)) (= var6 var23)) (= var5 var21)) (= var4 var19)) (= var3 var17)) (= var2 var15)) (= var1 var12))) (= var0 1)))) (inv_main_21 var9 var0 var7 var6 var5 var6 var3 var2 var1))))
(check-sat)