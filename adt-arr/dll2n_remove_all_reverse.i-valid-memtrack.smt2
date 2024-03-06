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
                   ((node (|node::data| Int) (|node::next| Addr) (|node::prev| Addr)))))
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
(declare-fun inv_main586_3 (Heap Addr Int Int Int Int Addr) Bool)
(declare-fun inv_main590_7 (Heap Addr Int Int Int Int Addr Addr Int) Bool)
(declare-fun inv_main609_5 (Heap Addr Int Int Addr Int Int Addr Addr) Bool)
(declare-fun inv_main621_3 (Heap Addr Int Int) Bool)
(declare-fun inv_main623_7 (Heap Addr Int Int Addr Int) Bool)
(declare-fun inv_main631_10 (Heap Addr Int) Bool)
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Heap)) (or (not (and (and (and (= var3 emptyHeap) (= var2 nullAddr)) (= var1 2)) (= var0 1))) (inv_main621_3 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Addr) (var6 Int) (var7 Int) (var8 Addr) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Int) (var13 Int) (var14 Addr) (var15 Int) (var16 Int) (var17 Addr) (var18 Heap)) (or (not (and (inv_main609_5 var18 var17 var16 var15 var14 var13 var12 var11 var10) (and (and (and (and (and (and (and (and (and (and (= var9 var18) (= var8 var17)) (= var7 var16)) (= var6 var15)) (= var5 var14)) (= var4 var13)) (= var3 var12)) (= var2 var10)) (= var1 var10)) (= var0 (|node::next| (getnode (read var18 var10))))) (not (= (|node::next| (getnode (read var18 var10))) nullAddr))))) (inv_main609_5 var9 var8 var7 var6 var5 var4 var3 var2 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Addr) (var4 Int) (var5 Int) (var6 Addr) (var7 Heap) (var8 Int) (var9 Addr) (var10 Int) (var11 Int) (var12 Addr) (var13 Heap)) (or (not (and (inv_main623_7 var13 var12 var11 var10 var9 var8) (and (and (and (and (and (and (and (and (and (= var7 var13) (= var6 var12)) (= var5 var11)) (= var4 var10)) (= var3 var9)) (= var2 var8)) (= var1 4)) (= var0 nullAddr)) (not (= nullAddr (|node::next| (getnode (read var13 var9)))))) (<= 0 var8)))) (inv_main609_5 var7 var6 var5 var4 var3 var2 var1 var0 var3))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Int) (var5 Int) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Int) (var11 Int) (var12 Addr) (var13 Int) (var14 Int) (var15 Addr) (var16 Heap) (var17 Addr) (var18 Addr) (var19 Int) (var20 Int) (var21 Addr) (var22 Int) (var23 Int) (var24 Addr) (var25 Heap)) (or (not (and (inv_main609_5 var25 var24 var23 var22 var21 var20 var19 var18 var17) (and (and (and (= (|node::next| (getnode (read var25 var17))) nullAddr) (and (and (and (and (and (and (and (and (= var16 (write var25 var18 (O_node (node (|node::data| (getnode (read var25 var18))) nullAddr (|node::prev| (getnode (read var25 var18))))))) (= var15 var24)) (= var14 var23)) (= var13 var22)) (= var12 var21)) (= var11 var20)) (= var10 var19)) (= var9 var18)) (= var8 var17))) (and (and (and (and (and (and (= var7 (write var16 var8 defObj)) (or (and (= var15 var8) (= var6 nullAddr)) (and (not (= var15 var8)) (= var6 var15)))) (= var5 var14)) (= var4 var13)) (= var3 var12)) (= var2 var11)) (= var1 var10))) (= var0 (+ var2 (- 1)))))) (inv_main623_7 var7 var6 var5 var4 var3 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Int) (var5 Int) (var6 Addr) (var7 Heap) (var8 Int) (var9 Int) (var10 Addr) (var11 Int) (var12 Int) (var13 Addr) (var14 Heap) (var15 Int) (var16 Addr) (var17 Int) (var18 Int) (var19 Addr) (var20 Heap)) (or (not (and (inv_main623_7 var20 var19 var18 var17 var16 var15) (and (and (and (and (= nullAddr (|node::next| (getnode (read var20 var16)))) (and (and (and (and (and (and (= var14 (write var20 var16 defObj)) (or (and (= var19 var16) (= var13 nullAddr)) (and (not (= var19 var16)) (= var13 var19)))) (= var12 var18)) (= var11 var17)) (= var10 var16)) (= var9 var15)) (= var8 4))) (and (and (and (and (and (and (= var7 var14) (= var6 var13)) (= var5 var12)) (= var4 var11)) (= var3 nullAddr)) (= var2 var9)) (= var1 var8))) (<= 0 var15)) (= var0 (+ var2 (- 1)))))) (inv_main623_7 var7 var6 var5 var4 var3 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Addr) (var7 Heap)) (or (not (and (inv_main586_3 var7 var6 var5 var4 var3 var2 var1) (and (not (<= 0 (+ var3 (- 1)))) (= var0 (+ var5 (- 1)))))) (inv_main623_7 var7 var6 var5 var4 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Addr) (var8 Heap) (var9 Bool) (var10 node) (var11 Addr) (var12 Int) (var13 Int) (var14 Int) (var15 Int) (var16 Addr) (var17 Heap) (var18 Addr) (var19 Addr) (var20 Int) (var21 Int) (var22 Int) (var23 Int) (var24 Addr) (var25 Heap) (var26 Addr) (var27 Addr) (var28 Addr) (var29 Int) (var30 Int) (var31 Int) (var32 Int) (var33 Int) (var34 Int) (var35 Int) (var36 Addr) (var37 Addr) (var38 Int) (var39 Addr) (var40 Heap) (var41 Heap) (var42 Addr) (var43 Addr) (var44 Int) (var45 Int) (var46 Int) (var47 Int) (var48 Addr) (var49 Heap)) (or (not (and (inv_main586_3 var49 var48 var47 var46 var45 var44 var43) (and (and (and (and (and (and (not (= var42 nullAddr)) (and (and (and (and (and (and (and (and (= var41 (write var40 var39 (O_node (node var38 (|node::next| (getnode (read var40 var39))) (|node::prev| (getnode (read var40 var39))))))) (= var37 var36)) (= var35 var34)) (= var33 var32)) (= var31 var30)) (= var29 var38)) (= var28 var27)) (= var26 var39)) (and (and (and (and (and (and (and (= var25 (write var41 var26 (O_node (node (|node::data| (getnode (read var41 var26))) var28 (|node::prev| (getnode (read var41 var26))))))) (= var24 var37)) (= var23 var35)) (= var22 var33)) (= var21 var31)) (= var20 var29)) (= var19 var28)) (= var18 var26)))) (and (and (and (and (and (and (and (= var17 (write var25 var18 (O_node (node (|node::data| (getnode (read var25 var18))) (|node::next| (getnode (read var25 var18))) nullAddr)))) (= var16 var24)) (= var15 var23)) (= var14 var22)) (= var13 var21)) (= var12 var20)) (= var42 var19)) (= var11 var18))) (and (not (= nullAddr var39)) (and (and (and (and (and (and (and (= var40 (newHeap (alloc var49 (O_node var10)))) (or (and var9 (= var36 (newAddr (alloc var49 (O_node var10))))) (and (not var9) (= var36 var48)))) (= var34 var47)) (= var32 var46)) (= var30 var45)) (= var38 var44)) (= var27 var43)) (= var39 (newAddr (alloc var49 (O_node var10))))))) (and (and (and (and (and (and (and (= var8 (write var17 var42 (O_node (node (|node::data| (getnode (read var17 var42))) (|node::next| (getnode (read var17 var42))) var11)))) (= var7 var16)) (= var6 var15)) (= var5 var14)) (= var4 var13)) (= var3 var12)) (= var2 var42)) (= var1 var11))) (<= 0 (+ var45 (- 1)))) (= var0 (+ var4 (- 1)))))) (inv_main586_3 var8 var7 var6 var5 var0 var3 var1))))
(assert (forall ((var0 Int) (var1 Bool) (var2 node) (var3 Addr) (var4 Int) (var5 Int) (var6 Int) (var7 Int) (var8 Addr) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Int) (var13 Int) (var14 Int) (var15 Int) (var16 Addr) (var17 Heap) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Int) (var22 Int) (var23 Int) (var24 Int) (var25 Int) (var26 Int) (var27 Int) (var28 Addr) (var29 Addr) (var30 Int) (var31 Addr) (var32 Heap) (var33 Heap) (var34 Addr) (var35 Addr) (var36 Int) (var37 Int) (var38 Int) (var39 Int) (var40 Addr) (var41 Heap)) (or (not (and (inv_main586_3 var41 var40 var39 var38 var37 var36 var35) (and (and (and (and (and (= var34 nullAddr) (and (and (and (and (and (and (and (and (= var33 (write var32 var31 (O_node (node var30 (|node::next| (getnode (read var32 var31))) (|node::prev| (getnode (read var32 var31))))))) (= var29 var28)) (= var27 var26)) (= var25 var24)) (= var23 var22)) (= var21 var30)) (= var20 var19)) (= var18 var31)) (and (and (and (and (and (and (and (= var17 (write var33 var18 (O_node (node (|node::data| (getnode (read var33 var18))) var20 (|node::prev| (getnode (read var33 var18))))))) (= var16 var29)) (= var15 var27)) (= var14 var25)) (= var13 var23)) (= var12 var21)) (= var11 var20)) (= var10 var18)))) (and (and (and (and (and (and (and (= var9 (write var17 var10 (O_node (node (|node::data| (getnode (read var17 var10))) (|node::next| (getnode (read var17 var10))) nullAddr)))) (= var8 var16)) (= var7 var15)) (= var6 var14)) (= var5 var13)) (= var4 var12)) (= var34 var11)) (= var3 var10))) (and (not (= nullAddr var31)) (and (and (and (and (and (and (and (= var32 (newHeap (alloc var41 (O_node var2)))) (or (and var1 (= var28 (newAddr (alloc var41 (O_node var2))))) (and (not var1) (= var28 var40)))) (= var26 var39)) (= var24 var38)) (= var22 var37)) (= var30 var36)) (= var19 var35)) (= var31 (newAddr (alloc var41 (O_node var2))))))) (<= 0 (+ var37 (- 1)))) (= var0 (+ var5 (- 1)))))) (inv_main586_3 var9 var8 var7 var6 var0 var4 var3))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Addr) (var4 Heap)) (or (not (and (inv_main621_3 var4 var3 var2 var1) (= var0 nullAddr))) (inv_main586_3 var4 var3 var2 var1 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Addr) (var8 Heap)) (or (not (inv_main590_7 var8 var7 var6 var5 var4 var3 var2 var1 var0)) (inv_main590_7 var8 var7 var6 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Bool) (var7 Addr) (var8 node) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Int) (var13 Int) (var14 Int) (var15 Int) (var16 Addr) (var17 Heap)) (or (not (and (inv_main586_3 var17 var16 var15 var14 var13 var12 var11) (and (and (and (= nullAddr var10) (and (and (and (and (and (and (and (= var9 (newHeap (alloc var17 (O_node var8)))) (or (and var6 (= var7 (newAddr (alloc var17 (O_node var8))))) (and (not var6) (= var7 var16)))) (= var5 var15)) (= var4 var14)) (= var3 var13)) (= var2 var12)) (= var1 var11)) (= var10 (newAddr (alloc var17 (O_node var8)))))) (<= 0 (+ var13 (- 1)))) (= var0 1)))) (inv_main590_7 var9 var7 var5 var4 var3 var2 var1 var10 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Int) (var4 Int) (var5 Addr) (var6 Heap)) (or (not (and (inv_main623_7 var6 var5 var4 var3 var2 var1) (and (and (= nullAddr var2) (not (<= 0 var1))) (= var0 0)))) (inv_main631_10 var6 var5 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Addr) (var5 Heap)) (or (not (and (inv_main623_7 var5 var4 var3 var2 var1 var0) (and (not (= nullAddr var1)) (not (<= 0 var0))))) (inv_exit var5 var4))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_exit var1 var0) (not (= var0 nullAddr))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap)) (not (and (inv_main631_10 var2 var1 var0) (not (= var1 nullAddr))))))
(check-sat)
