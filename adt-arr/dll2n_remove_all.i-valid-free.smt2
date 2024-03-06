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
(declare-fun inv_main586_3 (Heap Int Int Int Int Addr) Bool)
(declare-fun inv_main590_7 (Heap Int Int Int Int Addr Addr Int) Bool)
(declare-fun inv_main614_3 (Heap Int Int) Bool)
(declare-fun inv_main_14 (Heap Int Int Addr Int Int Addr) Bool)
(assert (forall ((var0 Int) (var1 Int) (var2 Heap)) (or (not (and (and (= var2 emptyHeap) (= var1 2)) (= var0 1))) (inv_main614_3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Heap)) (or (not (inv_main590_7 var7 var6 var5 var4 var3 var2 var1 var0)) (inv_main590_7 var7 var6 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 node) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Int) (var11 Int) (var12 Int) (var13 Int) (var14 Heap)) (or (not (and (inv_main586_3 var14 var13 var12 var11 var10 var9) (and (and (and (= nullAddr var8) (and (and (and (and (and (and (= var7 (newHeap (alloc var14 (O_node var6)))) (= var5 var13)) (= var4 var12)) (= var3 var11)) (= var2 var10)) (= var1 var9)) (= var8 (newAddr (alloc var14 (O_node var6)))))) (<= 0 (+ var11 (- 1)))) (= var0 1)))) (inv_main590_7 var7 var5 var4 var3 var2 var1 var8 var0))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Addr) (var7 Addr) (var8 Int) (var9 Int) (var10 Int) (var11 Int) (var12 Heap) (var13 Heap) (var14 Addr) (var15 Addr) (var16 Int) (var17 Int) (var18 Addr) (var19 Int) (var20 Int) (var21 Heap)) (or (not (and (inv_main_14 var21 var20 var19 var18 var17 var16 var15) (and (and (and (and (not (= var14 nullAddr)) (and (and (and (and (and (and (= var13 var12) (= var11 var10)) (= var9 var8)) (= var7 var6)) (= var5 (+ var4 (- 1)))) (= var3 3)) (= var14 (|node::next| (getnode (read var12 var6)))))) (<= 0 (+ var4 (- 1)))) (and (and (and (and (and (and (= var12 (write var21 var18 defObj)) (= var10 var20)) (= var8 var19)) (= var2 var18)) (= var4 var17)) (= var1 var16)) (= var6 var15))) (= var0 (write var13 var14 (O_node (node (|node::data| (getnode (read var13 var14))) (|node::next| (getnode (read var13 var14))) nullAddr))))))) (inv_main_14 var0 var11 var9 var7 var5 var3 var14))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Addr) (var6 Addr) (var7 Int) (var8 Int) (var9 Int) (var10 Int) (var11 Heap) (var12 Heap) (var13 Addr) (var14 Addr) (var15 Int) (var16 Int) (var17 Addr) (var18 Int) (var19 Int) (var20 Heap)) (or (not (and (inv_main_14 var20 var19 var18 var17 var16 var15 var14) (and (and (and (= var13 nullAddr) (and (and (and (and (and (and (= var12 var11) (= var10 var9)) (= var8 var7)) (= var6 var5)) (= var4 (+ var3 (- 1)))) (= var2 3)) (= var13 (|node::next| (getnode (read var11 var5)))))) (<= 0 (+ var3 (- 1)))) (and (and (and (and (and (and (= var11 (write var20 var17 defObj)) (= var9 var19)) (= var7 var18)) (= var1 var17)) (= var3 var16)) (= var0 var15)) (= var5 var14))))) (inv_main_14 var12 var10 var8 var6 var4 var2 var13))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Int) (var3 Addr) (var4 Int) (var5 Int) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Int) (var10 Int) (var11 Int) (var12 Int) (var13 Heap)) (or (not (and (inv_main586_3 var13 var12 var11 var10 var9 var8) (and (and (and (and (not (= var7 nullAddr)) (and (and (and (and (and (and (= var6 var13) (= var5 var12)) (= var4 var11)) (= var3 var8)) (= var2 (+ var12 (- 1)))) (= var1 3)) (= var7 (|node::next| (getnode (read var13 var8)))))) (<= 0 (+ var12 (- 1)))) (not (<= 0 (+ var10 (- 1))))) (= var0 (write var6 var7 (O_node (node (|node::data| (getnode (read var6 var7))) (|node::next| (getnode (read var6 var7))) nullAddr))))))) (inv_main_14 var0 var5 var4 var3 var2 var1 var7))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Int) (var4 Int) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Int) (var9 Int) (var10 Int) (var11 Int) (var12 Heap)) (or (not (and (inv_main586_3 var12 var11 var10 var9 var8 var7) (and (and (and (= var6 nullAddr) (and (and (and (and (and (and (= var5 var12) (= var4 var11)) (= var3 var10)) (= var2 var7)) (= var1 (+ var11 (- 1)))) (= var0 3)) (= var6 (|node::next| (getnode (read var12 var7)))))) (<= 0 (+ var11 (- 1)))) (not (<= 0 (+ var9 (- 1))))))) (inv_main_14 var5 var4 var3 var2 var1 var0 var6))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Heap) (var8 node) (var9 Addr) (var10 Int) (var11 Int) (var12 Int) (var13 Int) (var14 Heap) (var15 Addr) (var16 Addr) (var17 Int) (var18 Int) (var19 Int) (var20 Int) (var21 Heap) (var22 Addr) (var23 Addr) (var24 Addr) (var25 Int) (var26 Int) (var27 Int) (var28 Int) (var29 Int) (var30 Int) (var31 Int) (var32 Int) (var33 Addr) (var34 Heap) (var35 Heap) (var36 Addr) (var37 Addr) (var38 Int) (var39 Int) (var40 Int) (var41 Int) (var42 Heap)) (or (not (and (inv_main586_3 var42 var41 var40 var39 var38 var37) (and (and (and (and (and (and (not (= var36 nullAddr)) (and (and (and (and (and (and (and (= var35 (write var34 var33 (O_node (node var32 (|node::next| (getnode (read var34 var33))) (|node::prev| (getnode (read var34 var33))))))) (= var31 var30)) (= var29 var28)) (= var27 var26)) (= var25 var32)) (= var24 var23)) (= var22 var33)) (and (and (and (and (and (and (= var21 (write var35 var22 (O_node (node (|node::data| (getnode (read var35 var22))) var24 (|node::prev| (getnode (read var35 var22))))))) (= var20 var31)) (= var19 var29)) (= var18 var27)) (= var17 var25)) (= var16 var24)) (= var15 var22)))) (and (and (and (and (and (and (= var14 (write var21 var15 (O_node (node (|node::data| (getnode (read var21 var15))) (|node::next| (getnode (read var21 var15))) nullAddr)))) (= var13 var20)) (= var12 var19)) (= var11 var18)) (= var10 var17)) (= var36 var16)) (= var9 var15))) (and (not (= nullAddr var33)) (and (and (and (and (and (and (= var34 (newHeap (alloc var42 (O_node var8)))) (= var30 var41)) (= var28 var40)) (= var26 var39)) (= var32 var38)) (= var23 var37)) (= var33 (newAddr (alloc var42 (O_node var8))))))) (and (and (and (and (and (and (= var7 (write var14 var36 (O_node (node (|node::data| (getnode (read var14 var36))) (|node::next| (getnode (read var14 var36))) var9)))) (= var6 var13)) (= var5 var12)) (= var4 var11)) (= var3 var10)) (= var2 var36)) (= var1 var9))) (<= 0 (+ var39 (- 1)))) (= var0 (+ var4 (- 1)))))) (inv_main586_3 var7 var6 var5 var0 var3 var1))))
(assert (forall ((var0 Int) (var1 node) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Int) (var11 Int) (var12 Int) (var13 Int) (var14 Heap) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Int) (var19 Int) (var20 Int) (var21 Int) (var22 Int) (var23 Int) (var24 Int) (var25 Int) (var26 Addr) (var27 Heap) (var28 Heap) (var29 Addr) (var30 Addr) (var31 Int) (var32 Int) (var33 Int) (var34 Int) (var35 Heap)) (or (not (and (inv_main586_3 var35 var34 var33 var32 var31 var30) (and (and (and (and (and (= var29 nullAddr) (and (and (and (and (and (and (and (= var28 (write var27 var26 (O_node (node var25 (|node::next| (getnode (read var27 var26))) (|node::prev| (getnode (read var27 var26))))))) (= var24 var23)) (= var22 var21)) (= var20 var19)) (= var18 var25)) (= var17 var16)) (= var15 var26)) (and (and (and (and (and (and (= var14 (write var28 var15 (O_node (node (|node::data| (getnode (read var28 var15))) var17 (|node::prev| (getnode (read var28 var15))))))) (= var13 var24)) (= var12 var22)) (= var11 var20)) (= var10 var18)) (= var9 var17)) (= var8 var15)))) (and (and (and (and (and (and (= var7 (write var14 var8 (O_node (node (|node::data| (getnode (read var14 var8))) (|node::next| (getnode (read var14 var8))) nullAddr)))) (= var6 var13)) (= var5 var12)) (= var4 var11)) (= var3 var10)) (= var29 var9)) (= var2 var8))) (and (not (= nullAddr var26)) (and (and (and (and (and (and (= var27 (newHeap (alloc var35 (O_node var1)))) (= var23 var34)) (= var21 var33)) (= var19 var32)) (= var25 var31)) (= var16 var30)) (= var26 (newAddr (alloc var35 (O_node var1))))))) (<= 0 (+ var32 (- 1)))) (= var0 (+ var4 (- 1)))))) (inv_main586_3 var7 var6 var5 var0 var3 var2))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Heap)) (or (not (and (inv_main614_3 var3 var2 var1) (= var0 nullAddr))) (inv_main586_3 var3 var2 var1 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Addr) (var4 Int) (var5 Int) (var6 Heap)) (not (and (inv_main_14 var6 var5 var4 var3 var2 var1 var0) (and (not (= var3 nullAddr)) (= (read var6 var3) defObj))))))
(check-sat)
