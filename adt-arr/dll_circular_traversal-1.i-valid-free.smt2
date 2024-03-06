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
(declare-fun inv_main578_5 (Heap Int Int Int Int Addr Int) Bool)
(declare-fun inv_main583_3 (Heap Int Int Int Int Addr Addr) Bool)
(declare-fun inv_main587_7 (Heap Int Int Int Int Addr Addr Addr Int) Bool)
(declare-fun inv_main602_3 (Heap Int Int) Bool)
(declare-fun inv_main604_3 (Heap Int Int Addr Addr Int) Bool)
(declare-fun inv_main620_5 (Heap Int Int Addr Addr Int Addr) Bool)
(assert (forall ((var0 Int) (var1 Int) (var2 Heap)) (or (not (and (and (= var2 emptyHeap) (= var1 5)) (= var0 1))) (inv_main602_3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Int) (var10 Int) (var11 Heap) (var12 Addr) (var13 Int) (var14 Int) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Int) (var20 Int) (var21 Int) (var22 Int) (var23 Heap) (var24 Heap) (var25 Addr) (var26 Heap) (var27 Int) (var28 Int) (var29 Addr) (var30 Addr) (var31 Int) (var32 Int) (var33 Heap)) (or (not (and (inv_main604_3 var33 var32 var31 var30 var29 var28) (and (and (and (and (= (+ var27 (- 1)) (|node::data| (getnode (read var26 var25)))) (and (and (and (and (and (and (and (= var24 var23) (= var22 var21)) (= var20 var19)) (= var18 var17)) (= var16 var15)) (= var14 (+ var13 1))) (= var12 (|node::prev| (getnode (read var23 var15))))) (and (= var15 var17) (and (and (and (and (and (and (and (and (= var23 var11) (= var21 var10)) (= var19 var9)) (= var17 var8)) (= var7 var6)) (= var13 var5)) (= var15 (|node::next| (getnode (read var11 var6))))) (= var31 (|node::data| (getnode (read var33 var29))))) (and (and (and (and (and (= var11 (write var33 var29 (O_node (node var28 (|node::next| (getnode (read var33 var29))) (|node::prev| (getnode (read var33 var29))))))) (= var10 var32)) (= var9 var31)) (= var8 var30)) (= var6 var29)) (= var5 var28)))))) (and (and (and (and (and (= var26 var24) (= var4 var22)) (= var3 var20)) (= var2 nullAddr)) (= var25 var12)) (= var27 var14))) (= var1 (+ var27 (- 1)))) (= var0 (|node::prev| (getnode (read var26 var25))))))) (inv_main620_5 var26 var4 var3 var2 var25 var1 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Int) (var5 Int) (var6 Addr) (var7 Heap) (var8 Int) (var9 Addr) (var10 Int) (var11 Addr) (var12 Addr) (var13 Int) (var14 Int) (var15 Heap)) (or (not (and (inv_main620_5 var15 var14 var13 var12 var11 var10 var9) (and (and (and (= (+ var8 (- 1)) (|node::data| (getnode (read var7 var6)))) (and (not (= var6 nullAddr)) (and (and (and (and (and (and (= var7 (write var15 var11 defObj)) (= var5 var14)) (= var4 var13)) (= var3 var12)) (= var2 var11)) (= var8 var10)) (= var6 var9)))) (= var1 (+ var8 (- 1)))) (= var0 (|node::prev| (getnode (read var7 var6))))))) (inv_main620_5 var7 var5 var4 var3 var6 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Int) (var6 Int) (var7 Int) (var8 Heap)) (or (not (inv_main587_7 var8 var7 var6 var5 var4 var3 var2 var1 var0)) (inv_main587_7 var8 var7 var6 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 node) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Int) (var13 Int) (var14 Int) (var15 Int) (var16 Heap)) (or (not (and (inv_main583_3 var16 var15 var14 var13 var12 var11 var10) (and (and (and (= nullAddr var9) (and (and (and (and (and (and (and (= var8 (newHeap (alloc var16 (O_node var7)))) (= var6 var15)) (= var5 var14)) (= var4 var13)) (= var3 var12)) (= var2 var11)) (= var1 var10)) (= var9 (newAddr (alloc var16 (O_node var7)))))) (<= 0 (+ (+ var13 (- 1)) (- 1)))) (= var0 1)))) (inv_main587_7 var8 var6 var5 var4 var3 var2 var1 var9 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Heap)) (or (not (inv_main578_5 var6 var5 var4 var3 var2 var1 var0)) (inv_main578_5 var6 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Int) (var4 Int) (var5 node) (var6 Heap) (var7 Addr) (var8 Int) (var9 Int) (var10 Heap)) (or (not (and (inv_main602_3 var10 var9 var8) (and (and (= nullAddr var7) (and (and (and (and (and (= var6 (newHeap (alloc var10 (O_node var5)))) (= var4 var9)) (= var3 var8)) (= var2 var9)) (= var1 var8)) (= var7 (newAddr (alloc var10 (O_node var5)))))) (= var0 1)))) (inv_main578_5 var6 var4 var3 var2 var1 var7 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Int) (var7 Int) (var8 Int) (var9 Int) (var10 Heap) (var11 Heap) (var12 Addr) (var13 Addr) (var14 Int) (var15 Addr) (var16 Addr) (var17 Int) (var18 Int) (var19 Heap)) (or (not (and (inv_main604_3 var19 var18 var17 var16 var15 var14) (and (and (not (= var13 var12)) (and (and (and (and (and (and (and (and (= var11 var10) (= var9 var8)) (= var7 var6)) (= var12 var5)) (= var4 var3)) (= var2 var1)) (= var13 (|node::next| (getnode (read var10 var3))))) (= var17 (|node::data| (getnode (read var19 var15))))) (and (and (and (and (and (= var10 (write var19 var15 (O_node (node var14 (|node::next| (getnode (read var19 var15))) (|node::prev| (getnode (read var19 var15))))))) (= var8 var18)) (= var6 var17)) (= var5 var16)) (= var3 var15)) (= var1 var14)))) (= var0 (+ var2 1))))) (inv_main604_3 var11 var9 var7 var12 var13 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Int) (var11 Int) (var12 Int) (var13 Int) (var14 Heap) (var15 Addr) (var16 Addr) (var17 Int) (var18 Int) (var19 Int) (var20 Int) (var21 Heap)) (or (not (and (inv_main583_3 var21 var20 var19 var18 var17 var16 var15) (and (and (and (not (<= 0 (+ (+ var18 (- 1)) (- 1)))) (and (and (and (and (and (and (= var14 (write var21 var16 (O_node (node (|node::data| (getnode (read var21 var16))) var15 (|node::prev| (getnode (read var21 var16))))))) (= var13 var20)) (= var12 var19)) (= var11 var18)) (= var10 var17)) (= var9 var16)) (= var8 var15))) (and (and (and (and (and (and (= var7 (write var14 var8 (O_node (node (|node::data| (getnode (read var14 var8))) (|node::next| (getnode (read var14 var8))) var9)))) (= var6 var13)) (= var5 var12)) (= var4 var11)) (= var3 var10)) (= var2 var9)) (= var1 var8))) (= var0 1)))) (inv_main604_3 var7 var6 var5 var1 var1 var0))))
(assert (forall ((var0 Int) (var1 node) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Int) (var6 Int) (var7 Int) (var8 Int) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Int) (var14 Int) (var15 Int) (var16 Int) (var17 Heap) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Int) (var23 Int) (var24 Int) (var25 Int) (var26 Int) (var27 Int) (var28 Int) (var29 Int) (var30 Addr) (var31 Addr) (var32 Heap) (var33 Heap) (var34 Addr) (var35 Addr) (var36 Int) (var37 Int) (var38 Int) (var39 Int) (var40 Heap)) (or (not (and (inv_main583_3 var40 var39 var38 var37 var36 var35 var34) (and (and (and (and (and (and (and (and (and (and (and (and (= var33 (write var32 var31 (O_node (node (|node::data| (getnode (read var32 var31))) var30 (|node::prev| (getnode (read var32 var31))))))) (= var29 var28)) (= var27 var26)) (= var25 var24)) (= var23 var22)) (= var21 var20)) (= var19 var30)) (= var18 var31)) (and (and (and (and (and (and (and (= var17 (write var33 var18 (O_node (node var23 (|node::next| (getnode (read var33 var18))) (|node::prev| (getnode (read var33 var18))))))) (= var16 var29)) (= var15 var27)) (= var14 var25)) (= var13 var23)) (= var12 var21)) (= var11 var19)) (= var10 var18))) (and (and (and (and (and (and (and (= var9 (write var17 var11 (O_node (node (|node::data| (getnode (read var17 var11))) (|node::next| (getnode (read var17 var11))) var10)))) (= var8 var16)) (= var7 var15)) (= var6 var14)) (= var5 var13)) (= var4 var12)) (= var3 var11)) (= var2 var10))) (and (not (= nullAddr var31)) (and (and (and (and (and (and (and (= var32 (newHeap (alloc var40 (O_node var1)))) (= var28 var39)) (= var26 var38)) (= var24 var37)) (= var22 var36)) (= var20 var35)) (= var30 var34)) (= var31 (newAddr (alloc var40 (O_node var1))))))) (<= 0 (+ (+ var37 (- 1)) (- 1)))) (= var0 (+ var6 (- 1)))))) (inv_main583_3 var9 var8 var7 var0 var5 var4 var2))))
(assert (forall ((var0 node) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Heap) (var7 Addr) (var8 Int) (var9 Int) (var10 Int) (var11 Int) (var12 Heap) (var13 Addr) (var14 Int) (var15 Int) (var16 Int) (var17 Int) (var18 Int) (var19 Int) (var20 Int) (var21 Int) (var22 Addr) (var23 Heap) (var24 Heap) (var25 Int) (var26 Int) (var27 Heap)) (or (not (and (inv_main602_3 var27 var26 var25) (and (and (and (and (and (and (and (and (= var24 (write var23 var22 (O_node (node (|node::data| (getnode (read var23 var22))) var22 (|node::prev| (getnode (read var23 var22))))))) (= var21 var20)) (= var19 var18)) (= var17 var16)) (= var15 var14)) (= var13 var22)) (and (and (and (and (and (= var12 (write var24 var13 (O_node (node (|node::data| (getnode (read var24 var13))) (|node::next| (getnode (read var24 var13))) var13)))) (= var11 var21)) (= var10 var19)) (= var9 var17)) (= var8 var15)) (= var7 var13))) (and (and (and (and (and (= var6 (write var12 var7 (O_node (node var8 (|node::next| (getnode (read var12 var7))) (|node::prev| (getnode (read var12 var7))))))) (= var5 var11)) (= var4 var10)) (= var3 var9)) (= var2 var8)) (= var1 var7))) (and (not (= nullAddr var22)) (and (and (and (and (and (= var23 (newHeap (alloc var27 (O_node var0)))) (= var20 var26)) (= var18 var25)) (= var16 var26)) (= var14 var25)) (= var22 (newAddr (alloc var27 (O_node var0))))))))) (inv_main583_3 var6 var5 var4 var3 var2 var1 var1))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Int) (var5 Int) (var6 Heap)) (not (and (inv_main620_5 var6 var5 var4 var3 var2 var1 var0) (and (not (= var2 nullAddr)) (= (read var6 var2) defObj))))))
(check-sat)
