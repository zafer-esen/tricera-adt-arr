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
(declare-fun inv_exit (Heap Addr) Bool)
(declare-fun inv_main532_3 (Heap Addr) Bool)
(declare-fun inv_main533_15 (Heap Addr Addr Int) Bool)
(declare-fun inv_main536_3 (Heap Addr Addr Addr Addr Int) Bool)
(declare-fun inv_main540_17 (Heap Addr Addr Addr Addr Int Int) Bool)
(declare-fun inv_main562_10 (Heap Addr Int) Bool)
(declare-fun inv_main_16 (Heap Addr Addr Addr Addr Int) Bool)
(declare-fun inv_main_24 (Heap Addr Addr Addr Addr Int) Bool)
(assert (forall ((var0 Addr) (var1 Heap)) (or (not (and (= var1 emptyHeap) (= var0 nullAddr))) (inv_main532_3 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Int) (var6 Int) (var7 Int) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Heap)) (or (not (and (inv_main_16 var12 var11 var10 var9 var8 var7) (and (and (not (= var6 var5)) (and (and (and (and (and (and (= var4 var12) (= var3 var11)) (= var2 var10)) (= var1 var9)) (= var0 var8)) (= var5 var7)) (= var6 (|node::h| (getnode (read var12 var8)))))) (not (= var8 nullAddr))))) (inv_exit var4 var3))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (inv_main540_17 var6 var5 var4 var3 var2 var1 var0)) (inv_main540_17 var6 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Int) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Bool) (var12 Addr) (var13 node) (var14 Heap) (var15 Heap) (var16 Addr) (var17 Int) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Heap)) (or (not (and (inv_main536_3 var22 var21 var20 var19 var18 var17) (and (and (= var16 nullAddr) (and (and (and (and (and (and (and (and (= var15 (newHeap (alloc var14 (O_node var13)))) (or (and var11 (= var12 (newAddr (alloc var14 (O_node var13))))) (and (not var11) (= var12 var10)))) (= var9 var8)) (= var7 var6)) (= var5 var4)) (= var3 var2)) (= var16 (newAddr (alloc var14 (O_node var13))))) (and (not (= var1 0)) (<= 0 (+ (+ 30 (* (- 1) var17)) (- 1))))) (and (and (and (and (and (= var14 (write var22 var18 (O_node (node var17 (|node::n| (getnode (read var22 var18))))))) (= var10 var21)) (= var8 var20)) (= var6 var19)) (= var4 var18)) (= var2 var17)))) (= var0 1)))) (inv_main540_17 var15 var12 var9 var16 var5 var3 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main_16 var5 var4 var3 var2 var1 var0) (= var1 nullAddr))) (inv_main_24 var5 var4 var3 var2 var3 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Int) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Heap) (var13 Int) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Heap)) (or (not (and (inv_main_24 var18 var17 var16 var15 var14 var13) (and (and (and (and (and (and (and (and (= var12 var18) (= var11 var17)) (= var10 var16)) (= var9 var15)) (= var8 var14)) (= var7 var13)) (= var6 (|node::n| (getnode (read var18 var14))))) (not (= var14 nullAddr))) (and (and (and (and (and (= var5 (write var12 var8 defObj)) (or (and (= var11 var8) (= var4 nullAddr)) (and (not (= var11 var8)) (= var4 var11)))) (= var3 var10)) (= var2 var6)) (= var1 var8)) (= var0 var7))))) (inv_main_24 var5 var4 var3 var2 var2 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Bool) (var9 node) (var10 Heap) (var11 Int) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Heap) (var17 Addr) (var18 Int) (var19 Int) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Addr) (var25 Addr) (var26 Addr) (var27 Addr) (var28 Heap) (var29 Heap) (var30 Int) (var31 Addr) (var32 Addr) (var33 Addr) (var34 Addr) (var35 Heap)) (or (not (and (inv_main536_3 var35 var34 var33 var32 var31 var30) (and (and (and (and (and (and (and (and (and (= var29 var28) (= var27 var26)) (= var25 var24)) (= var23 var22)) (= var21 var20)) (= var19 var18)) (= var17 (|node::n| (getnode (read var28 var20))))) (and (and (and (and (and (= var28 (write var16 var15 (O_node (node (|node::h| (getnode (read var16 var15))) var14)))) (= var26 var13)) (= var24 var12)) (= var22 var14)) (= var20 var15)) (= var18 var11))) (and (not (= var14 nullAddr)) (and (and (and (and (and (and (and (and (= var16 (newHeap (alloc var10 (O_node var9)))) (or (and var8 (= var13 (newAddr (alloc var10 (O_node var9))))) (and (not var8) (= var13 var7)))) (= var12 var6)) (= var5 var4)) (= var15 var3)) (= var11 var2)) (= var14 (newAddr (alloc var10 (O_node var9))))) (and (not (= var1 0)) (<= 0 (+ (+ 30 (* (- 1) var30)) (- 1))))) (and (and (and (and (and (= var10 (write var35 var31 (O_node (node var30 (|node::n| (getnode (read var35 var31))))))) (= var7 var34)) (= var6 var33)) (= var4 var32)) (= var3 var31)) (= var2 var30))))) (= var0 (+ var19 1))))) (inv_main536_3 var29 var27 var25 var23 var17 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Bool) (var3 Addr) (var4 node) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main532_3 var8 var7) (and (and (not (= var6 nullAddr)) (and (and (= var5 (newHeap (alloc var8 (O_node var4)))) (or (and var2 (= var3 (newAddr (alloc var8 (O_node var4))))) (and (not var2) (= var3 var7)))) (= var6 (newAddr (alloc var8 (O_node var4)))))) (= var1 0)))) (inv_main536_3 var5 var3 var6 var0 var6 var1))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main_24 var6 var5 var4 var3 var2 var1) (and (= var2 nullAddr) (= var0 0)))) (inv_main562_10 var6 var5 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (inv_main533_15 var3 var2 var1 var0)) (inv_main533_15 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Bool) (var2 Addr) (var3 node) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main532_3 var7 var6) (and (and (= var5 nullAddr) (and (and (= var4 (newHeap (alloc var7 (O_node var3)))) (or (and var1 (= var2 (newAddr (alloc var7 (O_node var3))))) (and (not var1) (= var2 var6)))) (= var5 (newAddr (alloc var7 (O_node var3)))))) (= var0 1)))) (inv_main533_15 var4 var2 var5 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Int) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Heap) (var13 Int) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Heap)) (or (not (and (inv_main536_3 var18 var17 var16 var15 var14 var13) (and (and (and (not (<= 0 (+ (+ 30 (* (- 1) var13)) (- 1)))) (and (and (and (and (and (= var12 (write var18 var14 (O_node (node var13 (|node::n| (getnode (read var18 var14))))))) (= var11 var17)) (= var10 var16)) (= var9 var15)) (= var8 var14)) (= var7 var13))) (and (and (and (and (and (= var6 (write var12 var8 (O_node (node (|node::h| (getnode (read var12 var8))) 0)))) (= var5 var11)) (= var4 var10)) (= var3 var9)) (= var2 var8)) (= var1 var7))) (= var0 0)))) (inv_main_16 var6 var5 var4 var3 var4 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Int) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Heap) (var13 Int) (var14 Int) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Heap)) (or (not (and (inv_main536_3 var19 var18 var17 var16 var15 var14) (and (and (and (and (= var13 0) (<= 0 (+ (+ 30 (* (- 1) var14)) (- 1)))) (and (and (and (and (and (= var12 (write var19 var15 (O_node (node var14 (|node::n| (getnode (read var19 var15))))))) (= var11 var18)) (= var10 var17)) (= var9 var16)) (= var8 var15)) (= var7 var14))) (and (and (and (and (and (= var6 (write var12 var8 (O_node (node (|node::h| (getnode (read var12 var8))) 0)))) (= var5 var11)) (= var4 var10)) (= var3 var9)) (= var2 var8)) (= var1 var7))) (= var0 0)))) (inv_main_16 var6 var5 var4 var3 var4 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Int) (var4 Int) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Heap) (var14 Heap) (var15 Int) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Heap)) (or (not (and (inv_main_16 var20 var19 var18 var17 var16 var15) (and (and (and (and (and (and (and (and (= var14 var13) (= var12 var11)) (= var10 var9)) (= var8 var7)) (= var6 var5)) (= var4 var3)) (= var2 (|node::n| (getnode (read var13 var5))))) (and (and (= var1 var3) (and (and (and (and (and (and (= var13 var20) (= var11 var19)) (= var9 var18)) (= var7 var17)) (= var5 var16)) (= var3 var15)) (= var1 (|node::h| (getnode (read var20 var16)))))) (not (= var16 nullAddr)))) (= var0 (+ var4 1))))) (inv_main_16 var14 var12 var10 var8 var2 var0))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_exit var1 var0) (not (= var0 nullAddr))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap)) (not (and (inv_main562_10 var2 var1 var0) (not (= var1 nullAddr))))))
(check-sat)
