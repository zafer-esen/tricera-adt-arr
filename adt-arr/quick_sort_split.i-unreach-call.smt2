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
                   ((node (|node::expected_list| Int) (|node::value| Int) (|node::next| Addr)))))
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
(declare-fun inv_main581_5 (Heap Addr) Bool)
(declare-fun inv_main592_5 (Heap) Bool)
(declare-fun inv_main595_5 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main604_13 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main609_13 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main_14 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main_19 (Heap Addr Addr Addr Addr) Bool)
(assert (forall ((var0 Heap)) (or (not (= var0 emptyHeap)) (inv_main592_5 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Int) (var10 Int) (var11 Int) (var12 Int) (var13 Addr) (var14 Heap) (var15 Addr) (var16 Int) (var17 Int) (var18 Int) (var19 Int) (var20 Addr) (var21 Heap) (var22 Addr) (var23 Int) (var24 Int) (var25 Int) (var26 Int) (var27 Int) (var28 Addr) (var29 node) (var30 Heap) (var31 Addr) (var32 Heap)) (or (not (and (inv_main581_5 var32 var31) (and (and (and (and (and (and (and (and (and (and (and (= var30 (newHeap (alloc var32 (O_node var29)))) (= var28 var31)) (= var27 var26)) (= var25 1)) (= var24 var26)) (= var23 (- 1))) (= var22 (newAddr (alloc var32 (O_node var29))))) (and (and (and (and (and (and (= var21 (write var30 var22 (O_node (node (|node::expected_list| (getnode (read var30 var22))) (|node::value| (getnode (read var30 var22))) var28)))) (= var20 var28)) (= var19 var27)) (= var18 var25)) (= var17 var24)) (= var16 var23)) (= var15 var22))) (and (and (and (and (and (and (= var14 (write var21 var15 (O_node (node (|node::expected_list| (getnode (read var21 var15))) var17 (|node::next| (getnode (read var21 var15))))))) (= var13 var20)) (= var12 var19)) (= var11 var18)) (= var10 var17)) (= var9 var16)) (= var8 var15))) (and (and (and (and (and (and (= var7 (write var14 var8 (O_node (node var9 (|node::value| (getnode (read var14 var8))) (|node::next| (getnode (read var14 var8))))))) (= var6 var13)) (= var5 var12)) (= var4 var11)) (= var3 var10)) (= var2 var9)) (= var1 var8))) (<= 0 (+ (* (- 1) var26) (- 1)))) (not (= var0 0))))) (inv_main581_5 var7 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Int) (var10 Int) (var11 Int) (var12 Int) (var13 Addr) (var14 Heap) (var15 Addr) (var16 Int) (var17 Int) (var18 Int) (var19 Int) (var20 Addr) (var21 Heap) (var22 Addr) (var23 Int) (var24 Int) (var25 Int) (var26 Int) (var27 Int) (var28 Addr) (var29 node) (var30 Heap) (var31 Addr) (var32 Heap)) (or (not (and (inv_main581_5 var32 var31) (and (and (and (and (and (and (and (and (and (and (and (= var30 (newHeap (alloc var32 (O_node var29)))) (= var28 var31)) (= var27 var26)) (= var25 1)) (= var24 var26)) (= var23 1)) (= var22 (newAddr (alloc var32 (O_node var29))))) (and (and (and (and (and (and (= var21 (write var30 var22 (O_node (node (|node::expected_list| (getnode (read var30 var22))) (|node::value| (getnode (read var30 var22))) var28)))) (= var20 var28)) (= var19 var27)) (= var18 var25)) (= var17 var24)) (= var16 var23)) (= var15 var22))) (and (and (and (and (and (and (= var14 (write var21 var15 (O_node (node (|node::expected_list| (getnode (read var21 var15))) var17 (|node::next| (getnode (read var21 var15))))))) (= var13 var20)) (= var12 var19)) (= var11 var18)) (= var10 var17)) (= var9 var16)) (= var8 var15))) (and (and (and (and (and (and (= var7 (write var14 var8 (O_node (node var9 (|node::value| (getnode (read var14 var8))) (|node::next| (getnode (read var14 var8))))))) (= var6 var13)) (= var5 var12)) (= var4 var11)) (= var3 var10)) (= var2 var9)) (= var1 var8))) (not (<= 0 (+ (* (- 1) var26) (- 1))))) (not (= var0 0))))) (inv_main581_5 var7 var1))))
(assert (forall ((var0 Addr) (var1 Heap)) (or (not (and (inv_main592_5 var1) (= var0 nullAddr))) (inv_main581_5 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Int) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main_14 var10 var9 var8 var7 var6) (and (and (not (= var5 (- 1))) (and (and (and (and (and (= var4 var10) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var0 var6)) (= var5 (|node::expected_list| (getnode (read var10 var8)))))) (not (= var8 nullAddr))))) (inv_main604_13 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Heap) (var19 Heap) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Heap)) (or (not (and (inv_main595_5 var24 var23 var22 var21 var20) (and (and (and (and (and (and (and (and (and (= var19 var18) (= var17 var16)) (= var15 var14)) (= var13 var12)) (= var11 var10)) (= var9 var12)) (= var8 (|node::next| (getnode (read var18 var10))))) (and (and (and (and (and (and (= var7 (write var19 var11 (O_node (node (|node::expected_list| (getnode (read var19 var11))) (|node::value| (getnode (read var19 var11))) var9)))) (= var6 var17)) (= var5 var15)) (= var4 var13)) (= var3 var11)) (= var2 var9)) (= var1 var8))) (and (<= 0 var0) (and (and (and (and (and (= var18 var24) (= var16 var23)) (= var14 var22)) (= var12 var21)) (= var10 var20)) (= var0 (|node::value| (getnode (read var24 var20))))))) (not (= var20 nullAddr))))) (inv_main595_5 var7 var6 var5 var4 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Heap) (var19 Heap) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Heap)) (or (not (and (inv_main595_5 var24 var23 var22 var21 var20) (and (and (and (and (and (and (and (and (and (= var19 var18) (= var17 var16)) (= var15 var14)) (= var13 var12)) (= var11 var10)) (= var9 var14)) (= var8 (|node::next| (getnode (read var18 var10))))) (and (and (and (and (and (and (= var7 (write var19 var11 (O_node (node (|node::expected_list| (getnode (read var19 var11))) (|node::value| (getnode (read var19 var11))) var9)))) (= var6 var17)) (= var5 var15)) (= var4 var13)) (= var3 var11)) (= var2 var9)) (= var1 var8))) (and (not (<= 0 var0)) (and (and (and (and (and (= var18 var24) (= var16 var23)) (= var14 var22)) (= var12 var21)) (= var10 var20)) (= var0 (|node::value| (getnode (read var24 var20))))))) (not (= var20 nullAddr))))) (inv_main595_5 var7 var6 var5 var4 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Heap) (var8 Addr) (var9 Heap)) (or (not (and (inv_main581_5 var9 var8) (and (and (and (and (and (= var7 var6) (= var5 var4)) (= var3 var2)) (= var1 nullAddr)) (and (and (= var6 var9) (= var4 var8)) (= var2 nullAddr))) (= var0 0)))) (inv_main595_5 var7 var5 var3 var1 var5))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main_14 var4 var3 var2 var1 var0) (= var2 nullAddr))) (inv_main_19 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main609_13 var10 var9 var8 var7 var6) (and (and (and (and (and (= var5 var10) (= var4 var9)) (= var3 var8)) (= var2 var7)) (= var1 var6)) (= var0 (|node::next| (getnode (read var10 var7))))))) (inv_main_19 var5 var4 var3 var0 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap) (var11 Heap) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Heap)) (or (not (and (inv_main_19 var16 var15 var14 var13 var12) (and (and (and (and (and (and (= var11 var10) (= var9 var8)) (= var7 var6)) (= var5 var4)) (= var3 var2)) (= var1 (|node::next| (getnode (read var10 var4))))) (and (and (= var0 1) (and (and (and (and (and (= var10 var16) (= var8 var15)) (= var6 var14)) (= var4 var13)) (= var2 var12)) (= var0 (|node::expected_list| (getnode (read var16 var13)))))) (not (= var13 nullAddr)))))) (inv_main_19 var11 var9 var7 var1 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main595_5 var4 var3 var2 var1 var0) (= var0 nullAddr))) (inv_main_14 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main604_13 var10 var9 var8 var7 var6) (and (and (and (and (and (= var5 var10) (= var4 var9)) (= var3 var8)) (= var2 var7)) (= var1 var6)) (= var0 (|node::next| (getnode (read var10 var8))))))) (inv_main_14 var5 var4 var0 var2 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap) (var11 Heap) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Heap)) (or (not (and (inv_main_14 var16 var15 var14 var13 var12) (and (and (and (and (and (and (= var11 var10) (= var9 var8)) (= var7 var6)) (= var5 var4)) (= var3 var2)) (= var1 (|node::next| (getnode (read var10 var6))))) (and (and (= var0 (- 1)) (and (and (and (and (and (= var10 var16) (= var8 var15)) (= var6 var14)) (= var4 var13)) (= var2 var12)) (= var0 (|node::expected_list| (getnode (read var16 var14)))))) (not (= var14 nullAddr)))))) (inv_main_14 var11 var9 var1 var5 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Int) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main_19 var10 var9 var8 var7 var6) (and (and (not (= var5 1)) (and (and (and (and (and (= var4 var10) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var0 var6)) (= var5 (|node::expected_list| (getnode (read var10 var7)))))) (not (= var7 nullAddr))))) (inv_main609_13 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (not (inv_main604_13 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (not (inv_main609_13 var4 var3 var2 var1 var0))))
(check-sat)
