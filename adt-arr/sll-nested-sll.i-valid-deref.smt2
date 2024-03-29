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

(declare-datatypes ((HeapObject 0) (node 0) (internal_node 0))
                   (((O_Int (getInt Int)) (O_UInt (getUInt Int)) (O_Addr (getAddr Addr)) (O_AddrRange (getAddrRange AddrRange)) (O_node (getnode node)) (O_internal_node (getinternal_node internal_node)) (defObj))
                   ((node (|node::next| Addr) (|node::nested_node| Addr)))
                   ((internal_node (|internal_node::next| Addr)))))
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
(declare-fun inv_main (Heap Addr) Bool)
(declare-fun inv_main2398_1_13 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main2400_5 (Heap Addr) Bool)
(declare-fun inv_main2400_5_14 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main2405_1_30 (Heap Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main2405_1_7 (Heap Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main2407_5 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main2407_5_21 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main2407_5_31 (Heap Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main2407_5_8 (Heap Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main2411_1 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main2411_1_18 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main2442_9_38 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main2457_9 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main2458_9_42 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main2465_5 (Heap) Bool)
(declare-fun inv_main2466_5_36 (Heap Addr Addr) Bool)
(declare-fun inv_main2467_5_40 (Heap Addr Addr) Bool)
(declare-fun inv_main_15 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main_17 (Heap Addr Addr) Bool)
(declare-fun inv_main_28 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main_37 (Heap Addr Addr) Bool)
(declare-fun inv_main_6 (Heap Addr Addr Addr Addr) Bool)
(assert (forall ((var0 Heap)) (or (not (= var0 emptyHeap)) (inv_main2465_5 var0))))
(assert (forall ((var0 Addr) (var1 node) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Int) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main2411_1 var10 var9 var8 var7) (and (and (and (and (not (= var6 0)) (and (is-O_node (read var10 var8)) (is-O_node (read var10 var8)))) (and (and (= var5 (write var10 var8 (O_node (node (|node::next| (getnode (read var10 var8))) var7)))) (= var4 var9)) (= var3 var8))) (= var2 (newHeap (alloc var5 (O_node var1))))) (= var0 (newAddr (alloc var5 (O_node var1))))))) (inv_main2400_5_14 var2 var4 var3 var0))))
(assert (forall ((var0 Addr) (var1 node) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Int) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main_17 var10 var9 var8) (and (and (and (not (= var7 0)) (and (is-O_node (read var10 var8)) (and (and (and (= var6 var10) (= var5 var9)) (= var4 var8)) (= var3 (|node::next| (getnode (read var10 var8))))))) (= var2 (newHeap (alloc var6 (O_node var1))))) (= var0 (newAddr (alloc var6 (O_node var1))))))) (inv_main2400_5_14 var2 var5 var3 var0))))
(assert (forall ((var0 Addr) (var1 internal_node) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap) (var9 Int) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Heap)) (or (not (and (inv_main_6 var14 var13 var12 var11 var10) (and (and (and (not (= var9 0)) (and (is-O_internal_node (read var14 var10)) (and (and (and (and (and (= var8 var14) (= var7 var13)) (= var6 var12)) (= var5 var11)) (= var4 var10)) (= var3 (|internal_node::next| (getinternal_node (read var14 var10))))))) (= var2 (newHeap (alloc var8 (O_internal_node var1))))) (= var0 (newAddr (alloc var8 (O_internal_node var1))))))) (inv_main2407_5_8 var2 var7 var6 var5 var3 var0))))
(assert (forall ((var0 Addr) (var1 internal_node) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Int) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Heap)) (or (not (and (inv_main2407_5 var11 var10 var9 var8) (and (and (and (not (= var7 0)) (and (and (is-O_internal_node (read var11 var8)) (is-O_internal_node (read var11 var8))) (and (and (and (= var6 (write var11 var8 (O_internal_node (internal_node nullAddr)))) (= var5 var10)) (= var4 var9)) (= var3 var8)))) (= var2 (newHeap (alloc var6 (O_internal_node var1))))) (= var0 (newAddr (alloc var6 (O_internal_node var1))))))) (inv_main2407_5_8 var2 var5 var4 var3 var3 var0))))
(assert (forall ((var0 Addr) (var1 internal_node) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap) (var9 Int) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Heap)) (or (not (and (inv_main_28 var14 var13 var12 var11 var10) (and (and (and (not (= var9 0)) (and (is-O_internal_node (read var14 var10)) (and (and (and (and (and (= var8 var14) (= var7 var13)) (= var6 var12)) (= var5 var11)) (= var4 var10)) (= var3 (|internal_node::next| (getinternal_node (read var14 var10))))))) (= var2 (newHeap (alloc var8 (O_internal_node var1))))) (= var0 (newAddr (alloc var8 (O_internal_node var1))))))) (inv_main2407_5_31 var2 var7 var6 var5 var3 var0))))
(assert (forall ((var0 Addr) (var1 internal_node) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Int) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Heap)) (or (not (and (inv_main2407_5_21 var11 var10 var9 var8) (and (and (and (not (= var7 0)) (and (and (is-O_internal_node (read var11 var8)) (is-O_internal_node (read var11 var8))) (and (and (and (= var6 (write var11 var8 (O_internal_node (internal_node nullAddr)))) (= var5 var10)) (= var4 var9)) (= var3 var8)))) (= var2 (newHeap (alloc var6 (O_internal_node var1))))) (= var0 (newAddr (alloc var6 (O_internal_node var1))))))) (inv_main2407_5_31 var2 var5 var4 var3 var3 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main2466_5_36 var6 var5 var4) (and (and (not (= var3 nullAddr)) (is-O_node (read var6 var4))) (and (and (and (= var2 var6) (= var1 var5)) (= var0 var4)) (= var3 (|node::nested_node| (getnode (read var6 var4)))))))) (inv_main2442_9_38 var2 var1 var0 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main2442_9_38 var8 var7 var6 var5) (and (not (= var4 nullAddr)) (and (is-O_internal_node (read var8 var5)) (and (and (and (and (= var3 var8) (= var2 var7)) (= var1 var6)) (= var0 var5)) (= var4 (|internal_node::next| (getinternal_node (read var8 var5))))))))) (inv_main2442_9_38 var3 var2 var1 var4))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Heap)) (or (not (and (inv_main2457_9 var12 var11 var10 var9) (and (not (= var8 nullAddr)) (and (and (and (= var7 nullAddr) (is-O_node (read var12 var10))) (and (and (and (and (= var6 var12) (= var5 var11)) (= var4 var10)) (= var3 var9)) (= var7 (|node::nested_node| (getnode (read var12 var10)))))) (and (and (and (= var2 (write var6 var4 defObj)) (= var1 var5)) (= var0 var4)) (= var8 var3)))))) (inv_main2467_5_40 var2 var1 var8))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Heap) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Heap)) (or (not (and (inv_main2458_9_42 var20 var19 var18 var17 var16) (and (not (= var15 nullAddr)) (and (and (= var14 nullAddr) (and (and (is-O_internal_node (read var20 var16)) (and (and (and (and (and (= var13 var20) (= var12 var19)) (= var11 var18)) (= var10 var17)) (= var9 var16)) (= var8 (|internal_node::next| (getinternal_node (read var20 var16)))))) (and (and (and (and (and (= var7 (write var13 var9 defObj)) (= var6 var12)) (= var5 var11)) (= var4 var10)) (= var3 var9)) (= var14 var8)))) (and (and (and (= var2 (write var7 var5 defObj)) (= var1 var6)) (= var0 var5)) (= var15 var4)))))) (inv_main2467_5_40 var2 var1 var15))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main_37 var6 var5 var4) (and (not (= var3 nullAddr)) (and (= var2 nullAddr) (and (is-O_node (read var6 var4)) (and (and (and (= var1 var6) (= var3 var5)) (= var0 var4)) (= var2 (|node::next| (getnode (read var6 var4)))))))))) (inv_main2467_5_40 var1 var3 var3))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main2411_1 var7 var6 var5 var4) (and (not (= var3 nullAddr)) (and (= var3 nullAddr) (and (and (= var2 0) (and (is-O_node (read var7 var5)) (is-O_node (read var7 var5)))) (and (and (= var1 (write var7 var5 (O_node (node (|node::next| (getnode (read var7 var5))) var4)))) (= var3 var6)) (= var0 var5))))))) (inv_main2467_5_40 var1 var3 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Int) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main_17 var7 var6 var5) (and (not (= var4 nullAddr)) (and (= var4 nullAddr) (and (= var3 0) (and (is-O_node (read var7 var5)) (and (and (and (= var2 var7) (= var4 var6)) (= var1 var5)) (= var0 (|node::next| (getnode (read var7 var5))))))))))) (inv_main2467_5_40 var2 var4 var4))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main2405_1_7 var6 var5 var4 var3 var2 var1) (and (and (is-O_internal_node (read var6 var2)) (is-O_internal_node (read var6 var2))) (= var0 (write var6 var2 (O_internal_node (internal_node var1))))))) (inv_main_6 var0 var5 var4 var3 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Int) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Heap)) (or (not (and (inv_main_6 var11 var10 var9 var8 var7) (and (= var6 0) (and (is-O_internal_node (read var11 var7)) (and (and (and (and (and (= var5 var11) (= var4 var10)) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var0 (|internal_node::next| (getinternal_node (read var11 var7))))))))) (inv_main2411_1 var5 var4 var3 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main2407_5 var8 var7 var6 var5) (and (= var4 0) (and (and (is-O_internal_node (read var8 var5)) (is-O_internal_node (read var8 var5))) (and (and (and (= var3 (write var8 var5 (O_internal_node (internal_node nullAddr)))) (= var2 var7)) (= var1 var6)) (= var0 var5)))))) (inv_main2411_1 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Heap)) (or (not (and (inv_main2407_5_8 var11 var10 var9 var8 var7 var6) (and (and (is-O_internal_node (read var11 var6)) (is-O_internal_node (read var11 var6))) (and (and (and (and (and (= var5 (write var11 var6 (O_internal_node (internal_node nullAddr)))) (= var4 var10)) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var0 var6))))) (inv_main2405_1_7 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 internal_node) (var2 Heap) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Heap)) (or (not (and (inv_main var6 var5) (and (and (and (and (is-O_node (read var6 var5)) (is-O_node (read var6 var5))) (and (= var4 (write var6 var5 (O_node (node (|node::next| (getnode (read var6 var5))) nullAddr)))) (= var3 var5))) (= var2 (newHeap (alloc var4 (O_internal_node var1))))) (= var0 (newAddr (alloc var4 (O_internal_node var1))))))) (inv_main2407_5 var2 var3 var3 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main2466_5_36 var6 var5 var4) (and (and (= var3 nullAddr) (is-O_node (read var6 var4))) (and (and (and (= var2 var6) (= var1 var5)) (= var0 var4)) (= var3 (|node::nested_node| (getnode (read var6 var4)))))))) (inv_main_37 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main2442_9_38 var8 var7 var6 var5) (and (= var4 nullAddr) (and (is-O_internal_node (read var8 var5)) (and (and (and (and (= var3 var8) (= var2 var7)) (= var1 var6)) (= var0 var5)) (= var4 (|internal_node::next| (getinternal_node (read var8 var5))))))))) (inv_main_37 var3 var2 var1))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main2411_1_18 var4 var3 var2 var1) (and (and (and (is-O_node (read var4 var2)) (is-O_node (read var4 (|node::next| (getnode (read var4 var2)))))) (is-O_node (read var4 (|node::next| (getnode (read var4 var2)))))) (= var0 (write var4 (|node::next| (getnode (read var4 var2))) (O_node (node (|node::next| (getnode (read var4 (|node::next| (getnode (read var4 var2)))))) var1))))))) (inv_main_17 var0 var3 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main_15 var7 var6 var5 var4) (and (and (is-O_node (read var7 var4)) (is-O_node (read var7 var4))) (and (and (and (= var3 (write var7 var4 (O_node (node (|node::next| (getnode (read var7 var4))) nullAddr)))) (= var2 var6)) (= var1 var5)) (= var0 var4))))) (inv_main2398_1_13 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main2467_5_40 var3 var2 var1) (and (is-O_node (read var3 var1)) (= var0 (|node::next| (getnode (read var3 var1))))))) (inv_main2457_9 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main2457_9 var8 var7 var6 var5) (and (and (not (= var4 nullAddr)) (is-O_node (read var8 var6))) (and (and (and (and (= var3 var8) (= var2 var7)) (= var1 var6)) (= var0 var5)) (= var4 (|node::nested_node| (getnode (read var8 var6)))))))) (inv_main2458_9_42 var3 var2 var1 var0 var4))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Heap)) (or (not (and (inv_main2458_9_42 var16 var15 var14 var13 var12) (and (not (= var11 nullAddr)) (and (and (is-O_internal_node (read var16 var12)) (and (and (and (and (and (= var10 var16) (= var9 var15)) (= var8 var14)) (= var7 var13)) (= var6 var12)) (= var5 (|internal_node::next| (getinternal_node (read var16 var12)))))) (and (and (and (and (and (= var4 (write var10 var6 defObj)) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var0 var6)) (= var11 var5)))))) (inv_main2458_9_42 var4 var3 var2 var1 var11))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main2400_5_14 var4 var3 var2 var1) (and (and (is-O_node (read var4 var1)) (is-O_node (read var4 var1))) (= var0 (write var4 var1 (O_node (node nullAddr (|node::nested_node| (getnode (read var4 var1)))))))))) (inv_main_15 var0 var3 var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Heap)) (or (not (and (inv_main2407_5_31 var11 var10 var9 var8 var7 var6) (and (and (is-O_internal_node (read var11 var6)) (is-O_internal_node (read var11 var6))) (and (and (and (and (and (= var5 (write var11 var6 (O_internal_node (internal_node nullAddr)))) (= var4 var10)) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var0 var6))))) (inv_main2405_1_30 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main_37 var6 var5 var4) (and (not (= var3 nullAddr)) (and (is-O_node (read var6 var4)) (and (and (and (= var2 var6) (= var1 var5)) (= var0 var4)) (= var3 (|node::next| (getnode (read var6 var4))))))))) (inv_main2466_5_36 var2 var1 var3))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main2411_1 var7 var6 var5 var4) (and (not (= var3 nullAddr)) (and (and (= var2 0) (and (is-O_node (read var7 var5)) (is-O_node (read var7 var5)))) (and (and (= var1 (write var7 var5 (O_node (node (|node::next| (getnode (read var7 var5))) var4)))) (= var3 var6)) (= var0 var5)))))) (inv_main2466_5_36 var1 var3 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Int) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main_17 var7 var6 var5) (and (not (= var4 nullAddr)) (and (= var3 0) (and (is-O_node (read var7 var5)) (and (and (and (= var2 var7) (= var4 var6)) (= var1 var5)) (= var0 (|node::next| (getnode (read var7 var5)))))))))) (inv_main2466_5_36 var2 var4 var4))))
(assert (forall ((var0 Addr) (var1 internal_node) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main2398_1_13 var9 var8 var7 var6) (and (and (and (and (is-O_node (read var9 var7)) (is-O_node (read var9 var7))) (and (and (= var5 (write var9 var7 (O_node (node var6 (|node::nested_node| (getnode (read var9 var7))))))) (= var4 var8)) (= var3 var7))) (= var2 (newHeap (alloc var5 (O_internal_node var1))))) (= var0 (newAddr (alloc var5 (O_internal_node var1))))))) (inv_main2407_5_21 var2 var4 var3 var0))))
(assert (forall ((var0 Addr) (var1 node) (var2 Heap) (var3 Heap)) (or (not (and (inv_main2465_5 var3) (and (= var2 (newHeap (alloc var3 (O_node var1)))) (= var0 (newAddr (alloc var3 (O_node var1))))))) (inv_main2400_5 var2 var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main2405_1_30 var6 var5 var4 var3 var2 var1) (and (and (is-O_internal_node (read var6 var2)) (is-O_internal_node (read var6 var2))) (= var0 (write var6 var2 (O_internal_node (internal_node var1))))))) (inv_main_28 var0 var5 var4 var3 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Int) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Heap)) (or (not (and (inv_main_28 var11 var10 var9 var8 var7) (and (= var6 0) (and (is-O_internal_node (read var11 var7)) (and (and (and (and (and (= var5 var11) (= var4 var10)) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var0 (|internal_node::next| (getinternal_node (read var11 var7))))))))) (inv_main2411_1_18 var5 var4 var3 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main2407_5_21 var8 var7 var6 var5) (and (= var4 0) (and (and (is-O_internal_node (read var8 var5)) (is-O_internal_node (read var8 var5))) (and (and (and (= var3 (write var8 var5 (O_internal_node (internal_node nullAddr)))) (= var2 var7)) (= var1 var6)) (= var0 var5)))))) (inv_main2411_1_18 var3 var2 var1 var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Heap)) (or (not (and (inv_main2400_5 var2 var1) (and (and (is-O_node (read var2 var1)) (is-O_node (read var2 var1))) (= var0 (write var2 var1 (O_node (node nullAddr (|node::nested_node| (getnode (read var2 var1)))))))))) (inv_main var0 var1))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main2400_5 var1 var0) (not (is-O_node (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main2400_5 var1 var0) (and (is-O_node (read var1 var0)) (not (is-O_node (read var1 var0))))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main var1 var0) (not (is-O_node (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main var1 var0) (and (is-O_node (read var1 var0)) (not (is-O_node (read var1 var0))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main2407_5 var3 var2 var1 var0) (not (is-O_internal_node (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main2407_5 var3 var2 var1 var0) (and (is-O_internal_node (read var3 var0)) (not (is-O_internal_node (read var3 var0))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (not (and (inv_main2407_5_8 var5 var4 var3 var2 var1 var0) (not (is-O_internal_node (read var5 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (not (and (inv_main2407_5_8 var5 var4 var3 var2 var1 var0) (and (is-O_internal_node (read var5 var0)) (not (is-O_internal_node (read var5 var0))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (not (and (inv_main2405_1_7 var5 var4 var3 var2 var1 var0) (not (is-O_internal_node (read var5 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (not (and (inv_main2405_1_7 var5 var4 var3 var2 var1 var0) (and (is-O_internal_node (read var5 var1)) (not (is-O_internal_node (read var5 var1))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main_6 var4 var3 var2 var1 var0) (not (is-O_internal_node (read var4 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main2411_1 var3 var2 var1 var0) (not (is-O_node (read var3 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main2411_1 var3 var2 var1 var0) (and (is-O_node (read var3 var1)) (not (is-O_node (read var3 var1))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main2400_5_14 var3 var2 var1 var0) (not (is-O_node (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main2400_5_14 var3 var2 var1 var0) (and (is-O_node (read var3 var0)) (not (is-O_node (read var3 var0))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_15 var3 var2 var1 var0) (not (is-O_node (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_15 var3 var2 var1 var0) (and (is-O_node (read var3 var0)) (not (is-O_node (read var3 var0))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main2398_1_13 var3 var2 var1 var0) (not (is-O_node (read var3 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main2398_1_13 var3 var2 var1 var0) (and (is-O_node (read var3 var1)) (not (is-O_node (read var3 var1))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main2407_5_21 var3 var2 var1 var0) (not (is-O_internal_node (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main2407_5_21 var3 var2 var1 var0) (and (is-O_internal_node (read var3 var0)) (not (is-O_internal_node (read var3 var0))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (not (and (inv_main2407_5_31 var5 var4 var3 var2 var1 var0) (not (is-O_internal_node (read var5 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (not (and (inv_main2407_5_31 var5 var4 var3 var2 var1 var0) (and (is-O_internal_node (read var5 var0)) (not (is-O_internal_node (read var5 var0))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (not (and (inv_main2405_1_30 var5 var4 var3 var2 var1 var0) (not (is-O_internal_node (read var5 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (not (and (inv_main2405_1_30 var5 var4 var3 var2 var1 var0) (and (is-O_internal_node (read var5 var1)) (not (is-O_internal_node (read var5 var1))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main_28 var4 var3 var2 var1 var0) (not (is-O_internal_node (read var4 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main2411_1_18 var3 var2 var1 var0) (not (is-O_node (read var3 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main2411_1_18 var3 var2 var1 var0) (and (is-O_node (read var3 var1)) (not (is-O_node (read var3 (|node::next| (getnode (read var3 var1)))))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main2411_1_18 var3 var2 var1 var0) (and (and (is-O_node (read var3 var1)) (is-O_node (read var3 (|node::next| (getnode (read var3 var1)))))) (not (is-O_node (read var3 (|node::next| (getnode (read var3 var1)))))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_17 var2 var1 var0) (not (is-O_node (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main2466_5_36 var2 var1 var0) (not (is-O_node (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main2442_9_38 var3 var2 var1 var0) (not (is-O_internal_node (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_37 var2 var1 var0) (not (is-O_node (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main2467_5_40 var2 var1 var0) (not (is-O_node (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main2457_9 var3 var2 var1 var0) (not (is-O_node (read var3 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main2458_9_42 var4 var3 var2 var1 var0) (not (is-O_internal_node (read var4 var0)))))))
(check-sat)
