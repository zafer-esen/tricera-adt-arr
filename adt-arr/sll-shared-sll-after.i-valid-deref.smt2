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

(declare-datatypes ((HeapObject 0) (internal_node 0) (sll 0))
                   (((O_Int (getInt Int)) (O_UInt (getUInt Int)) (O_Addr (getAddr Addr)) (O_AddrRange (getAddrRange AddrRange)) (O_internal_node (getinternal_node internal_node)) (O_sll (getsll sll)) (defObj))
                   ((internal_node (|internal_node::next| Addr)))
                   ((sll (|sll::next| Addr) (|sll::shared| Addr)))))
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
(declare-fun inv_main2399_1_5 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main2401_5 (Heap Addr) Bool)
(declare-fun inv_main2401_5_6 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main2406_1_14 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main2408_5 (Heap Addr Addr) Bool)
(declare-fun inv_main2408_5_15 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main2461_5 (Heap) Bool)
(declare-fun inv_main2463_5_18 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main2464_5_21 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main2465_5_24 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main_13 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main_17 (Heap Addr Addr) Bool)
(declare-fun inv_main_19 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main_4 (Heap Addr Addr) Bool)
(declare-fun inv_main_7 (Heap Addr Addr Addr) Bool)
(assert (forall ((var0 Heap)) (or (not (= var0 emptyHeap)) (inv_main2461_5 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main2408_5_15 var9 var8 var7 var6 var5) (and (and (is-O_internal_node (read var9 var5)) (is-O_internal_node (read var9 var5))) (and (and (and (and (= var4 (write var9 var5 (O_internal_node (internal_node nullAddr)))) (= var3 var8)) (= var2 var7)) (= var1 var6)) (= var0 var5))))) (inv_main2406_1_14 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 internal_node) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Int) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main_4 var10 var9 var8) (and (and (and (= var7 0) (and (is-O_sll (read var10 var8)) (and (and (and (= var6 var10) (= var5 var9)) (= var4 var8)) (= var3 (|sll::next| (getsll (read var10 var8))))))) (= var2 (newHeap (alloc var6 (O_internal_node var1))))) (= var0 (newAddr (alloc var6 (O_internal_node var1))))))) (inv_main2408_5 var2 var5 var0))))
(assert (forall ((var0 Addr) (var1 internal_node) (var2 Heap) (var3 Addr) (var4 Heap) (var5 Int) (var6 Addr) (var7 Heap)) (or (not (and (inv_main var7 var6) (and (and (and (= var5 0) (and (and (is-O_sll (read var7 var6)) (is-O_sll (read var7 var6))) (and (= var4 (write var7 var6 (O_sll (sll (|sll::next| (getsll (read var7 var6))) nullAddr)))) (= var3 var6)))) (= var2 (newHeap (alloc var4 (O_internal_node var1))))) (= var0 (newAddr (alloc var4 (O_internal_node var1))))))) (inv_main2408_5 var2 var3 var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main2401_5_6 var4 var3 var2 var1) (and (and (is-O_sll (read var4 var1)) (is-O_sll (read var4 var1))) (= var0 (write var4 var1 (O_sll (sll nullAddr (|sll::shared| (getsll (read var4 var1)))))))))) (inv_main_7 var0 var3 var2 var1))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main2406_1_14 var5 var4 var3 var2 var1) (and (and (is-O_internal_node (read var5 var2)) (is-O_internal_node (read var5 var2))) (= var0 (write var5 var2 (O_internal_node (internal_node var1))))))) (inv_main_13 var0 var4 var3 var2))))
(assert (forall ((var0 Addr) (var1 internal_node) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Int) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Heap)) (or (not (and (inv_main_13 var12 var11 var10 var9) (and (and (and (not (= var8 0)) (and (is-O_internal_node (read var12 var9)) (and (and (and (and (= var7 var12) (= var6 var11)) (= var5 var10)) (= var4 var9)) (= var3 (|internal_node::next| (getinternal_node (read var12 var9))))))) (= var2 (newHeap (alloc var7 (O_internal_node var1))))) (= var0 (newAddr (alloc var7 (O_internal_node var1))))))) (inv_main2408_5_15 var2 var6 var5 var3 var0))))
(assert (forall ((var0 Addr) (var1 internal_node) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Int) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main2408_5 var9 var8 var7) (and (and (and (not (= var6 0)) (and (and (is-O_internal_node (read var9 var7)) (is-O_internal_node (read var9 var7))) (and (and (= var5 (write var9 var7 (O_internal_node (internal_node nullAddr)))) (= var4 var8)) (= var3 var7)))) (= var2 (newHeap (alloc var5 (O_internal_node var1))))) (= var0 (newAddr (alloc var5 (O_internal_node var1))))))) (inv_main2408_5_15 var2 var4 var3 var3 var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main2399_1_5 var4 var3 var2 var1) (and (and (is-O_sll (read var4 var2)) (is-O_sll (read var4 var2))) (= var0 (write var4 var2 (O_sll (sll var1 (|sll::shared| (getsll (read var4 var2)))))))))) (inv_main_4 var0 var3 var2))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main2463_5_18 var5 var4 var3 var2 var1) (and (and (is-O_sll (read var5 var2)) (is-O_sll (read var5 var2))) (= var0 (write var5 var2 (O_sll (sll (|sll::next| (getsll (read var5 var2))) var1))))))) (inv_main_19 var0 var4 var3 var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main_19 var10 var9 var8 var7 var6) (and (= var5 nullAddr) (and (is-O_sll (read var10 var7)) (and (and (and (and (and (= var4 var10) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var0 var6)) (= var5 (|sll::next| (getsll (read var10 var7))))))))) (inv_main_17 var4 var3 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main_13 var9 var8 var7 var6) (and (= var5 nullAddr) (and (= var4 0) (and (is-O_internal_node (read var9 var6)) (and (and (and (and (= var3 var9) (= var5 var8)) (= var2 var7)) (= var1 var6)) (= var0 (|internal_node::next| (getinternal_node (read var9 var6)))))))))) (inv_main_17 var3 var5 var2))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main2408_5 var6 var5 var4) (and (= var3 nullAddr) (and (= var2 0) (and (and (is-O_internal_node (read var6 var4)) (is-O_internal_node (read var6 var4))) (and (and (= var1 (write var6 var4 (O_internal_node (internal_node nullAddr)))) (= var3 var5)) (= var0 var4))))))) (inv_main_17 var1 var3 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (and (inv_main_17 var2 var1 var0) (not (= var1 nullAddr)))) (inv_main2464_5_21 var2 var1 var0 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Heap)) (or (not (and (inv_main2464_5_21 var13 var12 var11 var10) (and (not (= var9 nullAddr)) (and (and (is-O_sll (read var13 var10)) (and (and (and (and (= var8 var13) (= var7 var12)) (= var6 var11)) (= var5 var10)) (= var4 (|sll::next| (getsll (read var13 var10)))))) (and (and (and (and (= var3 (write var8 var5 defObj)) (= var2 var7)) (= var1 var6)) (= var0 var5)) (= var9 var4)))))) (inv_main2464_5_21 var3 var2 var1 var9))))
(assert (forall ((var0 Addr) (var1 sll) (var2 Heap) (var3 Heap)) (or (not (and (inv_main2461_5 var3) (and (= var2 (newHeap (alloc var3 (O_sll var1)))) (= var0 (newAddr (alloc var3 (O_sll var1))))))) (inv_main2401_5 var2 var0))))
(assert (forall ((var0 Addr) (var1 sll) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Int) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main_4 var10 var9 var8) (and (and (and (not (= var7 0)) (and (is-O_sll (read var10 var8)) (and (and (and (= var6 var10) (= var5 var9)) (= var4 var8)) (= var3 (|sll::next| (getsll (read var10 var8))))))) (= var2 (newHeap (alloc var6 (O_sll var1))))) (= var0 (newAddr (alloc var6 (O_sll var1))))))) (inv_main2401_5_6 var2 var5 var3 var0))))
(assert (forall ((var0 Addr) (var1 sll) (var2 Heap) (var3 Addr) (var4 Heap) (var5 Int) (var6 Addr) (var7 Heap)) (or (not (and (inv_main var7 var6) (and (and (and (not (= var5 0)) (and (and (is-O_sll (read var7 var6)) (is-O_sll (read var7 var6))) (and (= var4 (write var7 var6 (O_sll (sll (|sll::next| (getsll (read var7 var6))) nullAddr)))) (= var3 var6)))) (= var2 (newHeap (alloc var4 (O_sll var1))))) (= var0 (newAddr (alloc var4 (O_sll var1))))))) (inv_main2401_5_6 var2 var3 var3 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Heap)) (or (not (and (inv_main2465_5_24 var13 var12 var11 var10) (and (not (= var9 nullAddr)) (and (and (is-O_internal_node (read var13 var10)) (and (and (and (and (= var8 var13) (= var7 var12)) (= var6 var11)) (= var5 var10)) (= var4 (|internal_node::next| (getinternal_node (read var13 var10)))))) (and (and (and (and (= var3 (write var8 var5 defObj)) (= var2 var7)) (= var1 var6)) (= var0 var5)) (= var9 var4)))))) (inv_main2465_5_24 var3 var2 var1 var9))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (and (inv_main_17 var2 var1 var0) (and (not (= var0 nullAddr)) (= var1 nullAddr)))) (inv_main2465_5_24 var2 var1 var0 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Heap)) (or (not (and (inv_main2464_5_21 var13 var12 var11 var10) (and (not (= var9 nullAddr)) (and (= var8 nullAddr) (and (and (is-O_sll (read var13 var10)) (and (and (and (and (= var7 var13) (= var6 var12)) (= var5 var11)) (= var4 var10)) (= var3 (|sll::next| (getsll (read var13 var10)))))) (and (and (and (and (= var2 (write var7 var4 defObj)) (= var1 var6)) (= var9 var5)) (= var0 var4)) (= var8 var3))))))) (inv_main2465_5_24 var2 var1 var9 var9))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main_7 var7 var6 var5 var4) (and (and (is-O_sll (read var7 var4)) (is-O_sll (read var7 var4))) (and (and (and (= var3 (write var7 var4 (O_sll (sll (|sll::next| (getsll (read var7 var4))) nullAddr)))) (= var2 var6)) (= var1 var5)) (= var0 var4))))) (inv_main2399_1_5 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main_19 var10 var9 var8 var7 var6) (and (not (= var5 nullAddr)) (and (is-O_sll (read var10 var7)) (and (and (and (and (and (= var4 var10) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var0 var6)) (= var5 (|sll::next| (getsll (read var10 var7))))))))) (inv_main2463_5_18 var4 var3 var2 var5 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main_13 var9 var8 var7 var6) (and (not (= var5 nullAddr)) (and (= var4 0) (and (is-O_internal_node (read var9 var6)) (and (and (and (and (= var3 var9) (= var5 var8)) (= var2 var7)) (= var1 var6)) (= var0 (|internal_node::next| (getinternal_node (read var9 var6)))))))))) (inv_main2463_5_18 var3 var5 var2 var5 var2))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main2408_5 var6 var5 var4) (and (not (= var3 nullAddr)) (and (= var2 0) (and (and (is-O_internal_node (read var6 var4)) (is-O_internal_node (read var6 var4))) (and (and (= var1 (write var6 var4 (O_internal_node (internal_node nullAddr)))) (= var3 var5)) (= var0 var4))))))) (inv_main2463_5_18 var1 var3 var0 var3 var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Heap)) (or (not (and (inv_main2401_5 var2 var1) (and (and (is-O_sll (read var2 var1)) (is-O_sll (read var2 var1))) (= var0 (write var2 var1 (O_sll (sll nullAddr (|sll::shared| (getsll (read var2 var1)))))))))) (inv_main var0 var1))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main2401_5 var1 var0) (not (is-O_sll (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main2401_5 var1 var0) (and (is-O_sll (read var1 var0)) (not (is-O_sll (read var1 var0))))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main var1 var0) (not (is-O_sll (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main var1 var0) (and (is-O_sll (read var1 var0)) (not (is-O_sll (read var1 var0))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main2401_5_6 var3 var2 var1 var0) (not (is-O_sll (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main2401_5_6 var3 var2 var1 var0) (and (is-O_sll (read var3 var0)) (not (is-O_sll (read var3 var0))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_7 var3 var2 var1 var0) (not (is-O_sll (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_7 var3 var2 var1 var0) (and (is-O_sll (read var3 var0)) (not (is-O_sll (read var3 var0))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main2399_1_5 var3 var2 var1 var0) (not (is-O_sll (read var3 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main2399_1_5 var3 var2 var1 var0) (and (is-O_sll (read var3 var1)) (not (is-O_sll (read var3 var1))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_4 var2 var1 var0) (not (is-O_sll (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main2408_5 var2 var1 var0) (not (is-O_internal_node (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main2408_5 var2 var1 var0) (and (is-O_internal_node (read var2 var0)) (not (is-O_internal_node (read var2 var0))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main2408_5_15 var4 var3 var2 var1 var0) (not (is-O_internal_node (read var4 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main2408_5_15 var4 var3 var2 var1 var0) (and (is-O_internal_node (read var4 var0)) (not (is-O_internal_node (read var4 var0))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main2406_1_14 var4 var3 var2 var1 var0) (not (is-O_internal_node (read var4 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main2406_1_14 var4 var3 var2 var1 var0) (and (is-O_internal_node (read var4 var1)) (not (is-O_internal_node (read var4 var1))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_13 var3 var2 var1 var0) (not (is-O_internal_node (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main2463_5_18 var4 var3 var2 var1 var0) (not (is-O_sll (read var4 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main2463_5_18 var4 var3 var2 var1 var0) (and (is-O_sll (read var4 var1)) (not (is-O_sll (read var4 var1))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main_19 var4 var3 var2 var1 var0) (not (is-O_sll (read var4 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main2464_5_21 var3 var2 var1 var0) (not (is-O_sll (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main2465_5_24 var3 var2 var1 var0) (not (is-O_internal_node (read var3 var0)))))))
(check-sat)