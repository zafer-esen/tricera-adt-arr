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
(declare-fun inv_main2415_5 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main2425_5 (Heap Addr Addr) Bool)
(declare-fun inv_main2442_9 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main2450_9 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main2461_5 (Heap) Bool)
(declare-fun inv_main2463_5 (Heap Addr Addr Addr Addr) Bool)
(assert (forall ((var0 Heap)) (or (not (= var0 emptyHeap)) (inv_main2461_5 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 internal_node) (var11 Heap) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Heap) (var20 Heap) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Heap)) (or (not (and (inv_main2415_5 var24 var23 var22 var21) (and (and (and (and (and (and (= var20 var19) (= var18 var17)) (= var16 var15)) (= var14 var13)) (= var12 (|internal_node::next| (getinternal_node (read var19 var13))))) (and (and (and (and (and (and (= var11 (newHeap (alloc var24 (O_internal_node var10)))) (= var9 var23)) (= var8 var22)) (= var7 var21)) (= var6 (newAddr (alloc var24 (O_internal_node var10))))) (and (and (and (and (= var5 (write var11 var6 (O_internal_node (internal_node nullAddr)))) (= var4 var9)) (= var3 var8)) (= var2 var7)) (= var1 var6))) (not (= var0 0)))) (and (and (and (= var19 (write var5 var2 (O_internal_node (internal_node var1)))) (= var17 var4)) (= var15 var3)) (= var13 var2))))) (inv_main2415_5 var20 var18 var16 var12))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 internal_node) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main2425_5 var10 var9 var8) (and (and (and (and (= var7 (newHeap (alloc var10 (O_internal_node var6)))) (= var5 var9)) (= var4 (newAddr (alloc var10 (O_internal_node var6))))) (and (and (= var3 (write var7 var4 (O_internal_node (internal_node nullAddr)))) (= var2 var5)) (= var1 var4))) (= var0 0)))) (inv_main2415_5 var3 var2 var1 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Addr) (var12 sll) (var13 Heap) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Heap) (var20 Heap) (var21 Addr) (var22 Addr) (var23 Heap)) (or (not (and (inv_main2425_5 var23 var22 var21) (and (and (and (and (and (= var20 var19) (= var18 var17)) (= var16 var15)) (= var14 (|sll::next| (getsll (read var19 var15))))) (and (and (and (and (and (and (= var13 (newHeap (alloc var23 (O_sll var12)))) (= var11 var22)) (= var10 var21)) (= var9 (newAddr (alloc var23 (O_sll var12))))) (and (and (and (= var8 (write var13 var9 (O_sll (sll nullAddr (|sll::shared| (getsll (read var13 var9))))))) (= var7 var11)) (= var6 var10)) (= var5 var9))) (and (and (and (= var4 (write var8 var5 (O_sll (sll (|sll::next| (getsll (read var8 var5))) nullAddr)))) (= var3 var7)) (= var2 var6)) (= var1 var5))) (not (= var0 0)))) (and (and (= var19 (write var4 var2 (O_sll (sll var1 (|sll::shared| (getsll (read var4 var2))))))) (= var17 var3)) (= var15 var2))))) (inv_main2425_5 var20 var18 var14))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Heap) (var4 Addr) (var5 sll) (var6 Heap) (var7 Heap)) (or (not (and (inv_main2461_5 var7) (and (and (and (= var6 (newHeap (alloc var7 (O_sll var5)))) (= var4 (newAddr (alloc var7 (O_sll var5))))) (and (= var3 (write var6 var4 (O_sll (sll nullAddr (|sll::shared| (getsll (read var6 var4))))))) (= var2 var4))) (and (= var1 (write var3 var2 (O_sll (sll (|sll::next| (getsll (read var3 var2))) nullAddr)))) (= var0 var2))))) (inv_main2425_5 var1 var0 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main2450_9 var10 var9 var8 var7 var6) (and (and (not (= var5 nullAddr)) (and (and (and (and (= var4 (write var10 var7 defObj)) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var5 var6))) (= var0 (|sll::next| (getsll (read var4 var5))))))) (inv_main2450_9 var4 var3 var2 var5 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main2463_5 var5 var4 var3 var2 var1) (and (and (not (= var4 nullAddr)) (= var2 nullAddr)) (= var0 (|sll::next| (getsll (read var5 var4))))))) (inv_main2450_9 var5 var4 var3 var4 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap) (var10 Heap) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Heap)) (or (not (and (inv_main2463_5 var15 var14 var13 var12 var11) (and (and (and (and (and (and (and (= var10 var9) (= var8 var7)) (= var6 var5)) (= var4 var3)) (= var2 var1)) (= var0 (|sll::next| (getsll (read var9 var3))))) (not (= var12 nullAddr))) (and (and (and (and (= var9 (write var15 var12 (O_sll (sll (|sll::next| (getsll (read var15 var12))) var11)))) (= var7 var14)) (= var5 var13)) (= var3 var12)) (= var1 var11))))) (inv_main2463_5 var10 var8 var6 var0 var2))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main2415_5 var4 var3 var2 var1) (= var0 0))) (inv_main2463_5 var4 var3 var2 var3 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main2442_9 var10 var9 var8 var7 var6) (and (and (not (= var5 nullAddr)) (and (and (and (and (= var4 (write var10 var7 defObj)) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var5 var6))) (= var0 (|internal_node::next| (getinternal_node (read var4 var5))))))) (inv_main2442_9 var4 var3 var2 var5 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main2450_9 var10 var9 var8 var7 var6) (and (and (not (= var5 nullAddr)) (and (= var4 nullAddr) (and (and (and (and (= var3 (write var10 var7 defObj)) (= var2 var9)) (= var5 var8)) (= var1 var7)) (= var4 var6)))) (= var0 (|internal_node::next| (getinternal_node (read var3 var5))))))) (inv_main2442_9 var3 var2 var5 var5 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main2463_5 var5 var4 var3 var2 var1) (and (and (not (= var3 nullAddr)) (and (= var4 nullAddr) (= var2 nullAddr))) (= var0 (|internal_node::next| (getinternal_node (read var5 var3))))))) (inv_main2442_9 var5 var4 var3 var3 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main2450_9 var4 var3 var2 var1 var0) (and (not (= var1 nullAddr)) (= (read var4 var1) defObj))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main2442_9 var4 var3 var2 var1 var0) (and (not (= var1 nullAddr)) (= (read var4 var1) defObj))))))
(check-sat)
