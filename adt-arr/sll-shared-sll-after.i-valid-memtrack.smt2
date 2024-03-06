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
(declare-fun inv_main2415_5 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main2425_5 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main2461_5 (Heap Addr) Bool)
(declare-fun inv_main2463_5 (Heap Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main2464_5 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main2465_5 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main2466_12 (Heap Addr Int) Bool)
(assert (forall ((var0 Addr) (var1 Heap)) (or (not (and (= var1 emptyHeap) (= var0 nullAddr))) (inv_main2461_5 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main2465_5 var5 var4 var3 var2 var1) (and (= var1 nullAddr) (= var0 0)))) (inv_main2466_12 var5 var4 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Heap) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Heap)) (or (not (and (inv_main2465_5 var16 var15 var14 var13 var12) (and (and (and (and (and (and (and (= var11 var16) (= var10 var15)) (= var9 var14)) (= var8 var13)) (= var7 var12)) (= var6 (|internal_node::next| (getinternal_node (read var16 var12))))) (and (and (and (and (and (= var5 (write var11 var7 defObj)) (or (and (= var10 var7) (= var4 nullAddr)) (and (not (= var10 var7)) (= var4 var10)))) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var0 var6))) (not (= var12 nullAddr))))) (inv_main2465_5 var5 var4 var3 var2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main2464_5 var4 var3 var2 var1 var0) (= var0 nullAddr))) (inv_main2465_5 var4 var3 var2 var1 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Bool) (var15 Addr) (var16 sll) (var17 Heap) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Addr) (var25 Heap) (var26 Heap) (var27 Addr) (var28 Addr) (var29 Addr) (var30 Heap)) (or (not (and (inv_main2425_5 var30 var29 var28 var27) (and (and (and (and (and (and (= var26 var25) (= var24 var23)) (= var22 var21)) (= var20 var19)) (= var18 (|sll::next| (getsll (read var25 var19))))) (and (and (and (and (and (and (and (= var17 (newHeap (alloc var30 (O_sll var16)))) (or (and var14 (= var15 (newAddr (alloc var30 (O_sll var16))))) (and (not var14) (= var15 var29)))) (= var13 var28)) (= var12 var27)) (= var11 (newAddr (alloc var30 (O_sll var16))))) (and (and (and (and (= var10 (write var17 var11 (O_sll (sll nullAddr (|sll::shared| (getsll (read var17 var11))))))) (= var9 var15)) (= var8 var13)) (= var7 var12)) (= var6 var11))) (and (and (and (and (= var5 (write var10 var6 (O_sll (sll (|sll::next| (getsll (read var10 var6))) nullAddr)))) (= var4 var9)) (= var3 var8)) (= var2 var7)) (= var1 var6))) (not (= var0 0)))) (and (and (and (= var25 (write var5 var2 (O_sll (sll var1 (|sll::shared| (getsll (read var5 var2))))))) (= var23 var4)) (= var21 var3)) (= var19 var2))))) (inv_main2425_5 var26 var24 var22 var18))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Bool) (var8 Addr) (var9 sll) (var10 Heap) (var11 Addr) (var12 Heap)) (or (not (and (inv_main2461_5 var12 var11) (and (and (and (and (= var10 (newHeap (alloc var12 (O_sll var9)))) (or (and var7 (= var8 (newAddr (alloc var12 (O_sll var9))))) (and (not var7) (= var8 var11)))) (= var6 (newAddr (alloc var12 (O_sll var9))))) (and (and (= var5 (write var10 var6 (O_sll (sll nullAddr (|sll::shared| (getsll (read var10 var6))))))) (= var4 var8)) (= var3 var6))) (and (and (= var2 (write var5 var3 (O_sll (sll (|sll::next| (getsll (read var5 var3))) nullAddr)))) (= var1 var4)) (= var0 var3))))) (inv_main2425_5 var2 var1 var0 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Bool) (var12 Addr) (var13 internal_node) (var14 Heap) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Heap) (var25 Heap) (var26 Addr) (var27 Addr) (var28 Addr) (var29 Addr) (var30 Heap)) (or (not (and (inv_main2415_5 var30 var29 var28 var27 var26) (and (and (and (and (and (and (and (= var25 var24) (= var23 var22)) (= var21 var20)) (= var19 var18)) (= var17 var16)) (= var15 (|internal_node::next| (getinternal_node (read var24 var16))))) (and (and (and (and (and (and (and (= var14 (newHeap (alloc var30 (O_internal_node var13)))) (or (and var11 (= var12 (newAddr (alloc var30 (O_internal_node var13))))) (and (not var11) (= var12 var29)))) (= var10 var28)) (= var9 var27)) (= var8 var26)) (= var7 (newAddr (alloc var30 (O_internal_node var13))))) (and (and (and (and (and (= var6 (write var14 var7 (O_internal_node (internal_node nullAddr)))) (= var5 var12)) (= var4 var10)) (= var3 var9)) (= var2 var8)) (= var1 var7))) (not (= var0 0)))) (and (and (and (and (= var24 (write var6 var2 (O_internal_node (internal_node var1)))) (= var22 var5)) (= var20 var4)) (= var18 var3)) (= var16 var2))))) (inv_main2415_5 var25 var23 var21 var19 var15))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Bool) (var8 Addr) (var9 internal_node) (var10 Heap) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Heap)) (or (not (and (inv_main2425_5 var14 var13 var12 var11) (and (and (and (and (and (= var10 (newHeap (alloc var14 (O_internal_node var9)))) (or (and var7 (= var8 (newAddr (alloc var14 (O_internal_node var9))))) (and (not var7) (= var8 var13)))) (= var6 var12)) (= var5 (newAddr (alloc var14 (O_internal_node var9))))) (and (and (and (= var4 (write var10 var5 (O_internal_node (internal_node nullAddr)))) (= var3 var8)) (= var2 var6)) (= var1 var5))) (= var0 0)))) (inv_main2415_5 var4 var3 var2 var1 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Heap) (var12 Heap) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Heap)) (or (not (and (inv_main2463_5 var18 var17 var16 var15 var14 var13) (and (and (and (and (and (and (and (and (= var12 var11) (= var10 var9)) (= var8 var7)) (= var6 var5)) (= var4 var3)) (= var2 var1)) (= var0 (|sll::next| (getsll (read var11 var3))))) (not (= var14 nullAddr))) (and (and (and (and (and (= var11 (write var18 var14 (O_sll (sll (|sll::next| (getsll (read var18 var14))) var13)))) (= var9 var17)) (= var7 var16)) (= var5 var15)) (= var3 var14)) (= var1 var13))))) (inv_main2463_5 var12 var10 var8 var6 var0 var2))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main2415_5 var5 var4 var3 var2 var1) (= var0 0))) (inv_main2463_5 var5 var4 var3 var2 var3 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Heap) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Heap)) (or (not (and (inv_main2464_5 var16 var15 var14 var13 var12) (and (and (and (and (and (and (and (= var11 var16) (= var10 var15)) (= var9 var14)) (= var8 var13)) (= var7 var12)) (= var6 (|sll::next| (getsll (read var16 var12))))) (and (and (and (and (and (= var5 (write var11 var7 defObj)) (or (and (= var10 var7) (= var4 nullAddr)) (and (not (= var10 var7)) (= var4 var10)))) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var0 var6))) (not (= var12 nullAddr))))) (inv_main2464_5 var5 var4 var3 var2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main2463_5 var5 var4 var3 var2 var1 var0) (= var1 nullAddr))) (inv_main2464_5 var5 var4 var3 var2 var3))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap)) (not (and (inv_main2466_12 var2 var1 var0) (not (= var1 nullAddr))))))
(check-sat)
