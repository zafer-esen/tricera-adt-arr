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
(declare-fun inv_main2415_5 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main2443_9 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main2453_9 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main2459_5 (Heap) Bool)
(declare-fun inv_main2460_5 (Heap Addr Addr) Bool)
(declare-fun inv_main_9 (Heap Addr Addr Addr) Bool)
(assert (forall ((var0 Heap)) (or (not (= var0 emptyHeap)) (inv_main2459_5 var0))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main2415_5 var6 var5 var4 var3 var2) (and (= var1 0) (= var0 (write var6 var4 (O_sll (sll (|sll::next| (getsll (read var6 var4))) var3))))))) (inv_main_9 var0 var5 var4 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Heap) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr) (var19 sll) (var20 Heap) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Addr) (var25 Addr) (var26 Addr) (var27 Addr) (var28 Heap) (var29 Heap) (var30 Addr) (var31 Addr) (var32 Addr) (var33 Heap)) (or (not (and (inv_main_9 var33 var32 var31 var30) (and (and (and (and (and (and (= var29 var28) (= var27 var26)) (= var25 var24)) (= var23 var22)) (= var21 (|sll::next| (getsll (read var28 var24))))) (and (and (and (and (and (and (and (and (= var20 (newHeap (alloc var33 (O_sll var19)))) (= var18 var32)) (= var17 var31)) (= var16 var30)) (= var15 (newAddr (alloc var33 (O_sll var19))))) (and (and (and (and (= var14 (write var20 var15 (O_sll (sll nullAddr (|sll::shared| (getsll (read var20 var15))))))) (= var13 var18)) (= var12 var17)) (= var11 var16)) (= var10 var15))) (and (and (and (and (= var9 (write var14 var10 (O_sll (sll (|sll::next| (getsll (read var14 var10))) nullAddr)))) (= var8 var13)) (= var7 var12)) (= var6 var11)) (= var5 var10))) (not (= var4 0))) (and (and (and (= var3 (write var9 var7 (O_sll (sll var5 (|sll::shared| (getsll (read var9 var7))))))) (= var2 var8)) (= var1 var7)) (= var0 var6)))) (and (and (and (= var28 (write var3 (|sll::next| (getsll (read var3 var1))) (O_sll (sll (|sll::next| (getsll (read var3 (|sll::next| (getsll (read var3 var1)))))) var0)))) (= var26 var2)) (= var24 var1)) (= var22 var0))))) (inv_main_9 var29 var27 var21 var23))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main2453_9 var8 var7 var6 var5) (and (and (not (= var4 nullAddr)) (and (and (and (= var3 (write var8 var6 defObj)) (= var2 var7)) (= var1 var6)) (= var4 var5))) (= var0 (|sll::next| (getsll (read var3 var4))))))) (inv_main2453_9 var3 var2 var4 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main2443_9 var10 var9 var8 var7 var6) (and (and (not (= var5 nullAddr)) (and (= var4 nullAddr) (and (and (and (and (= var3 (write var10 var7 defObj)) (= var2 var9)) (= var5 var8)) (= var1 var7)) (= var4 var6)))) (= var0 (|sll::next| (getsll (read var3 var5))))))) (inv_main2453_9 var3 var2 var5 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main2460_5 var3 var2 var1) (and (and (not (= var2 nullAddr)) (and (= var2 nullAddr) (= var1 nullAddr))) (= var0 (|sll::next| (getsll (read var3 var2))))))) (inv_main2453_9 var3 var2 var2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main2460_5 var7 var6 var5) (and (and (not (= var4 nullAddr)) (and (and (and (= var3 nullAddr) (and (and (and (= var2 var7) (= var1 var6)) (= var4 var6)) (= var3 (|sll::shared| (getsll (read var7 var6)))))) (not (= var6 nullAddr))) (= var5 nullAddr))) (= var0 (|sll::next| (getsll (read var2 var4))))))) (inv_main2453_9 var2 var1 var4 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 internal_node) (var13 Heap) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Heap) (var24 Heap) (var25 Addr) (var26 Addr) (var27 Addr) (var28 Addr) (var29 Heap)) (or (not (and (inv_main2415_5 var29 var28 var27 var26 var25) (and (and (and (and (and (and (and (= var24 var23) (= var22 var21)) (= var20 var19)) (= var18 var17)) (= var16 var15)) (= var14 (|internal_node::next| (getinternal_node (read var23 var15))))) (and (and (and (and (and (and (and (= var13 (newHeap (alloc var29 (O_internal_node var12)))) (= var11 var28)) (= var10 var27)) (= var9 var26)) (= var8 var25)) (= var7 (newAddr (alloc var29 (O_internal_node var12))))) (and (and (and (and (and (= var6 (write var13 var7 (O_internal_node (internal_node nullAddr)))) (= var5 var11)) (= var4 var10)) (= var3 var9)) (= var2 var8)) (= var1 var7))) (not (= var0 0)))) (and (and (and (and (= var23 (write var6 var2 (O_internal_node (internal_node var1)))) (= var21 var5)) (= var19 var4)) (= var17 var3)) (= var15 var2))))) (inv_main2415_5 var24 var22 var20 var18 var14))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 sll) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 internal_node) (var14 Heap) (var15 Heap) (var16 Heap)) (or (not (and (inv_main2459_5 var16) (and (and (and (and (and (= var15 (newHeap (alloc var14 (O_internal_node var13)))) (= var12 var11)) (= var10 var11)) (= var9 (newAddr (alloc var14 (O_internal_node var13))))) (and (and (and (= var8 (write var15 var9 (O_internal_node (internal_node nullAddr)))) (= var7 var12)) (= var6 var10)) (= var5 var9))) (and (and (and (= var4 (newHeap (alloc var16 (O_sll var3)))) (= var2 (newAddr (alloc var16 (O_sll var3))))) (and (= var1 (write var4 var2 (O_sll (sll nullAddr (|sll::shared| (getsll (read var4 var2))))))) (= var0 var2))) (and (= var14 (write var1 var0 (O_sll (sll (|sll::next| (getsll (read var1 var0))) nullAddr)))) (= var11 var0)))))) (inv_main2415_5 var8 var7 var6 var5 var5))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main2460_5 var6 var5 var4) (and (and (and (and (= var3 var6) (= var2 var5)) (= var1 var4)) (= var0 (|sll::next| (getsll (read var6 var4))))) (not (= var4 nullAddr))))) (inv_main2460_5 var3 var2 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main_9 var4 var3 var2 var1) (= var0 0))) (inv_main2460_5 var4 var3 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main2443_9 var10 var9 var8 var7 var6) (and (and (not (= var5 nullAddr)) (and (and (and (and (= var4 (write var10 var7 defObj)) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var5 var6))) (= var0 (|internal_node::next| (getinternal_node (read var4 var5))))))) (inv_main2443_9 var4 var3 var2 var5 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main2460_5 var7 var6 var5) (and (and (and (and (not (= var4 nullAddr)) (and (and (and (= var3 var7) (= var2 var6)) (= var1 var6)) (= var4 (|sll::shared| (getsll (read var7 var6)))))) (not (= var6 nullAddr))) (= var5 nullAddr)) (= var0 (|internal_node::next| (getinternal_node (read var3 var4))))))) (inv_main2443_9 var3 var2 var1 var4 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main2443_9 var4 var3 var2 var1 var0) (and (not (= var1 nullAddr)) (= (read var4 var1) defObj))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main2453_9 var3 var2 var1 var0) (and (not (= var1 nullAddr)) (= (read var3 var1) defObj))))))
(check-sat)
