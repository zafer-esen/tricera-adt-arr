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
(declare-fun inv_main2415_5 (Heap Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main2451_9 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main2459_5 (Heap Addr) Bool)
(declare-fun inv_main2460_5 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main2462_12 (Heap Addr Int) Bool)
(declare-fun inv_main_22 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main_9 (Heap Addr Addr Addr Addr) Bool)
(assert (forall ((var0 Addr) (var1 Heap)) (or (not (and (= var1 emptyHeap) (= var0 nullAddr))) (inv_main2459_5 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main_22 var4 var3 var2 var1) (and (= var1 nullAddr) (= var0 0)))) (inv_main2462_12 var4 var3 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main2451_9 var4 var3 var2 var1 var0) (= var0 nullAddr))) (inv_main_22 var4 var3 var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Heap)) (or (not (and (inv_main_22 var13 var12 var11 var10) (and (and (and (and (and (and (= var9 var13) (= var8 var12)) (= var7 var11)) (= var6 var10)) (= var5 (|sll::next| (getsll (read var13 var10))))) (and (and (and (and (= var4 (write var9 var6 defObj)) (or (and (= var8 var6) (= var3 nullAddr)) (and (not (= var8 var6)) (= var3 var8)))) (= var2 var7)) (= var1 var6)) (= var0 var5))) (not (= var10 nullAddr))))) (inv_main_22 var4 var3 var2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main2460_5 var3 var2 var1 var0) (and (= var1 nullAddr) (= var0 nullAddr)))) (inv_main_22 var3 var2 var1 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Heap) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Heap)) (or (not (and (inv_main2451_9 var16 var15 var14 var13 var12) (and (and (and (and (and (and (and (= var11 var16) (= var10 var15)) (= var9 var14)) (= var8 var13)) (= var7 var12)) (= var6 (|internal_node::next| (getinternal_node (read var16 var12))))) (and (and (and (and (and (= var5 (write var11 var7 defObj)) (or (and (= var10 var7) (= var4 nullAddr)) (and (not (= var10 var7)) (= var4 var10)))) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var0 var6))) (not (= var12 nullAddr))))) (inv_main2451_9 var5 var4 var3 var2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main2460_5 var4 var3 var2 var1) (and (and (not (= var2 nullAddr)) (= var1 nullAddr)) (= var0 (|sll::shared| (getsll (read var4 var2))))))) (inv_main2451_9 var4 var3 var2 var2 var0))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main2415_5 var7 var6 var5 var4 var3 var2) (and (= var1 0) (= var0 (write var7 var4 (O_sll (sll (|sll::next| (getsll (read var7 var4))) var3))))))) (inv_main_9 var0 var6 var5 var4 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Int) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Heap) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Heap) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Bool) (var23 Addr) (var24 sll) (var25 Heap) (var26 Addr) (var27 Addr) (var28 Addr) (var29 Addr) (var30 Addr) (var31 Addr) (var32 Addr) (var33 Addr) (var34 Addr) (var35 Heap) (var36 Heap) (var37 Addr) (var38 Addr) (var39 Addr) (var40 Addr) (var41 Heap)) (or (not (and (inv_main_9 var41 var40 var39 var38 var37) (and (and (and (and (and (and (and (= var36 var35) (= var34 var33)) (= var32 var31)) (= var30 var29)) (= var28 var27)) (= var26 (|sll::next| (getsll (read var35 var29))))) (and (and (and (and (and (and (and (and (and (= var25 (newHeap (alloc var41 (O_sll var24)))) (or (and var22 (= var23 (newAddr (alloc var41 (O_sll var24))))) (and (not var22) (= var23 var40)))) (= var21 var39)) (= var20 var38)) (= var19 var37)) (= var18 (newAddr (alloc var41 (O_sll var24))))) (and (and (and (and (and (= var17 (write var25 var18 (O_sll (sll nullAddr (|sll::shared| (getsll (read var25 var18))))))) (= var16 var23)) (= var15 var21)) (= var14 var20)) (= var13 var19)) (= var12 var18))) (and (and (and (and (and (= var11 (write var17 var12 (O_sll (sll (|sll::next| (getsll (read var17 var12))) nullAddr)))) (= var10 var16)) (= var9 var15)) (= var8 var14)) (= var7 var13)) (= var6 var12))) (not (= var5 0))) (and (and (and (and (= var4 (write var11 var8 (O_sll (sll var6 (|sll::shared| (getsll (read var11 var8))))))) (= var3 var10)) (= var2 var9)) (= var1 var8)) (= var0 var7)))) (and (and (and (and (= var35 (write var4 (|sll::next| (getsll (read var4 var1))) (O_sll (sll (|sll::next| (getsll (read var4 (|sll::next| (getsll (read var4 var1)))))) var0)))) (= var33 var3)) (= var31 var2)) (= var29 var1)) (= var27 var0))))) (inv_main_9 var36 var34 var32 var26 var28))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Bool) (var14 Addr) (var15 internal_node) (var16 Heap) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Addr) (var25 Addr) (var26 Addr) (var27 Addr) (var28 Heap) (var29 Heap) (var30 Addr) (var31 Addr) (var32 Addr) (var33 Addr) (var34 Addr) (var35 Heap)) (or (not (and (inv_main2415_5 var35 var34 var33 var32 var31 var30) (and (and (and (and (and (and (and (and (= var29 var28) (= var27 var26)) (= var25 var24)) (= var23 var22)) (= var21 var20)) (= var19 var18)) (= var17 (|internal_node::next| (getinternal_node (read var28 var18))))) (and (and (and (and (and (and (and (and (= var16 (newHeap (alloc var35 (O_internal_node var15)))) (or (and var13 (= var14 (newAddr (alloc var35 (O_internal_node var15))))) (and (not var13) (= var14 var34)))) (= var12 var33)) (= var11 var32)) (= var10 var31)) (= var9 var30)) (= var8 (newAddr (alloc var35 (O_internal_node var15))))) (and (and (and (and (and (and (= var7 (write var16 var8 (O_internal_node (internal_node nullAddr)))) (= var6 var14)) (= var5 var12)) (= var4 var11)) (= var3 var10)) (= var2 var9)) (= var1 var8))) (not (= var0 0)))) (and (and (and (and (and (= var28 (write var7 var2 (O_internal_node (internal_node var1)))) (= var26 var6)) (= var24 var5)) (= var22 var4)) (= var20 var3)) (= var18 var2))))) (inv_main2415_5 var29 var27 var25 var23 var21 var17))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Bool) (var5 Addr) (var6 sll) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Heap) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Bool) (var19 Addr) (var20 internal_node) (var21 Heap) (var22 Heap) (var23 Addr) (var24 Heap)) (or (not (and (inv_main2459_5 var24 var23) (and (and (and (and (and (and (= var22 (newHeap (alloc var21 (O_internal_node var20)))) (or (and var18 (= var19 (newAddr (alloc var21 (O_internal_node var20))))) (and (not var18) (= var19 var17)))) (= var16 var15)) (= var14 var15)) (= var13 (newAddr (alloc var21 (O_internal_node var20))))) (and (and (and (and (= var12 (write var22 var13 (O_internal_node (internal_node nullAddr)))) (= var11 var19)) (= var10 var16)) (= var9 var14)) (= var8 var13))) (and (and (and (and (= var7 (newHeap (alloc var24 (O_sll var6)))) (or (and var4 (= var5 (newAddr (alloc var24 (O_sll var6))))) (and (not var4) (= var5 var23)))) (= var3 (newAddr (alloc var24 (O_sll var6))))) (and (and (= var2 (write var7 var3 (O_sll (sll nullAddr (|sll::shared| (getsll (read var7 var3))))))) (= var1 var5)) (= var0 var3))) (and (and (= var21 (write var2 var0 (O_sll (sll (|sll::next| (getsll (read var2 var0))) nullAddr)))) (= var17 var1)) (= var15 var0)))))) (inv_main2415_5 var12 var11 var10 var9 var8 var8))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main2460_5 var8 var7 var6 var5) (and (and (and (and (and (= var4 var8) (= var3 var7)) (= var2 var6)) (= var1 var5)) (= var0 (|sll::next| (getsll (read var8 var5))))) (not (= var5 nullAddr))))) (inv_main2460_5 var4 var3 var2 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main_9 var5 var4 var3 var2 var1) (= var0 0))) (inv_main2460_5 var5 var4 var3 var3))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap)) (not (and (inv_main2462_12 var2 var1 var0) (not (= var1 nullAddr))))))
(check-sat)
