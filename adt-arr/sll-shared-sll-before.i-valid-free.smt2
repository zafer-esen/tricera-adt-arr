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
(declare-fun inv_main2415_5 (Heap Addr Addr) Bool)
(declare-fun inv_main2437_9 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main2445_9 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main2455_5 (Heap) Bool)
(declare-fun inv_main_10 (Heap Addr Addr Addr Addr) Bool)
(assert (forall ((var0 Heap)) (or (not (= var0 emptyHeap)) (inv_main2455_5 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Int) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Heap) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Heap) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Addr) (var23 sll) (var24 Heap) (var25 Addr) (var26 Addr) (var27 Addr) (var28 Addr) (var29 Addr) (var30 Addr) (var31 Addr) (var32 Addr) (var33 Addr) (var34 Heap) (var35 Heap) (var36 Addr) (var37 Addr) (var38 Addr) (var39 Addr) (var40 Heap)) (or (not (and (inv_main_10 var40 var39 var38 var37 var36) (and (and (and (and (and (and (and (= var35 var34) (= var33 var32)) (= var31 var30)) (= var29 var28)) (= var27 var26)) (= var25 (|sll::next| (getsll (read var34 var26))))) (and (and (and (and (and (and (and (and (and (= var24 (newHeap (alloc var40 (O_sll var23)))) (= var22 var39)) (= var21 var38)) (= var20 var37)) (= var19 var36)) (= var18 (newAddr (alloc var40 (O_sll var23))))) (and (and (and (and (and (= var17 (write var24 var18 (O_sll (sll nullAddr (|sll::shared| (getsll (read var24 var18))))))) (= var16 var22)) (= var15 var21)) (= var14 var20)) (= var13 var19)) (= var12 var18))) (and (and (and (and (and (= var11 (write var17 var12 (O_sll (sll (|sll::next| (getsll (read var17 var12))) nullAddr)))) (= var10 var16)) (= var9 var15)) (= var8 var14)) (= var7 var13)) (= var6 var12))) (not (= var5 0))) (and (and (and (and (= var4 (write var11 var7 (O_sll (sll var6 (|sll::shared| (getsll (read var11 var7))))))) (= var3 var10)) (= var2 var9)) (= var1 var8)) (= var0 var7)))) (and (and (and (and (= var34 (write var4 (|sll::next| (getsll (read var4 var0))) (O_sll (sll (|sll::next| (getsll (read var4 (|sll::next| (getsll (read var4 var0)))))) var2)))) (= var32 var3)) (= var30 var2)) (= var28 var1)) (= var26 var0))))) (inv_main_10 var35 var33 var31 var29 var25))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Addr) (var13 sll) (var14 Heap) (var15 Addr) (var16 Addr) (var17 Heap)) (or (not (and (inv_main2415_5 var17 var16 var15) (and (and (and (and (and (and (and (= var14 (newHeap (alloc var17 (O_sll var13)))) (= var12 var16)) (= var11 var16)) (= var10 (newAddr (alloc var17 (O_sll var13))))) (and (and (and (= var9 (write var14 var10 (O_sll (sll nullAddr (|sll::shared| (getsll (read var14 var10))))))) (= var8 var12)) (= var7 var11)) (= var6 var10))) (and (and (and (= var5 (write var9 var6 (O_sll (sll (|sll::next| (getsll (read var9 var6))) nullAddr)))) (= var4 var8)) (= var3 var7)) (= var2 var6))) (= var1 0)) (= var0 (write var5 var2 (O_sll (sll (|sll::next| (getsll (read var5 var2))) var3))))))) (inv_main_10 var0 var4 var3 var2 var2))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 internal_node) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Heap) (var16 Heap) (var17 Addr) (var18 Addr) (var19 Heap)) (or (not (and (inv_main2415_5 var19 var18 var17) (and (and (and (and (and (= var16 var15) (= var14 var13)) (= var12 var11)) (= var10 (|internal_node::next| (getinternal_node (read var15 var11))))) (and (and (and (and (and (= var9 (newHeap (alloc var19 (O_internal_node var8)))) (= var7 var18)) (= var6 var17)) (= var5 (newAddr (alloc var19 (O_internal_node var8))))) (and (and (and (= var4 (write var9 var5 (O_internal_node (internal_node nullAddr)))) (= var3 var7)) (= var2 var6)) (= var1 var5))) (not (= var0 0)))) (and (and (= var15 (write var4 var2 (O_internal_node (internal_node var1)))) (= var13 var3)) (= var11 var2))))) (inv_main2415_5 var16 var14 var10))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 internal_node) (var4 Heap) (var5 Heap)) (or (not (and (inv_main2455_5 var5) (and (and (= var4 (newHeap (alloc var5 (O_internal_node var3)))) (= var2 (newAddr (alloc var5 (O_internal_node var3))))) (and (= var1 (write var4 var2 (O_internal_node (internal_node nullAddr)))) (= var0 var2))))) (inv_main2415_5 var1 var0 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main2437_9 var10 var9 var8 var7 var6) (and (and (not (= var5 nullAddr)) (and (and (and (and (= var4 (write var10 var7 defObj)) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var5 var6))) (= var0 (|internal_node::next| (getinternal_node (read var4 var5))))))) (inv_main2437_9 var4 var3 var2 var5 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main_10 var6 var5 var4 var3 var2) (and (and (not (= var5 nullAddr)) (= var1 0)) (= var0 (|internal_node::next| (getinternal_node (read var6 var5))))))) (inv_main2437_9 var6 var5 var3 var5 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main2445_9 var10 var9 var8 var7 var6) (and (and (not (= var5 nullAddr)) (and (and (and (and (= var4 (write var10 var7 defObj)) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var5 var6))) (= var0 (|sll::next| (getsll (read var4 var5))))))) (inv_main2445_9 var4 var3 var2 var5 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main2437_9 var10 var9 var8 var7 var6) (and (and (not (= var5 nullAddr)) (and (= var4 nullAddr) (and (and (and (and (= var3 (write var10 var7 defObj)) (= var2 var9)) (= var5 var8)) (= var1 var7)) (= var4 var6)))) (= var0 (|sll::next| (getsll (read var3 var5))))))) (inv_main2445_9 var3 var2 var5 var5 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main_10 var6 var5 var4 var3 var2) (and (and (not (= var3 nullAddr)) (and (= var5 nullAddr) (= var1 0))) (= var0 (|sll::next| (getsll (read var6 var3))))))) (inv_main2445_9 var6 var5 var3 var3 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main2437_9 var4 var3 var2 var1 var0) (and (not (= var1 nullAddr)) (= (read var4 var1) defObj))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main2445_9 var4 var3 var2 var1 var0) (and (not (= var1 nullAddr)) (= (read var4 var1) defObj))))))
(check-sat)
