(set-logic HORN)
(set-info :source |
    Benchmark: C_VC
    Output by Princess (http://www.philipp.ruemmer.org/princess.shtml)
|)
(set-info :status unsat)
;===============================================================================
; Encoding of Heap sorts and operations
;-------------------------------------------------------------------------------
(define-sort Addr() Int)
(declare-datatypes ((AddrRange 0))
                   (((AddrRange (AddrRangeStart Addr) (AddrRangeSize Int)))))

(declare-datatypes ((HeapObject 0) (item 0))
                   (((O_Int (getInt Int)) (O_UInt (getUInt Int)) (O_Addr (getAddr Addr)) (O_AddrRange (getAddrRange AddrRange)) (O_item (getitem item)) (defObj))
                   ((item (|item::next| Addr) (|item::data| Addr)))))
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
(declare-fun inv_main539_5 (Heap) Bool)
(declare-fun inv_main539_5_1 (Heap Addr) Bool)
(declare-fun inv_main544_9 (Heap Addr Addr) Bool)
(declare-fun inv_main551_13 (Heap Addr Addr) Bool)
(declare-fun inv_main_11 (Heap Addr Addr) Bool)
(declare-fun inv_main_5 (Heap Addr) Bool)
(declare-fun inv_main_7 (Heap Addr Addr) Bool)
(assert (forall ((var0 Heap)) (or (not (= var0 emptyHeap)) (inv_main539_5 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Int) (var6 Addr) (var7 item) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Int) (var12 Int) (var13 Addr) (var14 Addr) (var15 Heap) (var16 Addr) (var17 Heap) (var18 Int) (var19 Addr) (var20 Addr) (var21 Heap)) (or (not (and (inv_main539_5_1 var21 var20) (and (and (not (= var19 nullAddr)) (and (= var18 0) (and (and (and (and (not (= (|item::next| (getitem (read var17 var16))) nullAddr)) (and (and (and (and (= var15 var17) (= var14 var13)) (= var12 var11)) (= var10 var16)) (= var9 (|item::data| (getitem (read var17 (|item::next| (getitem (read var17 var16))))))))) (and (and (and (= var8 (newHeap (alloc var21 (O_item var7)))) (= var6 var20)) (= var5 1)) (= var4 (newAddr (alloc var21 (O_item var7)))))) (and (and (and (= var17 (write var8 var4 (O_item (item var6 (|item::data| (getitem (read var8 var4))))))) (= var13 var6)) (= var11 var5)) (= var16 var4))) (and (and (and (= var3 (write var15 var10 (O_item (item (|item::next| (getitem (read var15 var10))) var9)))) (= var2 var14)) (= var1 var12)) (= var19 var10))))) (= var0 (|item::next| (getitem (read var3 var19))))))) (inv_main544_9 var3 var19 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Int) (var6 Addr) (var7 item) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Int) (var12 Int) (var13 Addr) (var14 Addr) (var15 item) (var16 Heap) (var17 Addr) (var18 Heap) (var19 Int) (var20 Addr) (var21 Addr) (var22 Heap)) (or (not (and (inv_main539_5_1 var22 var21) (and (and (not (= var20 nullAddr)) (and (= var19 0) (and (and (and (and (= (|item::next| (getitem (read var18 var17))) nullAddr) (and (and (and (and (= var16 (newHeap (alloc var18 (O_item var15)))) (= var14 var13)) (= var12 var11)) (= var10 var17)) (= var9 (newAddr (alloc var18 (O_item var15)))))) (and (and (and (= var8 (newHeap (alloc var22 (O_item var7)))) (= var6 var21)) (= var5 1)) (= var4 (newAddr (alloc var22 (O_item var7)))))) (and (and (and (= var18 (write var8 var4 (O_item (item var6 (|item::data| (getitem (read var8 var4))))))) (= var13 var6)) (= var11 var5)) (= var17 var4))) (and (and (and (= var3 (write var16 var10 (O_item (item (|item::next| (getitem (read var16 var10))) var9)))) (= var2 var14)) (= var1 var12)) (= var20 var10))))) (= var0 (|item::next| (getitem (read var3 var20))))))) (inv_main544_9 var3 var20 var0))))
(assert (forall ((var0 Addr) (var1 Heap)) (or (not (and (inv_main539_5 var1) (= var0 nullAddr))) (inv_main539_5_1 var1 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Int) (var6 Addr) (var7 item) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Int) (var12 Int) (var13 Addr) (var14 Addr) (var15 Heap) (var16 Addr) (var17 Heap) (var18 Int) (var19 Addr) (var20 Heap)) (or (not (and (inv_main539_5_1 var20 var19) (and (not (= var18 0)) (and (and (and (and (not (= (|item::next| (getitem (read var17 var16))) nullAddr)) (and (and (and (and (= var15 var17) (= var14 var13)) (= var12 var11)) (= var10 var16)) (= var9 (|item::data| (getitem (read var17 (|item::next| (getitem (read var17 var16))))))))) (and (and (and (= var8 (newHeap (alloc var20 (O_item var7)))) (= var6 var19)) (= var5 1)) (= var4 (newAddr (alloc var20 (O_item var7)))))) (and (and (and (= var17 (write var8 var4 (O_item (item var6 (|item::data| (getitem (read var8 var4))))))) (= var13 var6)) (= var11 var5)) (= var16 var4))) (and (and (and (= var3 (write var15 var10 (O_item (item (|item::next| (getitem (read var15 var10))) var9)))) (= var2 var14)) (= var1 var12)) (= var0 var10)))))) (inv_main539_5_1 var3 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Int) (var6 Addr) (var7 item) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Int) (var12 Int) (var13 Addr) (var14 Addr) (var15 item) (var16 Heap) (var17 Addr) (var18 Heap) (var19 Int) (var20 Addr) (var21 Heap)) (or (not (and (inv_main539_5_1 var21 var20) (and (not (= var19 0)) (and (and (and (and (= (|item::next| (getitem (read var18 var17))) nullAddr) (and (and (and (and (= var16 (newHeap (alloc var18 (O_item var15)))) (= var14 var13)) (= var12 var11)) (= var10 var17)) (= var9 (newAddr (alloc var18 (O_item var15)))))) (and (and (and (= var8 (newHeap (alloc var21 (O_item var7)))) (= var6 var20)) (= var5 1)) (= var4 (newAddr (alloc var21 (O_item var7)))))) (and (and (and (= var18 (write var8 var4 (O_item (item var6 (|item::data| (getitem (read var8 var4))))))) (= var13 var6)) (= var11 var5)) (= var17 var4))) (and (and (and (= var3 (write var16 var10 (O_item (item (|item::next| (getitem (read var16 var10))) var9)))) (= var2 var14)) (= var1 var12)) (= var0 var10)))))) (inv_main539_5_1 var3 var0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main_5 var4 var3) (and (and (= var2 nullAddr) (and (and (= var1 var4) (= var0 var3)) (= var2 (|item::next| (getitem (read var4 var3)))))) (not (= var3 nullAddr))))) (inv_main551_13 var1 var0 var2))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main551_13 var3 var2 var1) (= var0 (write var3 (|item::data| (getitem (read var3 var2))) defObj)))) (inv_main_11 var0 var2 var1))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main_5 var4 var3) (and (and (not (= var2 nullAddr)) (and (and (= var1 var4) (= var0 var3)) (= var2 (|item::next| (getitem (read var4 var3)))))) (not (= var3 nullAddr))))) (inv_main_11 var1 var0 var2))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main544_9 var3 var2 var1) (= var0 (write var3 (|item::data| (getitem (read var3 var2))) defObj)))) (inv_main_7 var0 var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main_7 var5 var4 var3) (and (and (= var2 (write var5 var4 defObj)) (= var1 var4)) (= var0 var3)))) (inv_main_5 var2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main_11 var5 var4 var3) (and (and (= var2 (write var5 var4 defObj)) (= var1 var4)) (= var0 var3)))) (inv_main_5 var2 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Int) (var5 Addr) (var6 item) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Int) (var11 Int) (var12 Addr) (var13 Addr) (var14 Heap) (var15 Addr) (var16 Heap) (var17 Int) (var18 Addr) (var19 Addr) (var20 Heap)) (or (not (and (inv_main539_5_1 var20 var19) (and (= var18 nullAddr) (and (= var17 0) (and (and (and (and (not (= (|item::next| (getitem (read var16 var15))) nullAddr)) (and (and (and (and (= var14 var16) (= var13 var12)) (= var11 var10)) (= var9 var15)) (= var8 (|item::data| (getitem (read var16 (|item::next| (getitem (read var16 var15))))))))) (and (and (and (= var7 (newHeap (alloc var20 (O_item var6)))) (= var5 var19)) (= var4 1)) (= var3 (newAddr (alloc var20 (O_item var6)))))) (and (and (and (= var16 (write var7 var3 (O_item (item var5 (|item::data| (getitem (read var7 var3))))))) (= var12 var5)) (= var10 var4)) (= var15 var3))) (and (and (and (= var2 (write var14 var9 (O_item (item (|item::next| (getitem (read var14 var9))) var8)))) (= var1 var13)) (= var0 var11)) (= var18 var9))))))) (inv_main_5 var2 var18))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Int) (var5 Addr) (var6 item) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Int) (var11 Int) (var12 Addr) (var13 Addr) (var14 item) (var15 Heap) (var16 Addr) (var17 Heap) (var18 Int) (var19 Addr) (var20 Addr) (var21 Heap)) (or (not (and (inv_main539_5_1 var21 var20) (and (= var19 nullAddr) (and (= var18 0) (and (and (and (and (= (|item::next| (getitem (read var17 var16))) nullAddr) (and (and (and (and (= var15 (newHeap (alloc var17 (O_item var14)))) (= var13 var12)) (= var11 var10)) (= var9 var16)) (= var8 (newAddr (alloc var17 (O_item var14)))))) (and (and (and (= var7 (newHeap (alloc var21 (O_item var6)))) (= var5 var20)) (= var4 1)) (= var3 (newAddr (alloc var21 (O_item var6)))))) (and (and (and (= var17 (write var7 var3 (O_item (item var5 (|item::data| (getitem (read var7 var3))))))) (= var12 var5)) (= var10 var4)) (= var16 var3))) (and (and (and (= var2 (write var15 var9 (O_item (item (|item::next| (getitem (read var15 var9))) var8)))) (= var1 var13)) (= var0 var11)) (= var19 var9))))))) (inv_main_5 var2 var19))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main544_9 var2 var1 var0) (and (not (= (|item::data| (getitem (read var2 var1))) nullAddr)) (= (read var2 (|item::data| (getitem (read var2 var1)))) defObj))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_7 var2 var1 var0) (and (not (= var1 nullAddr)) (= (read var2 var1) defObj))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main551_13 var2 var1 var0) (and (not (= (|item::data| (getitem (read var2 var1))) nullAddr)) (= (read var2 (|item::data| (getitem (read var2 var1)))) defObj))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_11 var2 var1 var0) (and (not (= var1 nullAddr)) (= (read var2 var1) defObj))))))
(check-sat)
