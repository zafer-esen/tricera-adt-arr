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
(declare-fun inv_main532_5 (Heap Int Addr Int Int Addr) Bool)
(declare-fun inv_main534_18 (Heap Int Addr Int Int Addr Addr) Bool)
(declare-fun inv_main541_5 (Heap Int) Bool)
(declare-fun inv_main548_12 (Heap Int Addr Int) Bool)
(declare-fun inv_main_14 (Heap Int Addr Int) Bool)
(declare-fun inv_main_4 (Heap Int Addr Int Int Addr) Bool)
(declare-fun inv_main_9 (Heap Int Addr Int) Bool)
(assert (forall ((var0 Int) (var1 Heap)) (or (not (and (= var1 emptyHeap) (= var0 0))) (inv_main541_5 var1 var0))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Addr) (var3 Int) (var4 Heap)) (or (not (and (inv_main548_12 var4 var3 var2 var1) (and (is-O_item (read var4 var2)) (= var0 (write var4 (|item::data| (getitem (read var4 var2))) defObj))))) (inv_main_9 var0 var3 var2 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Addr) (var4 Int) (var5 Heap) (var6 Int) (var7 Int) (var8 Addr) (var9 Addr) (var10 Int) (var11 Int) (var12 Addr) (var13 Int) (var14 Heap)) (or (not (and (inv_main534_18 var14 var13 var12 var11 var10 var9 var8) (and (and (not (<= 0 (+ (* (- 1) (+ var7 1)) (- 1)))) (and (<= 0 (+ (+ var7 1) (- 1))) (and (= var6 0) (and (and (is-O_item (read var14 var9)) (is-O_item (read var14 var9))) (and (and (and (and (and (= var5 (write var14 var9 (O_item (item (|item::next| (getitem (read var14 var9))) var8)))) (= var4 var13)) (= var3 var12)) (= var7 var11)) (= var2 var10)) (= var1 var9)))))) (= var0 (+ var7 1))))) (inv_main_9 var5 var4 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Int) (var6 Int) (var7 Heap) (var8 Heap) (var9 Int) (var10 Int) (var11 Int) (var12 Addr) (var13 Addr) (var14 Int) (var15 Int) (var16 Addr) (var17 Int) (var18 Heap)) (or (not (and (inv_main534_18 var18 var17 var16 var15 var14 var13 var12) (and (not (<= 0 (+ (* (- 1) var11) (- 1)))) (and (<= 0 (+ var11 (- 1))) (and (and (and (= var10 0) (not (= var9 0))) (and (and (and (and (= var8 var7) (= var6 var5)) (= var4 var3)) (= var11 (+ var2 1))) (or (and (<= 0 (+ (+ 20 (* (- 1) var5)) (- 1))) (= var10 1)) (and (not (<= 0 (+ (+ 20 (* (- 1) var5)) (- 1)))) (= var10 0))))) (and (and (is-O_item (read var18 var13)) (is-O_item (read var18 var13))) (and (and (and (and (and (= var7 (write var18 var13 (O_item (item (|item::next| (getitem (read var18 var13))) var12)))) (= var5 var17)) (= var1 var16)) (= var2 var15)) (= var0 var14)) (= var3 var13)))))))) (inv_main_9 var8 var6 var4 var11))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Addr) (var4 Int) (var5 Heap) (var6 Int) (var7 Int) (var8 Addr) (var9 Addr) (var10 Int) (var11 Int) (var12 Addr) (var13 Int) (var14 Heap)) (or (not (and (inv_main534_18 var14 var13 var12 var11 var10 var9 var8) (and (and (<= 0 (+ (* (- 1) (+ var7 1)) (- 1))) (and (<= 0 (+ (+ var7 1) (- 1))) (and (= var6 0) (and (and (is-O_item (read var14 var9)) (is-O_item (read var14 var9))) (and (and (and (and (and (= var5 (write var14 var9 (O_item (item (|item::next| (getitem (read var14 var9))) var8)))) (= var4 var13)) (= var3 var12)) (= var7 var11)) (= var2 var10)) (= var1 var9)))))) (= var0 (+ var7 1))))) (inv_main548_12 var5 var4 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Int) (var6 Int) (var7 Heap) (var8 Heap) (var9 Int) (var10 Int) (var11 Int) (var12 Addr) (var13 Addr) (var14 Int) (var15 Int) (var16 Addr) (var17 Int) (var18 Heap)) (or (not (and (inv_main534_18 var18 var17 var16 var15 var14 var13 var12) (and (<= 0 (+ (* (- 1) var11) (- 1))) (and (<= 0 (+ var11 (- 1))) (and (and (and (= var10 0) (not (= var9 0))) (and (and (and (and (= var8 var7) (= var6 var5)) (= var4 var3)) (= var11 (+ var2 1))) (or (and (<= 0 (+ (+ 20 (* (- 1) var5)) (- 1))) (= var10 1)) (and (not (<= 0 (+ (+ 20 (* (- 1) var5)) (- 1)))) (= var10 0))))) (and (and (is-O_item (read var18 var13)) (is-O_item (read var18 var13))) (and (and (and (and (and (= var7 (write var18 var13 (O_item (item (|item::next| (getitem (read var18 var13))) var12)))) (= var5 var17)) (= var1 var16)) (= var2 var15)) (= var0 var14)) (= var3 var13)))))))) (inv_main548_12 var8 var6 var4 var11))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 item) (var4 Heap) (var5 Int) (var6 Addr) (var7 Int) (var8 Int) (var9 Addr) (var10 Addr) (var11 Int) (var12 Int) (var13 Heap) (var14 Heap) (var15 Int) (var16 Int) (var17 Addr) (var18 Addr) (var19 Int) (var20 Int) (var21 Addr) (var22 Int) (var23 Heap)) (or (not (and (inv_main534_18 var23 var22 var21 var20 var19 var18 var17) (and (and (and (and (and (and (and (not (= var16 0)) (not (= var15 0))) (and (and (and (and (= var14 var13) (= var12 var11)) (= var10 var9)) (= var8 (+ var7 1))) (or (and (<= 0 (+ (+ 20 (* (- 1) var11)) (- 1))) (= var16 1)) (and (not (<= 0 (+ (+ 20 (* (- 1) var11)) (- 1)))) (= var16 0))))) (and (and (is-O_item (read var23 var18)) (is-O_item (read var23 var18))) (and (and (and (and (and (= var13 (write var23 var18 (O_item (item (|item::next| (getitem (read var23 var18))) var17)))) (= var11 var22)) (= var6 var21)) (= var7 var20)) (= var5 var19)) (= var9 var18)))) (= var4 (newHeap (alloc var14 (O_item var3))))) (= var2 (+ var12 1))) (= var1 2)) (= var0 (newAddr (alloc var14 (O_item var3))))))) (inv_main532_5 var4 var2 var10 var8 var1 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Int) (var4 item) (var5 Heap) (var6 Addr) (var7 Int) (var8 Heap) (var9 Int) (var10 Heap)) (or (not (and (inv_main541_5 var10 var9) (and (and (and (and (and (and (and (= var8 var10) (= var7 var9)) (= var6 nullAddr)) (= var5 (newHeap (alloc var8 (O_item var4))))) (= var3 (+ var7 1))) (= var2 0)) (= var1 2)) (= var0 (newAddr (alloc var8 (O_item var4))))))) (inv_main532_5 var5 var3 var6 var2 var1 var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Int) (var3 Int) (var4 Addr) (var5 Int) (var6 Heap)) (or (not (and (inv_main532_5 var6 var5 var4 var3 var2 var1) (and (and (is-O_item (read var6 var1)) (is-O_item (read var6 var1))) (= var0 (write var6 var1 (O_item (item var4 (|item::data| (getitem (read var6 var1)))))))))) (inv_main_4 var0 var5 var4 var3 var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Addr) (var5 Int) (var6 Heap)) (or (not (and (inv_main_4 var6 var5 var4 var3 var2 var1) (and (and (and (and (is-O_item (read var6 var1)) (not (= (|item::next| (getitem (read var6 var1))) nullAddr))) (is-O_item (read var6 var1))) (is-O_item (read var6 (|item::next| (getitem (read var6 var1)))))) (= var0 (|item::data| (getitem (read var6 (|item::next| (getitem (read var6 var1)))))))))) (inv_main534_18 var6 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 item) (var2 Heap) (var3 Addr) (var4 Int) (var5 Int) (var6 Addr) (var7 Int) (var8 Heap)) (or (not (and (inv_main_4 var8 var7 var6 var5 var4 var3) (and (and (and (is-O_item (read var8 var3)) (= (|item::next| (getitem (read var8 var3))) nullAddr)) (= var2 (newHeap (alloc var8 (O_item var1))))) (= var0 (newAddr (alloc var8 (O_item var1))))))) (inv_main534_18 var2 var7 var6 var5 var4 var3 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap) (var5 Addr) (var6 Int) (var7 Addr) (var8 Int) (var9 Heap) (var10 Int) (var11 Int) (var12 Addr) (var13 Int) (var14 Heap)) (or (not (and (inv_main_9 var14 var13 var12 var11) (and (and (<= 0 (+ (+ var10 (- 1)) (- 1))) (and (and (is-O_item (read var14 var12)) (and (and (and (and (= var9 var14) (= var8 var13)) (= var7 var12)) (= var6 var11)) (= var5 (|item::next| (getitem (read var14 var12)))))) (and (and (and (and (= var4 (write var9 var7 defObj)) (= var3 var8)) (= var2 var7)) (= var10 var6)) (= var1 var5)))) (= var0 (+ var10 (- 1)))))) (inv_main_14 var4 var3 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap) (var5 Addr) (var6 Int) (var7 Addr) (var8 Int) (var9 Heap) (var10 Int) (var11 Int) (var12 Addr) (var13 Int) (var14 Heap)) (or (not (and (inv_main_14 var14 var13 var12 var11) (and (and (<= 0 (+ (+ var10 (- 1)) (- 1))) (and (and (is-O_item (read var14 var12)) (and (and (and (and (= var9 var14) (= var8 var13)) (= var7 var12)) (= var6 var11)) (= var5 (|item::next| (getitem (read var14 var12)))))) (and (and (and (and (= var4 (write var9 var7 defObj)) (= var3 var8)) (= var2 var7)) (= var10 var6)) (= var1 var5)))) (= var0 (+ var10 (- 1)))))) (inv_main_14 var4 var3 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Addr) (var4 Int) (var5 Heap) (var6 Int) (var7 Int) (var8 Addr) (var9 Addr) (var10 Int) (var11 Int) (var12 Addr) (var13 Int) (var14 Heap)) (or (not (and (inv_main534_18 var14 var13 var12 var11 var10 var9 var8) (and (and (<= 0 (+ (+ var7 1) (- 1))) (and (not (<= 0 (+ (+ var7 1) (- 1)))) (and (= var6 0) (and (and (is-O_item (read var14 var9)) (is-O_item (read var14 var9))) (and (and (and (and (and (= var5 (write var14 var9 (O_item (item (|item::next| (getitem (read var14 var9))) var8)))) (= var4 var13)) (= var3 var12)) (= var7 var11)) (= var2 var10)) (= var1 var9)))))) (= var0 (+ var7 1))))) (inv_main_14 var5 var4 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Int) (var6 Int) (var7 Heap) (var8 Heap) (var9 Int) (var10 Int) (var11 Int) (var12 Addr) (var13 Addr) (var14 Int) (var15 Int) (var16 Addr) (var17 Int) (var18 Heap)) (or (not (and (inv_main534_18 var18 var17 var16 var15 var14 var13 var12) (and (<= 0 (+ var11 (- 1))) (and (not (<= 0 (+ var11 (- 1)))) (and (and (and (= var10 0) (not (= var9 0))) (and (and (and (and (= var8 var7) (= var6 var5)) (= var4 var3)) (= var11 (+ var2 1))) (or (and (<= 0 (+ (+ 20 (* (- 1) var5)) (- 1))) (= var10 1)) (and (not (<= 0 (+ (+ 20 (* (- 1) var5)) (- 1)))) (= var10 0))))) (and (and (is-O_item (read var18 var13)) (is-O_item (read var18 var13))) (and (and (and (and (and (= var7 (write var18 var13 (O_item (item (|item::next| (getitem (read var18 var13))) var12)))) (= var5 var17)) (= var1 var16)) (= var2 var15)) (= var0 var14)) (= var3 var13)))))))) (inv_main_14 var8 var6 var4 var11))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Addr) (var4 Int) (var5 Heap)) (not (and (inv_main532_5 var5 var4 var3 var2 var1 var0) (not (is-O_item (read var5 var0)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Addr) (var4 Int) (var5 Heap)) (not (and (inv_main532_5 var5 var4 var3 var2 var1 var0) (and (is-O_item (read var5 var0)) (not (is-O_item (read var5 var0))))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Addr) (var4 Int) (var5 Heap)) (not (and (inv_main_4 var5 var4 var3 var2 var1 var0) (not (is-O_item (read var5 var0)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Addr) (var4 Int) (var5 Heap)) (not (and (inv_main_4 var5 var4 var3 var2 var1 var0) (and (and (is-O_item (read var5 var0)) (not (= (|item::next| (getitem (read var5 var0))) nullAddr))) (not (is-O_item (read var5 var0))))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Addr) (var4 Int) (var5 Heap)) (not (and (inv_main_4 var5 var4 var3 var2 var1 var0) (and (and (and (is-O_item (read var5 var0)) (not (= (|item::next| (getitem (read var5 var0))) nullAddr))) (is-O_item (read var5 var0))) (not (is-O_item (read var5 (|item::next| (getitem (read var5 var0)))))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Addr) (var5 Int) (var6 Heap)) (not (and (inv_main534_18 var6 var5 var4 var3 var2 var1 var0) (not (is-O_item (read var6 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Addr) (var5 Int) (var6 Heap)) (not (and (inv_main534_18 var6 var5 var4 var3 var2 var1 var0) (and (is-O_item (read var6 var1)) (not (is-O_item (read var6 var1))))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Heap)) (not (and (inv_main548_12 var3 var2 var1 var0) (not (is-O_item (read var3 var1)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Heap)) (not (and (inv_main_9 var3 var2 var1 var0) (not (is-O_item (read var3 var1)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Heap)) (not (and (inv_main_14 var3 var2 var1 var0) (not (is-O_item (read var3 var1)))))))
(check-sat)
