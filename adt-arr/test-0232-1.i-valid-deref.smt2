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
(declare-fun inv_main530_5 (Heap Addr Int Addr) Bool)
(declare-fun inv_main532_18 (Heap Addr Int Addr Addr) Bool)
(declare-fun inv_main539_5 (Heap) Bool)
(declare-fun inv_main543_9 (Heap Addr) Bool)
(declare-fun inv_main_3 (Heap Addr Int Addr) Bool)
(declare-fun inv_main_9 (Heap Addr) Bool)
(assert (forall ((var0 Heap)) (or (not (= var0 emptyHeap)) (inv_main539_5 var0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main543_9 var7 var6) (and (not (= var5 nullAddr)) (and (and (is-O_item (read var7 var6)) (and (and (= var4 var7) (= var3 var6)) (= var2 (|item::next| (getitem (read var7 var6)))))) (and (and (= var1 (write var4 var3 defObj)) (= var0 var3)) (= var5 var2)))))) (inv_main_9 var1 var5))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main_9 var7 var6) (and (not (= var5 nullAddr)) (and (and (is-O_item (read var7 var6)) (and (and (= var4 var7) (= var3 var6)) (= var2 (|item::next| (getitem (read var7 var6)))))) (and (and (= var1 (write var4 var3 defObj)) (= var0 var3)) (= var5 var2)))))) (inv_main_9 var1 var5))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Int) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Int) (var8 Addr) (var9 Heap)) (or (not (and (inv_main532_18 var9 var8 var7 var6 var5) (and (not (= var4 nullAddr)) (and (= var4 nullAddr) (and (= var3 0) (and (and (is-O_item (read var9 var6)) (is-O_item (read var9 var6))) (and (and (and (= var2 (write var9 var6 (O_item (item (|item::next| (getitem (read var9 var6))) var5)))) (= var1 var8)) (= var0 var7)) (= var4 var6)))))))) (inv_main_9 var2 var4))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Int) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Int) (var8 Addr) (var9 Heap)) (or (not (and (inv_main532_18 var9 var8 var7 var6 var5) (and (not (= var4 nullAddr)) (and (= var3 0) (and (and (is-O_item (read var9 var6)) (is-O_item (read var9 var6))) (and (and (and (= var2 (write var9 var6 (O_item (item (|item::next| (getitem (read var9 var6))) var5)))) (= var1 var8)) (= var0 var7)) (= var4 var6))))))) (inv_main543_9 var2 var4))))
(assert (forall ((var0 Addr) (var1 Int) (var2 item) (var3 Heap) (var4 Addr) (var5 Heap) (var6 Heap)) (or (not (and (inv_main539_5 var6) (and (and (and (and (= var5 var6) (= var4 nullAddr)) (= var3 (newHeap (alloc var5 (O_item var2))))) (= var1 1)) (= var0 (newAddr (alloc var5 (O_item var2))))))) (inv_main530_5 var3 var4 var1 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 item) (var3 Heap) (var4 Addr) (var5 Int) (var6 Addr) (var7 Heap) (var8 Int) (var9 Addr) (var10 Addr) (var11 Int) (var12 Addr) (var13 Heap)) (or (not (and (inv_main532_18 var13 var12 var11 var10 var9) (and (and (and (and (not (= var8 0)) (and (and (is-O_item (read var13 var10)) (is-O_item (read var13 var10))) (and (and (and (= var7 (write var13 var10 (O_item (item (|item::next| (getitem (read var13 var10))) var9)))) (= var6 var12)) (= var5 var11)) (= var4 var10)))) (= var3 (newHeap (alloc var7 (O_item var2))))) (= var1 1)) (= var0 (newAddr (alloc var7 (O_item var2))))))) (inv_main530_5 var3 var4 var1 var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Int) (var3 Addr) (var4 Heap)) (or (not (and (inv_main530_5 var4 var3 var2 var1) (and (and (is-O_item (read var4 var1)) (is-O_item (read var4 var1))) (= var0 (write var4 var1 (O_item (item var3 (|item::data| (getitem (read var4 var1)))))))))) (inv_main_3 var0 var3 var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Heap)) (or (not (and (inv_main_3 var4 var3 var2 var1) (and (and (and (and (is-O_item (read var4 var1)) (not (= (|item::next| (getitem (read var4 var1))) nullAddr))) (is-O_item (read var4 var1))) (is-O_item (read var4 (|item::next| (getitem (read var4 var1)))))) (= var0 (|item::data| (getitem (read var4 (|item::next| (getitem (read var4 var1)))))))))) (inv_main532_18 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 item) (var2 Heap) (var3 Addr) (var4 Int) (var5 Addr) (var6 Heap)) (or (not (and (inv_main_3 var6 var5 var4 var3) (and (and (and (is-O_item (read var6 var3)) (= (|item::next| (getitem (read var6 var3))) nullAddr)) (= var2 (newHeap (alloc var6 (O_item var1))))) (= var0 (newAddr (alloc var6 (O_item var1))))))) (inv_main532_18 var2 var5 var4 var3 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Heap)) (not (and (inv_main530_5 var3 var2 var1 var0) (not (is-O_item (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Heap)) (not (and (inv_main530_5 var3 var2 var1 var0) (and (is-O_item (read var3 var0)) (not (is-O_item (read var3 var0))))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Heap)) (not (and (inv_main_3 var3 var2 var1 var0) (not (is-O_item (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Heap)) (not (and (inv_main_3 var3 var2 var1 var0) (and (and (is-O_item (read var3 var0)) (not (= (|item::next| (getitem (read var3 var0))) nullAddr))) (not (is-O_item (read var3 var0))))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Heap)) (not (and (inv_main_3 var3 var2 var1 var0) (and (and (and (is-O_item (read var3 var0)) (not (= (|item::next| (getitem (read var3 var0))) nullAddr))) (is-O_item (read var3 var0))) (not (is-O_item (read var3 (|item::next| (getitem (read var3 var0)))))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Heap)) (not (and (inv_main532_18 var4 var3 var2 var1 var0) (not (is-O_item (read var4 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Heap)) (not (and (inv_main532_18 var4 var3 var2 var1 var0) (and (is-O_item (read var4 var1)) (not (is-O_item (read var4 var1))))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main543_9 var1 var0) (not (is-O_item (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main_9 var1 var0) (not (is-O_item (read var1 var0)))))))
(check-sat)
