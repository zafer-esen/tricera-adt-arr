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
(declare-datatypes ((HeapObject 0) (node 0))
                   (((O_Int (getInt Int)) (O_UInt (getUInt Int)) (O_Addr (getAddr Addr)) (O_node (getnode node)) (defObj))
                   ((node (h Int) (n Addr)))))
(declare-datatypes ((AllocResHeap 0) (Heap 0))
                   (((AllocResHeap   (newHeap Heap) (newAddr Addr)))
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
(declare-fun inv_main12 (Heap Int Addr Addr Addr) Bool)
(declare-fun inv_main13 (Heap Int Addr Addr Addr) Bool)
(declare-fun inv_main17 (Heap Int Addr Addr Addr) Bool)
(declare-fun inv_main18 (Heap Int Addr Addr Addr) Bool)
(declare-fun inv_main23 (Heap Int Addr Addr Addr) Bool)
(declare-fun inv_main26 (Heap Int Addr Addr Addr Int) Bool)
(declare-fun inv_main29 (Heap Int Addr Addr Addr) Bool)
(declare-fun inv_main3 (Heap Int) Bool)
(declare-fun inv_main33 (Heap Int Addr Addr Addr) Bool)
(declare-fun inv_main37 (Heap Int Addr Addr Addr) Bool)
(declare-fun inv_main40 (Heap Int Addr Addr Addr) Bool)
(declare-fun inv_main44 (Heap Int Addr Addr Addr) Bool)
(declare-fun inv_main49 (Heap Int Addr Addr Addr) Bool)
(declare-fun inv_main53 (Heap Int Addr Addr Addr Addr) Bool)
(declare-fun inv_main57 (Heap Int Addr Addr Addr) Bool)
(declare-fun inv_main8 (Heap Int Addr Int) Bool)
(assert (forall ((var0 Heap)) (or (not (= var0 emptyHeap)) (inv_main3 var0 1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Int) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Int) (var12 Heap)) (or (not (and (inv_main53 var12 var11 var10 var9 var8 var7) (and (is-O_node (read var12 var8)) (and (and (and (and (and (and (= var6 var12) (= var5 var11)) (= var4 var10)) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var0 (n (getnode (read var12 var8)))))))) (inv_main49 (write var6 var1 defObj) var5 var4 var3 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap) (var5 Int) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Int) (var10 Heap)) (or (not (and (inv_main33 var10 var9 var8 var7 var6) (and (and (= var5 3) (is-O_node (read var10 var6))) (and (and (and (and (and (= var4 var10) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var0 var6)) (= var5 (h (getnode (read var10 var6)))))))) (inv_main49 var4 var3 var2 var1 var2))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Heap)) (or (not (inv_main8 var3 var2 var1 var0)) (inv_main8 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 node) (var2 Heap) (var3 Addr) (var4 Int) (var5 Heap)) (or (not (and (inv_main3 var5 var4) (and (= var3 nullAddr) (and (and (= var2 (newHeap (alloc var5 (O_node var1)))) (= var0 var4)) (= var3 (newAddr (alloc var5 (O_node var1)))))))) (inv_main8 var2 var0 var3 1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap)) (or (not (and (inv_main23 var4 var3 var2 var1 var0) (is-O_node (read var4 var0)))) (inv_main29 (write var4 var0 (O_node (node (h (getnode (read var4 var0))) var1))) var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Int) (var10 Heap)) (or (not (and (inv_main29 var10 var9 var8 var7 var6) (and (is-O_node (read var10 var6)) (and (and (and (and (and (= var5 var10) (= var4 var9)) (= var3 var8)) (= var2 var7)) (= var1 var6)) (= var0 (n (getnode (read var10 var6)))))))) (inv_main12 var5 var4 var3 var2 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 node) (var3 Heap) (var4 Addr) (var5 Int) (var6 Heap)) (or (not (and (inv_main3 var6 var5) (and (not (= var4 nullAddr)) (and (and (= var3 (newHeap (alloc var6 (O_node var2)))) (= var1 var5)) (= var4 (newAddr (alloc var6 (O_node var2)))))))) (inv_main12 var3 var1 var4 var0 var4))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Int) (var8 node) (var9 Heap) (var10 Heap) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Int) (var16 Heap)) (or (not (and (inv_main17 var16 var15 var14 var13 var12) (and (and (not (= var11 nullAddr)) (and (and (and (and (and (= var10 (newHeap (alloc var9 (O_node var8)))) (= var7 0)) (= var6 var5)) (= var4 var3)) (= var2 var1)) (= var11 (newAddr (alloc var9 (O_node var8)))))) (and (is-O_node (read var16 var12)) (and (and (and (and (= var9 (write var16 var12 (O_node (node 1 (n (getnode (read var16 var12))))))) (= var0 var15)) (= var5 var14)) (= var3 var13)) (= var1 var12)))))) (inv_main23 var10 var7 var6 var11 var2))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Int) (var8 node) (var9 Heap) (var10 Heap) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Int) (var16 Heap)) (or (not (and (inv_main18 var16 var15 var14 var13 var12) (and (and (not (= var11 nullAddr)) (and (and (and (and (and (= var10 (newHeap (alloc var9 (O_node var8)))) (= var7 1)) (= var6 var5)) (= var4 var3)) (= var2 var1)) (= var11 (newAddr (alloc var9 (O_node var8)))))) (and (is-O_node (read var16 var12)) (and (and (and (and (= var9 (write var16 var12 (O_node (node 2 (n (getnode (read var16 var12))))))) (= var0 var15)) (= var5 var14)) (= var3 var13)) (= var1 var12)))))) (inv_main23 var10 var7 var6 var11 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap) (var5 Int) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Int) (var10 Heap)) (or (not (and (inv_main49 var10 var9 var8 var7 var6) (and (and (not (= var5 3)) (is-O_node (read var10 var6))) (and (and (and (and (and (= var4 var10) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var0 var6)) (= var5 (h (getnode (read var10 var6)))))))) (inv_main53 var4 var3 var2 var1 var0 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap)) (or (not (and (inv_main12 var5 var4 var3 var2 var1) (and (not (= var4 0)) (not (= var0 0))))) (inv_main17 var5 var4 var3 var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Int) (var10 Heap)) (or (not (and (inv_main37 var10 var9 var8 var7 var6) (and (is-O_node (read var10 var6)) (and (and (and (and (and (= var5 var10) (= var4 var9)) (= var3 var8)) (= var2 var7)) (= var1 var6)) (= var0 (n (getnode (read var10 var6)))))))) (inv_main33 var5 var4 var3 var2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Int) (var9 Heap)) (or (not (and (inv_main13 var9 var8 var7 var6 var5) (and (is-O_node (read var9 var5)) (and (and (and (and (= var4 (write var9 var5 (O_node (node 3 (n (getnode (read var9 var5))))))) (= var3 var8)) (= var2 var7)) (= var1 var6)) (= var0 var5))))) (inv_main33 var4 1 var2 var1 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap) (var5 Int) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Int) (var10 Heap)) (or (not (and (inv_main40 var10 var9 var8 var7 var6) (and (and (= var5 1) (is-O_node (read var10 var6))) (and (and (and (and (and (= var4 var10) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var0 var6)) (= var5 (h (getnode (read var10 var6)))))))) (inv_main37 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap) (var5 Int) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Int) (var10 Heap)) (or (not (and (inv_main44 var10 var9 var8 var7 var6) (and (and (= var5 2) (is-O_node (read var10 var6))) (and (and (and (and (and (= var4 var10) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var0 var6)) (= var5 (h (getnode (read var10 var6)))))))) (inv_main37 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Int) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Int) (var10 Heap)) (or (not (and (inv_main33 var10 var9 var8 var7 var6) (and (= var5 0) (and (and (not (= var4 3)) (is-O_node (read var10 var6))) (and (and (and (and (and (= var3 var10) (= var5 var9)) (= var2 var8)) (= var1 var7)) (= var0 var6)) (= var4 (h (getnode (read var10 var6))))))))) (inv_main44 var3 1 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap) (var5 Int) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Int) (var10 Heap)) (or (not (and (inv_main40 var10 var9 var8 var7 var6) (and (and (not (= var5 1)) (is-O_node (read var10 var6))) (and (and (and (and (and (= var4 var10) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var0 var6)) (= var5 (h (getnode (read var10 var6)))))))) (inv_main57 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap) (var5 Int) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Int) (var10 Heap)) (or (not (and (inv_main44 var10 var9 var8 var7 var6) (and (and (not (= var5 2)) (is-O_node (read var10 var6))) (and (and (and (and (and (= var4 var10) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var0 var6)) (= var5 (h (getnode (read var10 var6)))))))) (inv_main57 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap)) (or (not (and (inv_main12 var5 var4 var3 var2 var1) (and (= var4 0) (not (= var0 0))))) (inv_main18 var5 var4 var3 var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Int) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Int) (var10 Heap)) (or (not (and (inv_main33 var10 var9 var8 var7 var6) (and (not (= var5 0)) (and (and (not (= var4 3)) (is-O_node (read var10 var6))) (and (and (and (and (and (= var3 var10) (= var5 var9)) (= var2 var8)) (= var1 var7)) (= var0 var6)) (= var4 (h (getnode (read var10 var6))))))))) (inv_main40 var3 0 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap)) (or (not (and (inv_main12 var5 var4 var3 var2 var1) (= var0 0))) (inv_main13 var5 var4 var3 var2 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap)) (or (not (inv_main26 var5 var4 var3 var2 var1 var0)) (inv_main26 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Int) (var8 node) (var9 Heap) (var10 Heap) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Int) (var16 Heap)) (or (not (and (inv_main17 var16 var15 var14 var13 var12) (and (and (= var11 nullAddr) (and (and (and (and (and (= var10 (newHeap (alloc var9 (O_node var8)))) (= var7 0)) (= var6 var5)) (= var4 var3)) (= var2 var1)) (= var11 (newAddr (alloc var9 (O_node var8)))))) (and (is-O_node (read var16 var12)) (and (and (and (and (= var9 (write var16 var12 (O_node (node 1 (n (getnode (read var16 var12))))))) (= var0 var15)) (= var5 var14)) (= var3 var13)) (= var1 var12)))))) (inv_main26 var10 var7 var6 var11 var2 1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Int) (var8 node) (var9 Heap) (var10 Heap) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Int) (var16 Heap)) (or (not (and (inv_main18 var16 var15 var14 var13 var12) (and (and (= var11 nullAddr) (and (and (and (and (and (= var10 (newHeap (alloc var9 (O_node var8)))) (= var7 1)) (= var6 var5)) (= var4 var3)) (= var2 var1)) (= var11 (newAddr (alloc var9 (O_node var8)))))) (and (is-O_node (read var16 var12)) (and (and (and (and (= var9 (write var16 var12 (O_node (node 2 (n (getnode (read var16 var12))))))) (= var0 var15)) (= var5 var14)) (= var3 var13)) (= var1 var12)))))) (inv_main26 var10 var7 var6 var11 var2 1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap)) (not (and (inv_main17 var4 var3 var2 var1 var0) (not (is-O_node (read var4 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap)) (not (and (inv_main18 var4 var3 var2 var1 var0) (not (is-O_node (read var4 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap)) (not (and (inv_main23 var4 var3 var2 var1 var0) (not (is-O_node (read var4 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap)) (not (and (inv_main29 var4 var3 var2 var1 var0) (not (is-O_node (read var4 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap)) (not (and (inv_main13 var4 var3 var2 var1 var0) (not (is-O_node (read var4 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap)) (not (and (inv_main33 var4 var3 var2 var1 var0) (not (is-O_node (read var4 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap)) (not (and (inv_main40 var4 var3 var2 var1 var0) (not (is-O_node (read var4 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap)) (not (and (inv_main44 var4 var3 var2 var1 var0) (not (is-O_node (read var4 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap)) (not (and (inv_main37 var4 var3 var2 var1 var0) (not (is-O_node (read var4 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap)) (not (and (inv_main49 var4 var3 var2 var1 var0) (not (is-O_node (read var4 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap)) (not (and (inv_main53 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var5 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap)) (not (inv_main57 var4 var3 var2 var1 var0))))
(check-sat)
