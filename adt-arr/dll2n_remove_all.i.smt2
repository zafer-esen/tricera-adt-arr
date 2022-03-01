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
                   ((node (data Int) (next Addr) (prev Addr)))))
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
(declare-fun inv_main12 (Heap Int Int Int Int Addr Addr) Bool)
(declare-fun inv_main15 (Heap Int Int Int Int Addr Addr Int) Bool)
(declare-fun inv_main18 (Heap Int Int Int Int Addr Addr) Bool)
(declare-fun inv_main19 (Heap Int Int Int Int Addr Addr) Bool)
(declare-fun inv_main22 (Heap Int Int Int Int Addr Addr) Bool)
(declare-fun inv_main28 (Heap Int Int Addr Int) Bool)
(declare-fun inv_main31 (Heap Int Int Addr Int Int) Bool)
(declare-fun inv_main36 (Heap Int Int Addr Int Int Addr) Bool)
(declare-fun inv_main4 (Heap Int Int) Bool)
(declare-fun inv_main42 (Heap Int Int Addr Int) Bool)
(declare-fun inv_main8 (Heap Int Int Int Int Addr) Bool)
(assert (forall ((var0 Heap)) (or (not (= var0 emptyHeap)) (inv_main4 var0 2 1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Addr) (var7 Int) (var8 Int) (var9 Int) (var10 Int) (var11 Addr) (var12 Heap) (var13 Heap) (var14 Addr) (var15 Int) (var16 Int) (var17 Addr) (var18 Int) (var19 Int) (var20 Heap)) (or (not (and (inv_main36 var20 var19 var18 var17 var16 var15 var14) (and (and (and (and (and (and (and (and (= var13 (write var12 var11 defObj)) (= var10 var9)) (= var8 var7)) (= var6 var11)) (= var5 var4)) (= var3 var2)) (= var1 var0)) (is-O_node (read var20 var14))) (and (and (and (and (and (and (= var12 (write var20 var14 (O_node (node (data (getnode (read var20 var14))) (next (getnode (read var20 var14))) nullAddr)))) (= var9 var19)) (= var7 var18)) (= var11 var17)) (= var4 var16)) (= var2 var15)) (= var0 var14))))) (inv_main28 var13 var10 var8 var1 (+ var5 (- 1))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Addr) (var7 Int) (var8 Int) (var9 Int) (var10 Int) (var11 Addr) (var12 Heap) (var13 Heap) (var14 Int) (var15 Int) (var16 Addr) (var17 Int) (var18 Int) (var19 Heap)) (or (not (and (inv_main31 var19 var18 var17 var16 var15 var14) (and (and (and (and (and (and (and (= var13 (write var12 var11 defObj)) (= var10 var9)) (= var8 var7)) (= var6 var11)) (= var5 var4)) (= var3 var2)) (= var1 var0)) (and (and (= var0 nullAddr) (is-O_node (read var19 var16))) (and (and (and (and (and (and (= var12 var19) (= var9 var18)) (= var7 var17)) (= var11 var16)) (= var4 var15)) (= var2 var14)) (= var0 (next (getnode (read var19 var16))))))))) (inv_main28 var13 var10 var8 var1 (+ var5 (- 1))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Int) (var4 Int) (var5 Heap)) (or (not (and (inv_main8 var5 var4 var3 var2 var1 var0) (not (<= 0 (+ var2 (- 1)))))) (inv_main28 var5 var4 var3 var0 (+ var4 (- 1))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Heap)) (or (not (and (inv_main28 var4 var3 var2 var1 var0) (and (not (= nullAddr var1)) (not (<= 0 var0))))) (inv_main42 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Heap)) (or (not (inv_main15 var7 var6 var5 var4 var3 var2 var1 var0)) (inv_main15 var7 var6 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Int) (var4 Int) (var5 node) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Int) (var10 Int) (var11 Int) (var12 Int) (var13 Heap)) (or (not (and (inv_main8 var13 var12 var11 var10 var9 var8) (and (and (= nullAddr var7) (and (and (and (and (and (and (= var6 (newHeap (alloc var13 (O_node var5)))) (= var4 var12)) (= var3 var11)) (= var2 var10)) (= var1 var9)) (= var0 var8)) (= var7 (newAddr (alloc var13 (O_node var5)))))) (<= 0 (+ var10 (- 1)))))) (inv_main15 var6 var4 var3 var2 var1 var0 var7 1))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Int) (var4 Int) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Int) (var10 Int) (var11 Int) (var12 Int) (var13 Heap)) (or (not (and (inv_main19 var13 var12 var11 var10 var9 var8 var7) (and (and (not (= var6 nullAddr)) (is-O_node (read var13 var7))) (and (and (and (and (and (and (= var5 (write var13 var7 (O_node (node (data (getnode (read var13 var7))) (next (getnode (read var13 var7))) nullAddr)))) (= var4 var12)) (= var3 var11)) (= var2 var10)) (= var1 var9)) (= var6 var8)) (= var0 var7))))) (inv_main22 var5 var4 var3 var2 var1 var6 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Int) (var4 Int) (var5 Heap) (var6 Addr) (var7 Int) (var8 Int) (var9 Addr) (var10 Int) (var11 Int) (var12 Heap)) (or (not (and (inv_main31 var12 var11 var10 var9 var8 var7) (and (and (not (= var6 nullAddr)) (is-O_node (read var12 var9))) (and (and (and (and (and (and (= var5 var12) (= var4 var11)) (= var3 var10)) (= var2 var9)) (= var1 var8)) (= var0 var7)) (= var6 (next (getnode (read var12 var9)))))))) (inv_main36 var5 var4 var3 var2 var1 var0 var6))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Heap)) (or (not (and (inv_main12 var6 var5 var4 var3 var2 var1 var0) (is-O_node (read var6 var0)))) (inv_main18 (write var6 var0 (O_node (node var2 (next (getnode (read var6 var0))) (prev (getnode (read var6 var0)))))) var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Heap)) (or (not (and (inv_main18 var6 var5 var4 var3 var2 var1 var0) (is-O_node (read var6 var0)))) (inv_main19 (write var6 var0 (O_node (node (data (getnode (read var6 var0))) var1 (prev (getnode (read var6 var0)))))) var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Heap)) (or (not (and (inv_main28 var4 var3 var2 var1 var0) (<= 0 var0))) (inv_main31 var4 var3 var2 var1 var0 3))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Int) (var4 Int) (var5 node) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Int) (var10 Int) (var11 Int) (var12 Int) (var13 Heap)) (or (not (and (inv_main8 var13 var12 var11 var10 var9 var8) (and (and (not (= nullAddr var7)) (and (and (and (and (and (and (= var6 (newHeap (alloc var13 (O_node var5)))) (= var4 var12)) (= var3 var11)) (= var2 var10)) (= var1 var9)) (= var0 var8)) (= var7 (newAddr (alloc var13 (O_node var5)))))) (<= 0 (+ var10 (- 1)))))) (inv_main12 var6 var4 var3 var2 var1 var0 var7))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Int) (var10 Int) (var11 Int) (var12 Int) (var13 Heap)) (or (not (and (inv_main22 var13 var12 var11 var10 var9 var8 var7) (and (is-O_node (read var13 var8)) (and (and (and (and (and (and (= var6 (write var13 var8 (O_node (node (data (getnode (read var13 var8))) (next (getnode (read var13 var8))) var7)))) (= var5 var12)) (= var4 var11)) (= var3 var10)) (= var2 var9)) (= var1 var8)) (= var0 var7))))) (inv_main8 var6 var5 var4 (+ var3 (- 1)) var2 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Int) (var4 Int) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Int) (var10 Int) (var11 Int) (var12 Int) (var13 Heap)) (or (not (and (inv_main19 var13 var12 var11 var10 var9 var8 var7) (and (and (= var6 nullAddr) (is-O_node (read var13 var7))) (and (and (and (and (and (and (= var5 (write var13 var7 (O_node (node (data (getnode (read var13 var7))) (next (getnode (read var13 var7))) nullAddr)))) (= var4 var12)) (= var3 var11)) (= var2 var10)) (= var1 var9)) (= var6 var8)) (= var0 var7))))) (inv_main8 var5 var4 var3 (+ var2 (- 1)) var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Heap)) (or (not (inv_main4 var2 var1 var0)) (inv_main8 var2 var1 var0 var1 var0 nullAddr))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Heap)) (not (and (inv_main12 var6 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var6 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Heap)) (not (and (inv_main18 var6 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var6 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Heap)) (not (and (inv_main19 var6 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var6 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Heap)) (not (and (inv_main22 var6 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var6 var1)))))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Int) (var4 Int) (var5 Heap)) (not (and (inv_main31 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var5 var2)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Addr) (var4 Int) (var5 Int) (var6 Heap)) (not (and (inv_main36 var6 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var6 var0)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Heap)) (not (inv_main42 var4 var3 var2 var1 var0))))
(check-sat)
