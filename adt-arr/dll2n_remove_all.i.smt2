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
                   (((O_Int (getInt Int)) (O_Addr (getAddr Addr)) (O_node (getnode node)) (defObj))
                   ((node (data Int) (next Addr) (prev Addr)))))
(declare-datatypes ((AllocResHeap 0) (Heap 0))
                   (((AllocResHeap   (newHeap Heap) (newAddr Addr)))
                    ((HeapCtor (HeapSize Int)
                               (HeapContents (Array Addr HeapObject))))))
(define-fun nullAddr  () Addr 0)
(define-fun defHeapObject    () HeapObject defObj)
(define-fun valid     ((h Heap) (p Addr)) Bool
  (and (>= (HeapSize h) p) (> p 0)))
(define-fun emptyHeap () Heap (
  HeapCtor 0 (( as const (Array Addr HeapObject)) defHeapObject)))
(define-fun read ((h Heap) (p Addr)) HeapObject
  (ite (valid h p)
       (select (HeapContents h) p)
       defHeapObject))
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
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Int) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Int) (var8 Int) (var9 Int) (var10 Int) (var11 Heap) (var12 Addr)) (or (not (and (inv_main31 var6 var7 var0 var5 var9 var10) (and (not (= var12 nullAddr)) (and (and (and (and (and (and (= var11 var6) (= var1 var7)) (= var2 var0)) (= var4 var5)) (= var8 var9)) (= var3 var10)) (= var12 (next (getnode (read var6 var5)))))))) (inv_main36 var11 var1 var2 var4 var8 var3 var12))))
(assert (forall ((var0 Int) (var1 Heap) (var2 Int) (var3 Int) (var4 Heap) (var5 Int) (var6 Int) (var7 Addr) (var8 Addr) (var9 Int) (var10 Addr) (var11 Int) (var12 Int) (var13 Addr)) (or (not (and (inv_main19 var4 var5 var11 var3 var0 var8 var7) (and (not (= var10 nullAddr)) (and (and (and (and (and (and (= var1 (write var4 var7 (O_node (node (data (getnode (read var4 var7))) (next (getnode (read var4 var7))) nullAddr)))) (= var2 var5)) (= var6 var11)) (= var9 var3)) (= var12 var0)) (= var10 var8)) (= var13 var7))))) (inv_main22 var1 var2 var6 var9 var12 var10 var13))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Int) (var4 Int)) (or (not (and (inv_main28 var2 var3 var0 var1 var4) (and (not (= nullAddr var1)) (not (<= 0 var4))))) (inv_main42 var2 var3 var0 var1 var4))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Int) (var4 Heap) (var5 Int) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Int) (var10 Addr) (var11 Int) (var12 Heap) (var13 Int)) (or (not (and (inv_main22 var4 var5 var11 var3 var1 var10 var8) (and (and (and (and (and (and (= var12 (write var4 var10 (O_node (node (data (getnode (read var4 var10))) (next (getnode (read var4 var10))) var8)))) (= var0 var5)) (= var2 var11)) (= var13 var3)) (= var9 var1)) (= var6 var10)) (= var7 var8)))) (inv_main8 var12 var0 var2 (+ var13 (- 1)) var9 var7))))
(assert (forall ((var0 Int) (var1 Int) (var2 Heap) (var3 Int) (var4 Addr) (var5 Int) (var6 Addr) (var7 Int) (var8 Addr) (var9 Int) (var10 Addr) (var11 Int) (var12 Int) (var13 Heap)) (or (not (and (inv_main19 var2 var3 var11 var1 var0 var8 var4) (and (= var10 nullAddr) (and (and (and (and (and (and (= var13 (write var2 var4 (O_node (node (data (getnode (read var2 var4))) (next (getnode (read var2 var4))) nullAddr)))) (= var12 var3)) (= var9 var11)) (= var7 var1)) (= var5 var0)) (= var10 var8)) (= var6 var4))))) (inv_main8 var13 var12 var9 (+ var7 (- 1)) var5 var6))))
(assert (forall ((var0 Int) (var1 Heap) (var2 Int)) (or (not (inv_main4 var1 var2 var0)) (inv_main8 var1 var2 var0 var2 var0 nullAddr))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Int) (var4 Heap) (var5 Int) (var6 Addr) (var7 Addr)) (or (not (inv_main15 var4 var5 var0 var3 var1 var7 var6 var2)) (inv_main15 var4 var5 var0 var3 var1 var7 var6 var2))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 node) (var4 Int) (var5 Heap) (var6 Int) (var7 Addr) (var8 Addr) (var9 Int) (var10 Int) (var11 Heap) (var12 Int) (var13 Int)) (or (not (and (inv_main8 var5 var6 var10 var4 var1 var8) (and (and (= nullAddr var7) (and (and (and (and (and (and (= var11 (newHeap (alloc var5 (O_node var3)))) (= var0 var6)) (= var12 var10)) (= var9 var4)) (= var13 var1)) (= var2 var8)) (= var7 (newAddr (alloc var5 (O_node var3)))))) (<= 0 (+ var4 (- 1)))))) (inv_main15 var11 var0 var12 var9 var13 var2 var7 1))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr)) (or (not (inv_main18 var3 var4 var0 var2 var1 var6 var5)) (inv_main19 (write var3 var5 (O_node (node (data (getnode (read var3 var5))) var6 (prev (getnode (read var3 var5)))))) var4 var0 var2 var1 var6 var5))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Heap) (var3 Int) (var4 Int) (var5 Addr) (var6 Int) (var7 Int) (var8 Addr) (var9 Heap) (var10 Int) (var11 Addr) (var12 Int) (var13 Int) (var14 Int) (var15 Addr) (var16 Heap) (var17 Int) (var18 Int) (var19 Addr) (var20 Int)) (or (not (and (inv_main36 var2 var3 var12 var15 var7 var18 var11) (and (and (and (and (and (and (and (= var16 (write var9 var0 defObj)) (= var1 var4)) (= var14 var10)) (= var19 var0)) (= var20 var13)) (= var17 var6)) (= var5 var8)) (and (and (and (and (and (and (= var9 (write var2 var11 (O_node (node (data (getnode (read var2 var11))) (next (getnode (read var2 var11))) nullAddr)))) (= var4 var3)) (= var10 var12)) (= var0 var15)) (= var13 var7)) (= var6 var18)) (= var8 var11))))) (inv_main28 var16 var1 var14 var5 (+ var20 (- 1))))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Heap) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Int) (var8 Int) (var9 Int) (var10 Addr) (var11 Int) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Heap) (var16 Int) (var17 Int) (var18 Int) (var19 Addr)) (or (not (and (inv_main31 var2 var3 var9 var12 var4 var18) (and (and (and (and (and (and (and (= var15 (write var0 var13 defObj)) (= var7 var5)) (= var6 var1)) (= var10 var13)) (= var8 var17)) (= var11 var16)) (= var19 var14)) (and (= var14 nullAddr) (and (and (and (and (and (and (= var0 var2) (= var5 var3)) (= var1 var9)) (= var13 var12)) (= var17 var4)) (= var16 var18)) (= var14 (next (getnode (read var2 var12))))))))) (inv_main28 var15 var7 var6 var19 (+ var8 (- 1))))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Heap) (var4 Int) (var5 Addr)) (or (not (and (inv_main8 var3 var4 var0 var2 var1 var5) (not (<= 0 (+ var2 (- 1)))))) (inv_main28 var3 var4 var0 var5 (+ var4 (- 1))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Int) (var4 Int)) (or (not (and (inv_main28 var2 var3 var0 var1 var4) (<= 0 var4))) (inv_main31 var2 var3 var0 var1 var4 3))))
(assert (forall ((var0 node) (var1 Int) (var2 Int) (var3 Int) (var4 Heap) (var5 Int) (var6 Addr) (var7 Addr) (var8 Heap) (var9 Addr) (var10 Int) (var11 Int) (var12 Int) (var13 Int)) (or (not (and (inv_main8 var4 var5 var10 var3 var2 var7) (and (and (not (= nullAddr var9)) (and (and (and (and (and (and (= var8 (newHeap (alloc var4 (O_node var0)))) (= var12 var5)) (= var1 var10)) (= var13 var3)) (= var11 var2)) (= var6 var7)) (= var9 (newAddr (alloc var4 (O_node var0)))))) (<= 0 (+ var3 (- 1)))))) (inv_main12 var8 var12 var1 var13 var11 var6 var9))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr)) (or (not (inv_main12 var3 var4 var0 var2 var1 var6 var5)) (inv_main18 (write var3 var5 (O_node (node var1 (next (getnode (read var3 var5))) (prev (getnode (read var3 var5)))))) var4 var0 var2 var1 var6 var5))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr)) (not (and (inv_main12 var3 var4 var0 var2 var1 var6 var5) (not (is-O_node (read var3 var5)))))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr)) (not (and (inv_main18 var3 var4 var0 var2 var1 var6 var5) (not (is-O_node (read var3 var5)))))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr)) (not (and (inv_main19 var3 var4 var0 var2 var1 var6 var5) (not (is-O_node (read var3 var5)))))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr)) (not (and (inv_main22 var3 var4 var0 var2 var1 var6 var5) (not (is-O_node (read var3 var6)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Int) (var4 Int) (var5 Int)) (not (and (inv_main31 var2 var3 var0 var1 var4 var5) (not (is-O_node (read var2 var1)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Heap) (var4 Int) (var5 Int) (var6 Int)) (not (and (inv_main36 var3 var4 var1 var2 var5 var6 var0) (not (is-O_node (read var3 var0)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Int) (var4 Int)) (not (inv_main42 var2 var3 var0 var1 var4))))
(check-sat)
