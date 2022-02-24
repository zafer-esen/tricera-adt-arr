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
(declare-const allDefHeapObject (Array Addr HeapObject))
(define-fun emptyHeap () Heap (HeapCtor 0 allDefHeapObject))
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
(define-fun Heap-eq     ((h1 Heap) (h2 Heap)) Bool
  (forall ((p Addr))
          (and (= (valid h1 p) (valid h2 p))
               (= (read h1 p) (read h2 p)))))
;===============================================================================
(declare-fun inv_main12 (Heap Int Int Int Int Addr Int) Bool)
(declare-fun inv_main15 (Heap Int Int Int Int Addr) Bool)
(declare-fun inv_main16 (Heap Int Int Int Int Addr) Bool)
(declare-fun inv_main18 (Heap Int Int Int Int Addr Addr) Bool)
(declare-fun inv_main19 (Heap Int Int Int Int Addr Addr) Bool)
(declare-fun inv_main22 (Heap Int Int Int Int Addr Addr Addr) Bool)
(declare-fun inv_main25 (Heap Int Int Int Int Addr Addr Addr Int) Bool)
(declare-fun inv_main28 (Heap Int Int Int Int Addr Addr Addr) Bool)
(declare-fun inv_main29 (Heap Int Int Int Int Addr Addr Addr) Bool)
(declare-fun inv_main32 (Heap Int Int Int Int Addr Addr) Bool)
(declare-fun inv_main36 (Heap Int Int Addr Int Addr) Bool)
(declare-fun inv_main37 (Heap Int Int Addr Int Addr) Bool)
(declare-fun inv_main39 (Heap Int Int Addr Int Addr) Bool)
(declare-fun inv_main4 (Heap Int Int) Bool)
(declare-fun inv_main42 (Heap Int Int Addr Int Addr) Bool)
(declare-fun inv_main45 (Heap Int Int Addr Int Addr) Bool)
(declare-fun inv_main51 (Heap Int Int Addr Int Addr) Bool)
(declare-fun inv_main52 (Heap Int Int Addr Int Addr) Bool)
(declare-fun inv_main57 (Heap Int Int Addr Int Addr) Bool)
(declare-fun inv_main9 (Heap Int Int Int Int Addr) Bool)
(assert (forall ((var0 Heap)) (or (not (= var0 emptyHeap)) (inv_main4 var0 5 1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Heap) (var6 Addr)) (or (not (and (inv_main18 var5 var3 var4 var2 var0 var1 var6) (not (<= 0 (+ (+ var2 (- 1)) (- 1)))))) (inv_main19 var5 var3 var4 var2 var0 var1 var6))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Addr) (var5 Int) (var6 Int) (var7 Int) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Heap) (var12 Heap)) (or (not (and (inv_main42 var12 var1 var2 var4 var0 var10) (and (not (= var3 var8)) (and (and (and (and (and (and (= var11 var12) (= var7 var1)) (= var6 var2)) (= var8 var4)) (= var5 var0)) (= var9 var10)) (= var3 (next (getnode (read var12 var10)))))))) (inv_main36 var11 var7 var6 var8 (+ var5 1) var3))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Int) (var4 Int) (var5 Heap) (var6 Addr) (var7 Int) (var8 Int) (var9 Int) (var10 Addr) (var11 Int) (var12 Addr) (var13 Heap)) (or (not (and (inv_main32 var13 var8 var3 var7 var0 var2 var6) (and (and (and (and (and (and (= var5 (write var13 var6 (O_node (node (data (getnode (read var13 var6))) (next (getnode (read var13 var6))) var2)))) (= var11 var8)) (= var9 var3)) (= var1 var7)) (= var4 var0)) (= var12 var2)) (= var10 var6)))) (inv_main36 var5 var11 var9 var10 1 var10))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Heap)) (or (not (inv_main15 var5 var3 var4 var2 var0 var1)) (inv_main16 (write var5 var1 (O_node (node (data (getnode (read var5 var1))) (next (getnode (read var5 var1))) var1))) var3 var4 var2 var0 var1))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main36 var5 var1 var2 var3 var0 var4) (not (= var2 (data (getnode (read var5 var4))))))) (inv_main57 var5 var1 var2 var3 var0 var4))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main51 var5 var1 var2 var3 var0 var4) (not (= var0 (data (getnode (read var5 var4))))))) (inv_main57 var5 var1 var2 var3 var0 var4))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Addr) (var5 Int) (var6 Int) (var7 Int) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Heap) (var12 Heap)) (or (not (and (inv_main42 var12 var1 var2 var4 var0 var10) (and (= var3 var8) (and (and (and (and (and (and (= var11 var12) (= var7 var1)) (= var6 var2)) (= var8 var4)) (= var5 var0)) (= var9 var10)) (= var3 (next (getnode (read var12 var10)))))))) (inv_main37 var11 var7 var6 var8 (+ var5 1) var3))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main36 var5 var1 var2 var3 var0 var4) (= var2 (data (getnode (read var5 var4)))))) (inv_main39 var5 var1 var2 var3 var0 var4))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Addr) (var6 Heap) (var7 Addr)) (or (not (inv_main28 var6 var3 var4 var2 var0 var1 var7 var5)) (inv_main29 (write var6 var5 (O_node (node var0 (next (getnode (read var6 var5))) (prev (getnode (read var6 var5)))))) var3 var4 var2 var0 var1 var7 var5))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main51 var5 var1 var2 var3 var0 var4) (= var0 (data (getnode (read var5 var4)))))) (inv_main52 var5 var1 var2 var3 var0 var4))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Addr) (var7 Heap) (var8 Addr)) (or (not (inv_main25 var7 var3 var5 var2 var0 var1 var8 var6 var4)) (inv_main25 var7 var3 var5 var2 var0 var1 var8 var6 var4))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Addr) (var6 Addr) (var7 Heap) (var8 node) (var9 Addr) (var10 Int) (var11 Int) (var12 Int) (var13 Addr) (var14 Int) (var15 Heap)) (or (not (and (inv_main18 var15 var11 var2 var10 var0 var1 var5) (and (and (= nullAddr var9) (and (and (and (and (and (and (and (= var7 (newHeap (alloc var15 (O_node var8)))) (= var4 var11)) (= var12 var2)) (= var14 var10)) (= var3 var0)) (= var6 var1)) (= var13 var5)) (= var9 (newAddr (alloc var15 (O_node var8)))))) (<= 0 (+ (+ var10 (- 1)) (- 1)))))) (inv_main25 var7 var4 var12 var14 var3 var6 var13 var9 1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Heap) (var6 Addr)) (or (not (inv_main19 var5 var3 var4 var2 var0 var1 var6)) (inv_main32 (write var5 var1 (O_node (node (data (getnode (read var5 var1))) var6 (prev (getnode (read var5 var1)))))) var3 var4 var2 var0 var1 var6))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Heap)) (or (not (inv_main12 var6 var3 var4 var2 var0 var1 var5)) (inv_main12 var6 var3 var4 var2 var0 var1 var5))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Addr) (var7 node) (var8 Int) (var9 Heap)) (or (not (and (inv_main4 var9 var1 var3) (and (= nullAddr var6) (and (and (and (and (and (= var0 (newHeap (alloc var9 (O_node var7)))) (= var2 var1)) (= var5 var3)) (= var4 var1)) (= var8 var3)) (= var6 (newAddr (alloc var9 (O_node var7)))))))) (inv_main12 var0 var2 var5 var4 var8 var6 1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Int) (var4 Int) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Int) (var10 Int) (var11 Int) (var12 Int) (var13 Addr) (var14 Int) (var15 Heap)) (or (not (and (inv_main29 var15 var11 var4 var10 var0 var1 var7 var13) (and (and (and (and (and (and (and (= var2 (write var15 var7 (O_node (node (data (getnode (read var15 var7))) (next (getnode (read var15 var7))) var13)))) (= var12 var11)) (= var14 var4)) (= var9 var10)) (= var3 var0)) (= var5 var1)) (= var8 var7)) (= var6 var13)))) (inv_main18 var2 var12 var14 (+ var9 (- 1)) var3 var5 var6))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Int) (var5 Int) (var6 Int) (var7 Int) (var8 Int) (var9 Int) (var10 Heap) (var11 Heap)) (or (not (and (inv_main16 var11 var5 var6 var4 var1 var3) (and (and (and (and (and (= var10 (write var11 var3 (O_node (node var1 (next (getnode (read var11 var3))) (prev (getnode (read var11 var3))))))) (= var0 var5)) (= var8 var6)) (= var9 var4)) (= var7 var1)) (= var2 var3)))) (inv_main18 var10 var0 var8 var9 var7 var2 var2))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Int) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Int) (var9 Addr) (var10 Heap) (var11 Int) (var12 Heap)) (or (not (and (inv_main37 var10 var2 var4 var6 var1 var9) (and (and (and (and (and (and (= var12 var10) (= var8 var2)) (= var11 var4)) (= var7 var6)) (= var0 var1)) (= var3 var9)) (= var5 (prev (getnode (read var10 var9))))))) (inv_main45 var12 var8 var11 var7 var0 var5))))
(assert (forall ((var0 Int) (var1 node) (var2 Addr) (var3 Int) (var4 Addr) (var5 Addr) (var6 Int) (var7 Int) (var8 Int) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Int) (var13 Heap) (var14 Int) (var15 Int)) (or (not (and (inv_main18 var13 var7 var3 var6 var0 var2 var4) (and (and (not (= nullAddr var5)) (and (and (and (and (and (and (and (= var9 (newHeap (alloc var13 (O_node var1)))) (= var14 var7)) (= var12 var3)) (= var8 var6)) (= var15 var0)) (= var11 var2)) (= var10 var4)) (= var5 (newAddr (alloc var13 (O_node var1)))))) (<= 0 (+ (+ var6 (- 1)) (- 1)))))) (inv_main22 var9 var14 var12 var8 var15 var11 var10 var5))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Heap)) (or (not (inv_main9 var5 var3 var4 var2 var0 var1)) (inv_main15 (write var5 var1 (O_node (node (data (getnode (read var5 var1))) var1 (prev (getnode (read var5 var1)))))) var3 var4 var2 var0 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Addr) (var6 Heap) (var7 Addr)) (or (not (inv_main22 var6 var3 var4 var2 var0 var1 var7 var5)) (inv_main28 (write var6 var5 (O_node (node (data (getnode (read var6 var5))) var7 (prev (getnode (read var6 var5)))))) var3 var4 var2 var0 var1 var7 var5))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (inv_main39 var5 var1 var2 var3 var0 var4)) (inv_main42 (write var5 var4 (O_node (node var0 (next (getnode (read var5 var4))) (prev (getnode (read var5 var4)))))) var1 var2 var3 var0 var4))))
(assert (forall ((var0 Int) (var1 Int) (var2 node) (var3 Addr) (var4 Int) (var5 Int) (var6 Int) (var7 Int) (var8 Heap) (var9 Heap)) (or (not (and (inv_main4 var8 var4 var6) (and (not (= nullAddr var3)) (and (and (and (and (and (= var9 (newHeap (alloc var8 (O_node var2)))) (= var0 var4)) (= var7 var6)) (= var5 var4)) (= var1 var6)) (= var3 (newAddr (alloc var8 (O_node var2)))))))) (inv_main9 var9 var0 var7 var5 var1 var3))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Int) (var3 Int) (var4 Addr) (var5 Addr) (var6 Int) (var7 Int) (var8 Int) (var9 Int) (var10 Int) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Heap) (var16 Heap) (var17 Int)) (or (not (and (inv_main45 var16 var10 var3 var11 var8 var13) (and (and (and (and (and (and (= var15 (write var16 var11 (O_node (node (data (getnode (read var16 var11))) (next (getnode (read var16 var11))) nullAddr)))) (= var9 var10)) (= var7 var3)) (= var12 var11)) (= var2 var8)) (= var14 var13)) (and (and (and (and (and (= var0 var15) (= var17 var9)) (= var6 var7)) (= var4 nullAddr)) (= var1 var2)) (= var5 var14))))) (inv_main51 var0 var17 var6 var4 (+ var1 (- 1)) var5))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Int) (var8 Int) (var9 Int) (var10 Heap) (var11 Int) (var12 Addr) (var13 Int) (var14 Addr) (var15 Addr) (var16 Heap) (var17 Int) (var18 Int) (var19 Addr)) (or (not (and (inv_main52 var16 var9 var2 var12 var8 var15) (and (not (= var19 nullAddr)) (and (and (and (and (and (and (and (= var3 var16) (= var18 var9)) (= var17 var2)) (= var5 var12)) (= var11 var8)) (= var6 var15)) (= var4 (prev (getnode (read var16 var15))))) (and (and (and (and (and (and (= var10 (write var3 var6 defObj)) (= var13 var18)) (= var7 var17)) (= var0 var5)) (= var1 var11)) (= var14 var6)) (= var19 var4)))))) (inv_main51 var10 var13 var7 var0 (+ var1 (- 1)) var19))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Heap)) (not (and (inv_main9 var5 var3 var4 var2 var0 var1) (not (is-O_node (read var5 var1)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Heap)) (not (and (inv_main15 var5 var3 var4 var2 var0 var1) (not (is-O_node (read var5 var1)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Heap)) (not (and (inv_main16 var5 var3 var4 var2 var0 var1) (not (is-O_node (read var5 var1)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Addr) (var6 Heap) (var7 Addr)) (not (and (inv_main22 var6 var3 var4 var2 var0 var1 var7 var5) (not (is-O_node (read var6 var5)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Addr) (var6 Heap) (var7 Addr)) (not (and (inv_main28 var6 var3 var4 var2 var0 var1 var7 var5) (not (is-O_node (read var6 var5)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Addr) (var6 Heap) (var7 Addr)) (not (and (inv_main29 var6 var3 var4 var2 var0 var1 var7 var5) (not (is-O_node (read var6 var7)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Heap) (var6 Addr)) (not (and (inv_main19 var5 var3 var4 var2 var0 var1 var6) (not (is-O_node (read var5 var1)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Heap) (var6 Addr)) (not (and (inv_main32 var5 var3 var4 var2 var0 var1 var6) (not (is-O_node (read var5 var6)))))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap)) (not (and (inv_main36 var5 var1 var2 var3 var0 var4) (not (is-O_node (read var5 var4)))))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap)) (not (and (inv_main39 var5 var1 var2 var3 var0 var4) (not (is-O_node (read var5 var4)))))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap)) (not (and (inv_main42 var5 var1 var2 var3 var0 var4) (not (is-O_node (read var5 var4)))))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap)) (not (and (inv_main37 var5 var1 var2 var3 var0 var4) (not (is-O_node (read var5 var4)))))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap)) (not (and (inv_main45 var5 var1 var2 var3 var0 var4) (not (is-O_node (read var5 var3)))))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap)) (not (and (inv_main51 var5 var1 var2 var3 var0 var4) (not (is-O_node (read var5 var4)))))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap)) (not (and (inv_main52 var5 var1 var2 var3 var0 var4) (not (is-O_node (read var5 var4)))))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap)) (not (inv_main57 var5 var1 var2 var3 var0 var4))))
(check-sat)
