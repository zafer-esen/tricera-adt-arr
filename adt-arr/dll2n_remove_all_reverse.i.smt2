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
(declare-fun inv_main12 (Heap Int Int Int Int Addr Addr) Bool)
(declare-fun inv_main15 (Heap Int Int Int Int Addr Addr Int) Bool)
(declare-fun inv_main18 (Heap Int Int Int Int Addr Addr) Bool)
(declare-fun inv_main19 (Heap Int Int Int Int Addr Addr) Bool)
(declare-fun inv_main22 (Heap Int Int Int Int Addr Addr) Bool)
(declare-fun inv_main28 (Heap Int Int Addr Int) Bool)
(declare-fun inv_main31 (Heap Int Int Addr Int Int) Bool)
(declare-fun inv_main38 (Heap Int Int Addr Int Int Addr Addr) Bool)
(declare-fun inv_main39 (Heap Int Int Addr Int Int Addr Addr) Bool)
(declare-fun inv_main4 (Heap Int Int) Bool)
(declare-fun inv_main41 (Heap Int Int Addr Int Int Addr Addr) Bool)
(declare-fun inv_main47 (Heap Int Int Addr Int) Bool)
(declare-fun inv_main8 (Heap Int Int Int Int Addr) Bool)
(assert (forall ((var0 Heap)) (or (not (= var0 emptyHeap)) (inv_main4 var0 2 1))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Int) (var5 Int) (var6 Int) (var7 Int) (var8 Heap) (var9 Int) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Heap)) (or (not (and (inv_main22 var8 var9 var1 var5 var4 var12 var11) (and (and (and (and (and (and (= var13 (write var8 var12 (O_node (node (data (getnode (read var8 var12))) (next (getnode (read var8 var12))) var11)))) (= var6 var9)) (= var2 var1)) (= var7 var5)) (= var0 var4)) (= var3 var12)) (= var10 var11)))) (inv_main8 var13 var6 var2 (+ var7 (- 1)) var0 var10))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Int) (var4 Int) (var5 Addr) (var6 Heap) (var7 Int) (var8 Int) (var9 Int) (var10 Addr) (var11 Addr) (var12 Heap) (var13 Addr)) (or (not (and (inv_main19 var6 var7 var2 var4 var3 var11 var10) (and (= var13 nullAddr) (and (and (and (and (and (and (= var12 (write var6 var10 (O_node (node (data (getnode (read var6 var10))) (next (getnode (read var6 var10))) nullAddr)))) (= var8 var7)) (= var9 var2)) (= var0 var4)) (= var1 var3)) (= var13 var11)) (= var5 var10))))) (inv_main8 var12 var8 var9 (+ var0 (- 1)) var1 var5))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Int)) (or (not (inv_main4 var0 var1 var2)) (inv_main8 var0 var1 var2 var1 var2 nullAddr))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Int) (var3 Addr) (var4 Addr) (var5 Int) (var6 Int)) (or (not (inv_main12 var0 var1 var2 var6 var5 var4 var3)) (inv_main18 (write var0 var3 (O_node (node var5 (next (getnode (read var0 var3))) (prev (getnode (read var0 var3)))))) var1 var2 var6 var5 var4 var3))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Int) (var3 Int) (var4 Addr)) (or (not (and (inv_main28 var0 var1 var2 var4 var3) (and (not (= nullAddr var4)) (not (<= 0 var3))))) (inv_main47 var0 var1 var2 var4 var3))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Int) (var3 Addr) (var4 Int) (var5 Addr) (var6 Int) (var7 Addr)) (or (not (and (inv_main38 var0 var2 var4 var7 var6 var1 var5 var3) (= (next (getnode (read var0 var3))) nullAddr))) (inv_main39 var0 var2 var4 var7 var6 var1 var5 var3))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Int) (var3 Int) (var4 Addr)) (or (not (and (inv_main28 var0 var1 var2 var4 var3) (<= 0 var3))) (inv_main31 var0 var1 var2 var4 var3 3))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Int) (var9 Int) (var10 Int) (var11 Addr) (var12 Addr) (var13 Int) (var14 Addr) (var15 Int) (var16 Heap)) (or (not (and (inv_main41 var7 var10 var3 var6 var15 var9 var14 var1) (and (and (and (and (and (and (and (and (= var16 var7) (= var8 var10)) (= var4 var3)) (= var12 var6)) (= var13 var15)) (= var0 var9)) (= var2 var14)) (= var5 var1)) (= var11 (next (getnode (read var7 var1))))))) (inv_main38 var16 var8 var4 var12 var13 var0 var2 var11))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Int) (var8 Int) (var9 Heap) (var10 Int) (var11 Addr) (var12 Addr)) (or (not (and (inv_main31 var1 var4 var6 var11 var10 var2) (and (and (and (and (and (and (and (= var9 var1) (= var8 var4)) (= var5 var6)) (= var12 var11)) (= var3 var10)) (= var7 var2)) (= var0 nullAddr)) (not (= nullAddr (next (getnode (read var1 var11)))))))) (inv_main38 var9 var8 var5 var12 var3 var7 var0 var12))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Int) (var3 Addr) (var4 Int) (var5 Addr) (var6 Int) (var7 Addr)) (or (not (and (inv_main38 var0 var2 var4 var7 var6 var1 var5 var3) (not (= (next (getnode (read var0 var3))) nullAddr)))) (inv_main41 var0 var2 var4 var7 var6 var1 var3 var3))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Addr) (var5 Int) (var6 Addr) (var7 Addr) (var8 Heap) (var9 Int) (var10 Int) (var11 Heap) (var12 Int) (var13 Addr) (var14 Int) (var15 Heap) (var16 Int) (var17 Addr) (var18 Int) (var19 Addr) (var20 Int) (var21 Int)) (or (not (and (inv_main39 var11 var14 var2 var6 var20 var12 var19 var1) (and (and (and (and (and (and (and (and (= var15 (write var11 var19 (O_node (node (data (getnode (read var11 var19))) nullAddr (prev (getnode (read var11 var19))))))) (= var21 var14)) (= var18 var2)) (= var17 var6)) (= var10 var20)) (= var9 var12)) (= var4 var19)) (= var13 var1)) (and (and (and (and (and (= var8 (write var15 var13 defObj)) (= var3 var21)) (= var0 var18)) (= var7 var17)) (= var16 var10)) (= var5 var9))))) (inv_main28 var8 var3 var0 var7 (+ var16 (- 1))))))
(assert (forall ((var0 Int) (var1 Heap) (var2 Int) (var3 Int) (var4 Int) (var5 Addr) (var6 Heap) (var7 Heap) (var8 Int) (var9 Int) (var10 Int) (var11 Addr) (var12 Int) (var13 Int) (var14 Int) (var15 Int) (var16 Int) (var17 Addr)) (or (not (and (inv_main31 var7 var10 var3 var5 var14 var9) (and (and (= nullAddr (next (getnode (read var7 var5)))) (and (and (and (and (and (= var6 (write var7 var5 defObj)) (= var2 var10)) (= var16 var3)) (= var17 var5)) (= var13 var14)) (= var0 var9))) (and (and (and (and (and (= var1 var6) (= var4 var2)) (= var15 var16)) (= var11 nullAddr)) (= var12 var13)) (= var8 var0))))) (inv_main28 var1 var4 var15 var11 (+ var12 (- 1))))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Int) (var3 Addr) (var4 Int) (var5 Int)) (or (not (and (inv_main8 var0 var1 var2 var5 var4 var3) (not (<= 0 (+ var5 (- 1)))))) (inv_main28 var0 var1 var2 var3 (+ var1 (- 1))))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Heap) (var5 Int) (var6 Int) (var7 Int) (var8 Addr) (var9 Int) (var10 Heap) (var11 Addr) (var12 Int) (var13 Addr)) (or (not (and (inv_main19 var4 var6 var0 var2 var1 var11 var8) (and (not (= var13 nullAddr)) (and (and (and (and (and (and (= var10 (write var4 var8 (O_node (node (data (getnode (read var4 var8))) (next (getnode (read var4 var8))) nullAddr)))) (= var7 var6)) (= var5 var0)) (= var12 var2)) (= var9 var1)) (= var13 var11)) (= var3 var8))))) (inv_main22 var10 var7 var5 var12 var9 var13 var3))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Int) (var3 Addr) (var4 Addr) (var5 Int) (var6 Int)) (or (not (inv_main18 var0 var1 var2 var6 var5 var4 var3)) (inv_main19 (write var0 var3 (O_node (node (data (getnode (read var0 var3))) var4 (prev (getnode (read var0 var3)))))) var1 var2 var6 var5 var4 var3))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Addr) (var4 Int) (var5 Int) (var6 Int) (var7 Int) (var8 Int) (var9 Heap) (var10 node) (var11 Heap) (var12 Int) (var13 Addr)) (or (not (and (inv_main8 var11 var12 var2 var5 var4 var13) (and (and (not (= nullAddr var0)) (and (and (and (and (and (and (= var9 (newHeap (alloc var11 (O_node var10)))) (= var8 var12)) (= var6 var2)) (= var7 var5)) (= var1 var4)) (= var3 var13)) (= var0 (newAddr (alloc var11 (O_node var10)))))) (<= 0 (+ var5 (- 1)))))) (inv_main12 var9 var8 var6 var7 var1 var3 var0))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Int) (var3 Int) (var4 Addr) (var5 Addr) (var6 Int) (var7 Int)) (or (not (inv_main15 var0 var1 var3 var7 var6 var5 var4 var2)) (inv_main15 var0 var1 var3 var7 var6 var5 var4 var2))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 node) (var4 Int) (var5 Int) (var6 Heap) (var7 Int) (var8 Addr) (var9 Addr) (var10 Int) (var11 Addr) (var12 Heap) (var13 Int)) (or (not (and (inv_main8 var6 var7 var0 var2 var1 var11) (and (and (= nullAddr var9) (and (and (and (and (and (and (= var12 (newHeap (alloc var6 (O_node var3)))) (= var4 var7)) (= var5 var0)) (= var10 var2)) (= var13 var1)) (= var8 var11)) (= var9 (newAddr (alloc var6 (O_node var3)))))) (<= 0 (+ var2 (- 1)))))) (inv_main15 var12 var4 var5 var10 var13 var8 var9 1))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Int) (var3 Addr) (var4 Addr) (var5 Int) (var6 Int)) (not (and (inv_main12 var0 var1 var2 var6 var5 var4 var3) (not (is-O_node (read var0 var3)))))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Int) (var3 Addr) (var4 Addr) (var5 Int) (var6 Int)) (not (and (inv_main18 var0 var1 var2 var6 var5 var4 var3) (not (is-O_node (read var0 var3)))))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Int) (var3 Addr) (var4 Addr) (var5 Int) (var6 Int)) (not (and (inv_main19 var0 var1 var2 var6 var5 var4 var3) (not (is-O_node (read var0 var3)))))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Int) (var3 Addr) (var4 Addr) (var5 Int) (var6 Int)) (not (and (inv_main22 var0 var1 var2 var6 var5 var4 var3) (not (is-O_node (read var0 var4)))))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Int) (var3 Int) (var4 Int) (var5 Addr)) (not (and (inv_main31 var0 var2 var3 var5 var4 var1) (not (is-O_node (read var0 var5)))))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Int) (var3 Addr) (var4 Int) (var5 Addr) (var6 Int) (var7 Addr)) (not (and (inv_main38 var0 var2 var4 var7 var6 var1 var5 var3) (not (is-O_node (read var0 var3)))))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Int) (var3 Addr) (var4 Int) (var5 Addr) (var6 Int) (var7 Addr)) (not (and (inv_main41 var0 var2 var4 var7 var6 var1 var5 var3) (not (is-O_node (read var0 var3)))))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Int) (var3 Addr) (var4 Int) (var5 Addr) (var6 Int) (var7 Addr)) (not (and (inv_main39 var0 var2 var4 var7 var6 var1 var5 var3) (not (is-O_node (read var0 var5)))))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Int) (var3 Int) (var4 Addr)) (not (inv_main47 var0 var1 var2 var4 var3))))
(check-sat)
