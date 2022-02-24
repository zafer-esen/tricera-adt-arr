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
                   ((node (h Int) (n Addr)))))
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
(declare-fun inv_main13 (Heap Int Int Addr Addr Addr) Bool)
(declare-fun inv_main14 (Heap Int Int Addr Addr Addr) Bool)
(declare-fun inv_main18 (Heap Int Int Addr Addr Addr) Bool)
(declare-fun inv_main22 (Heap Int Int Addr Addr Addr) Bool)
(declare-fun inv_main25 (Heap Int Int Addr Addr Addr Int) Bool)
(declare-fun inv_main28 (Heap Int Int Addr Addr Addr) Bool)
(declare-fun inv_main30 (Heap Int Int Addr Addr Addr) Bool)
(declare-fun inv_main34 (Heap Int Int Addr Addr Addr) Bool)
(declare-fun inv_main38 (Heap Int Int Addr Addr Addr) Bool)
(declare-fun inv_main4 (Heap Int Int) Bool)
(declare-fun inv_main41 (Heap Int Int Addr Addr Addr Int) Bool)
(declare-fun inv_main44 (Heap Int Int Addr Addr Addr) Bool)
(declare-fun inv_main46 (Heap Int Int Addr Addr Addr) Bool)
(declare-fun inv_main50 (Heap Int Int Addr Addr Addr) Bool)
(declare-fun inv_main51 (Heap Int Int Addr Addr Addr) Bool)
(declare-fun inv_main54 (Heap Int Int Addr Addr Addr) Bool)
(declare-fun inv_main56 (Heap Int Int Addr Addr Addr) Bool)
(declare-fun inv_main59 (Heap Int Int Addr Addr Addr) Bool)
(declare-fun inv_main62 (Heap Int Int Addr Addr Addr) Bool)
(declare-fun inv_main66 (Heap Int Int Addr Addr Addr) Bool)
(declare-fun inv_main68 (Heap Int Int Addr Addr Addr) Bool)
(declare-fun inv_main9 (Heap Int Int Addr Int) Bool)
(assert (forall ((var0 Heap)) (or (not (= var0 emptyHeap)) (inv_main4 var0 0 0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Heap) (var6 Int) (var7 Addr) (var8 Int) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Int)) (or (not (and (inv_main51 var5 var8 var0 var1 var2 var7) (and (not (= var4 2)) (and (and (and (and (and (and (= var3 var5) (= var6 var8)) (= var12 var0)) (= var10 var1)) (= var9 var2)) (= var11 var7)) (= var4 (h (getnode (read var5 var7)))))))) (inv_main56 var3 var6 var12 var10 var9 var11))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Int) (var6 Int)) (or (not (inv_main25 var3 var6 var0 var1 var2 var4 var5)) (inv_main25 var3 var6 var0 var1 var2 var4 var5))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Addr) (var4 Heap) (var5 Addr) (var6 node) (var7 Addr) (var8 Int) (var9 Addr) (var10 Addr) (var11 Int) (var12 Int) (var13 Addr) (var14 Int) (var15 Heap) (var16 Addr) (var17 Addr) (var18 Heap) (var19 Addr)) (or (not (and (inv_main18 var15 var8 var2 var13 var5 var7) (and (= var9 nullAddr) (and (and (and (and (and (and (and (= var18 (newHeap (alloc var4 (O_node var6)))) (= var11 var14)) (= var1 var12)) (= var17 var10)) (= var16 var0)) (= var3 var19)) (= var9 (newAddr (alloc var4 (O_node var6))))) (and (and (and (and (and (= var4 (write var15 var7 (O_node (node 1 (n (getnode (read var15 var7))))))) (= var14 var8)) (= var12 var2)) (= var10 var13)) (= var0 var5)) (= var19 var7)))))) (inv_main25 var18 var11 var1 var17 var9 var3 1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Int) (var9 Addr) (var10 Heap) (var11 Int) (var12 Int)) (or (not (and (inv_main54 var4 var12 var0 var1 var2 var9) (and (and (and (and (and (and (= var10 var4) (= var11 var12)) (= var8 var0)) (= var7 var1)) (= var6 var2)) (= var3 var9)) (= var5 (n (getnode (read var4 var9))))))) (inv_main50 var10 var11 var8 var7 var6 var5))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Heap) (var9 Int) (var10 Addr) (var11 Addr)) (or (not (and (inv_main46 var5 var9 var0 var2 var3 var7) (and (and (and (and (and (= var8 (write var5 var7 (O_node (node (h (getnode (read var5 var7))) 0)))) (= var1 var9)) (= var4 var0)) (= var11 var2)) (= var10 var3)) (= var6 var7)))) (inv_main50 var8 0 0 var11 var10 var11))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Int) (var10 Int) (var11 Addr) (var12 Int)) (or (not (and (inv_main51 var5 var10 var1 var2 var3 var8) (and (= var4 2) (and (and (and (and (and (and (= var7 var5) (= var12 var10)) (= var9 var1)) (= var11 var2)) (= var6 var3)) (= var0 var8)) (= var4 (h (getnode (read var5 var8)))))))) (inv_main59 var7 var12 (+ var9 1) var11 var6 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Int) (var6 Heap) (var7 Addr) (var8 Int) (var9 Addr) (var10 Int) (var11 Int) (var12 Heap)) (or (not (and (inv_main50 var6 var11 var1 var2 var3 var9) (and (not (= var5 1)) (and (and (and (and (and (and (= var12 var6) (= var10 var11)) (= var8 var1)) (= var4 var2)) (= var7 var3)) (= var0 var9)) (= var5 (h (getnode (read var6 var9)))))))) (inv_main51 var12 var10 var8 var4 var7 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Int) (var7 Heap) (var8 Int) (var9 Addr) (var10 Int) (var11 Heap) (var12 Addr)) (or (not (and (inv_main59 var7 var10 var1 var3 var4 var9) (and (and (and (and (and (and (= var11 var7) (= var6 var10)) (= var8 var1)) (= var0 var3)) (= var2 var4)) (= var12 var9)) (= var5 (n (getnode (read var7 var9))))))) (inv_main51 var11 var6 var8 var0 var2 var5))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Heap) (var6 Addr) (var7 Int) (var8 Int) (var9 Addr) (var10 Int) (var11 Int) (var12 Addr)) (or (not (and (inv_main50 var4 var11 var0 var2 var3 var9) (and (= var8 1) (and (and (and (and (and (and (= var5 var4) (= var10 var11)) (= var7 var0)) (= var6 var2)) (= var1 var3)) (= var12 var9)) (= var8 (h (getnode (read var4 var9)))))))) (inv_main54 var5 (+ var10 1) var7 var6 var1 var12))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Int) (var9 Int) (var10 Addr) (var11 Int) (var12 Addr)) (or (not (and (inv_main66 var6 var11 var1 var4 var5 var10) (and (not (= var3 nullAddr)) (and (and (and (and (and (and (= var0 var6) (= var8 var11)) (= var9 var1)) (= var7 var4)) (= var2 var5)) (= var12 var10)) (= var3 (n (getnode (read var6 var10)))))))) (inv_main68 var0 var8 var9 var7 var2 var12))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap) (var5 Addr) (var6 Int)) (or (not (and (inv_main14 var4 var6 var0 var1 var2 var5) (and (not (= var3 0)) (<= 0 (+ (+ 10 (* (- 1) var0)) (- 1)))))) (inv_main34 var4 var6 (+ var0 1) var1 var2 var5))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Heap) (var8 Addr) (var9 Int) (var10 Int) (var11 Int) (var12 Int)) (or (not (and (inv_main56 var6 var10 var2 var3 var4 var8) (and (and (= var9 3) (not (<= 0 (+ (+ (+ var12 var11) (- 20)) (- 1))))) (and (and (and (and (and (and (= var7 var6) (= var12 var10)) (= var11 var2)) (= var0 var3)) (= var1 var4)) (= var5 var8)) (= var9 (h (getnode (read var6 var8)))))))) (inv_main66 var7 var12 var11 var0 var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Int) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap) (var9 Addr) (var10 Int) (var11 Int) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Heap) (var17 Heap) (var18 Int)) (or (not (and (inv_main68 var16 var11 var1 var14 var3 var7) (and (and (and (and (and (and (and (= var8 var16) (= var0 var11)) (= var10 var1)) (= var15 var14)) (= var5 var3)) (= var2 var7)) (= var9 (n (getnode (read var16 var7))))) (and (and (and (and (and (= var17 (write var8 var2 defObj)) (= var4 var0)) (= var18 var10)) (= var13 var15)) (= var6 var9)) (= var12 var2))))) (inv_main66 var17 var4 var18 var13 var6 var6))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Int) (var7 Heap) (var8 Addr) (var9 Int) (var10 Addr) (var11 Int) (var12 Addr)) (or (not (and (inv_main44 var7 var11 var0 var3 var4 var8) (and (and (and (and (and (and (= var5 var7) (= var9 var11)) (= var6 var0)) (= var12 var3)) (= var1 var4)) (= var2 var8)) (= var10 (n (getnode (read var7 var8))))))) (inv_main14 var5 var9 var6 var12 var1 var10))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Int)) (or (not (and (inv_main13 var3 var5 var0 var1 var2 var4) (not (<= 0 (+ (+ 10 (* (- 1) var5)) (- 1)))))) (inv_main14 var3 var5 var0 var1 var2 var4))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Addr) (var6 Int)) (or (not (and (inv_main13 var3 var6 var0 var1 var2 var5) (and (= var4 0) (<= 0 (+ (+ 10 (* (- 1) var6)) (- 1)))))) (inv_main14 var3 var6 var0 var1 var2 var5))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Int) (var4 Int)) (or (not (inv_main9 var2 var3 var0 var1 var4)) (inv_main9 var2 var3 var0 var1 var4))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Heap) (var4 node) (var5 Heap) (var6 Int) (var7 Int)) (or (not (and (inv_main4 var3 var6 var0) (and (= var2 nullAddr) (and (and (and (= var5 (newHeap (alloc var3 (O_node var4)))) (= var7 var6)) (= var1 var0)) (= var2 (newAddr (alloc var3 (O_node var4)))))))) (inv_main9 var5 var7 var1 var2 1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Int)) (or (not (inv_main38 var3 var5 var0 var1 var2 var4)) (inv_main44 (write var3 var4 (O_node (node (h (getnode (read var3 var4))) var2))) var5 var0 var1 var2 var4))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Addr) (var6 Int)) (or (not (inv_main41 var3 var6 var0 var1 var2 var5 var4)) (inv_main41 var3 var6 var0 var1 var2 var5 var4))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 node) (var6 Addr) (var7 Addr) (var8 Int) (var9 Int) (var10 Addr) (var11 Int) (var12 Addr) (var13 Int) (var14 Heap) (var15 Heap) (var16 Heap) (var17 Addr) (var18 Int) (var19 Addr)) (or (not (and (inv_main34 var15 var8 var1 var12 var3 var6) (and (= var10 nullAddr) (and (and (and (and (and (and (and (= var16 (newHeap (alloc var14 (O_node var5)))) (= var13 var11)) (= var9 var18)) (= var7 var0)) (= var4 var2)) (= var19 var17)) (= var10 (newAddr (alloc var14 (O_node var5))))) (and (and (and (and (and (= var14 (write var15 var6 (O_node (node 2 (n (getnode (read var15 var6))))))) (= var11 var8)) (= var18 var1)) (= var0 var12)) (= var2 var3)) (= var17 var6)))))) (inv_main41 var16 var13 var9 var7 var10 var19 1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Int)) (or (not (inv_main22 var3 var5 var0 var1 var2 var4)) (inv_main28 (write var3 var4 (O_node (node (h (getnode (read var3 var4))) var2))) var5 var0 var1 var2 var4))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Addr) (var4 Heap) (var5 Addr) (var6 node) (var7 Addr) (var8 Int) (var9 Addr) (var10 Addr) (var11 Int) (var12 Int) (var13 Addr) (var14 Int) (var15 Heap) (var16 Addr) (var17 Addr) (var18 Heap) (var19 Addr)) (or (not (and (inv_main18 var15 var8 var2 var13 var5 var7) (and (not (= var9 nullAddr)) (and (and (and (and (and (and (and (= var18 (newHeap (alloc var4 (O_node var6)))) (= var11 var14)) (= var1 var12)) (= var17 var10)) (= var16 var0)) (= var3 var19)) (= var9 (newAddr (alloc var4 (O_node var6))))) (and (and (and (and (and (= var4 (write var15 var7 (O_node (node 1 (n (getnode (read var15 var7))))))) (= var14 var8)) (= var12 var2)) (= var10 var13)) (= var0 var5)) (= var19 var7)))))) (inv_main22 var18 var11 var1 var17 var9 var3))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Int) (var11 Addr) (var12 Heap)) (or (not (and (inv_main28 var6 var10 var0 var3 var4 var8) (and (and (and (and (and (and (= var12 var6) (= var2 var10)) (= var1 var0)) (= var9 var3)) (= var7 var4)) (= var11 var8)) (= var5 (n (getnode (read var6 var8))))))) (inv_main13 var12 var2 var1 var9 var7 var5))))
(assert (forall ((var0 Int) (var1 Heap) (var2 Int) (var3 node) (var4 Addr) (var5 Addr) (var6 Int) (var7 Int) (var8 Heap)) (or (not (and (inv_main4 var1 var7 var0) (and (not (= var4 nullAddr)) (and (and (and (= var8 (newHeap (alloc var1 (O_node var3)))) (= var6 var7)) (= var2 var0)) (= var4 (newAddr (alloc var1 (O_node var3)))))))) (inv_main13 var8 var6 var2 var4 var5 var4))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Int) (var10 Int) (var11 Addr) (var12 Int)) (or (not (and (inv_main56 var5 var10 var0 var1 var2 var8) (and (or (not (= var3 3)) (<= 0 (+ (+ (+ var9 var12) (- 20)) (- 1)))) (and (and (and (and (and (and (= var7 var5) (= var9 var10)) (= var12 var0)) (= var6 var1)) (= var4 var2)) (= var11 var8)) (= var3 (h (getnode (read var5 var8)))))))) (inv_main62 var7 var9 var12 var6 var4 var11))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Int)) (or (not (and (inv_main14 var3 var5 var0 var1 var2 var4) (not (<= 0 (+ (+ 10 (* (- 1) var0)) (- 1)))))) (inv_main30 var3 var5 var0 var1 var2 var4))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Addr) (var6 Int)) (or (not (and (inv_main14 var3 var6 var0 var1 var2 var5) (and (= var4 0) (<= 0 (+ (+ 10 (* (- 1) var0)) (- 1)))))) (inv_main30 var3 var6 var0 var1 var2 var5))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Int)) (or (not (inv_main30 var3 var5 var0 var1 var2 var4)) (inv_main46 (write var3 var4 (O_node (node 3 (n (getnode (read var3 var4)))))) var5 var0 var1 var2 var4))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 node) (var6 Addr) (var7 Addr) (var8 Int) (var9 Int) (var10 Addr) (var11 Int) (var12 Addr) (var13 Int) (var14 Heap) (var15 Heap) (var16 Heap) (var17 Addr) (var18 Int) (var19 Addr)) (or (not (and (inv_main34 var15 var8 var1 var12 var3 var6) (and (not (= var10 nullAddr)) (and (and (and (and (and (and (and (= var16 (newHeap (alloc var14 (O_node var5)))) (= var13 var11)) (= var9 var18)) (= var7 var0)) (= var4 var2)) (= var19 var17)) (= var10 (newAddr (alloc var14 (O_node var5))))) (and (and (and (and (and (= var14 (write var15 var6 (O_node (node 2 (n (getnode (read var15 var6))))))) (= var11 var8)) (= var18 var1)) (= var0 var12)) (= var2 var3)) (= var17 var6)))))) (inv_main38 var16 var13 var9 var7 var10 var19))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Int) (var6 Int)) (or (not (and (inv_main13 var3 var6 var0 var1 var2 var4) (and (not (= var5 0)) (<= 0 (+ (+ 10 (* (- 1) var6)) (- 1)))))) (inv_main18 var3 (+ var6 1) var0 var1 var2 var4))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Int)) (not (and (inv_main18 var3 var5 var0 var1 var2 var4) (not (is-O_node (read var3 var4)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Int)) (not (and (inv_main22 var3 var5 var0 var1 var2 var4) (not (is-O_node (read var3 var4)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Int)) (not (and (inv_main28 var3 var5 var0 var1 var2 var4) (not (is-O_node (read var3 var4)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Int)) (not (and (inv_main34 var3 var5 var0 var1 var2 var4) (not (is-O_node (read var3 var4)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Int)) (not (and (inv_main38 var3 var5 var0 var1 var2 var4) (not (is-O_node (read var3 var4)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Int)) (not (and (inv_main44 var3 var5 var0 var1 var2 var4) (not (is-O_node (read var3 var4)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Int)) (not (and (inv_main30 var3 var5 var0 var1 var2 var4) (not (is-O_node (read var3 var4)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Int)) (not (and (inv_main46 var3 var5 var0 var1 var2 var4) (not (is-O_node (read var3 var4)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Int)) (not (and (inv_main50 var3 var5 var0 var1 var2 var4) (not (is-O_node (read var3 var4)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Int)) (not (and (inv_main54 var3 var5 var0 var1 var2 var4) (not (is-O_node (read var3 var4)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Int)) (not (and (inv_main51 var3 var5 var0 var1 var2 var4) (not (is-O_node (read var3 var4)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Int)) (not (and (inv_main59 var3 var5 var0 var1 var2 var4) (not (is-O_node (read var3 var4)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Int)) (not (and (inv_main56 var3 var5 var0 var1 var2 var4) (not (is-O_node (read var3 var4)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Int)) (not (inv_main62 var3 var5 var0 var1 var2 var4))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Int)) (not (and (inv_main66 var3 var5 var0 var1 var2 var4) (not (is-O_node (read var3 var4)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Int)) (not (and (inv_main68 var3 var5 var0 var1 var2 var4) (not (is-O_node (read var3 var4)))))))
(check-sat)