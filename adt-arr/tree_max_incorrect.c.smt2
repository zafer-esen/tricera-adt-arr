(set-info :source |
    Benchmark: C_VC
    Output by Princess (http://www.philipp.ruemmer.org/princess.shtml)
|)
(set-info :status unsat)
;===============================================================================
; Encoding of Heap sorts and operations
;-------------------------------------------------------------------------------
(define-sort Addr() Int)
(declare-datatypes ((HeapObject 0) (node 0))
                   (((O_Int (getInt Int)) (O_Addr (getAddr Addr)) (O_node (getnode node)) (defObj))
                   ((node (data Int) (left Addr) (right Addr)))))
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
(declare-fun check0 (Heap Addr Int Heap Addr Int) Bool)
(declare-fun check1 (Heap Addr Int Heap Addr Int) Bool)
(declare-fun check10 (Heap Addr Int Heap Addr Int Addr Int) Bool)
(declare-fun check2 (Heap Addr Int Heap Addr Int) Bool)
(declare-fun check3 (Heap Addr Int Heap Addr Int) Bool)
(declare-fun check4 (Heap Addr Int Heap Addr Int) Bool)
(declare-fun check5 (Heap Addr Int Heap Addr Int) Bool)
(declare-fun check6 (Heap Addr Int Heap Addr Int) Bool)
(declare-fun check7 (Heap Addr Int Heap Addr Int) Bool)
(declare-fun check8 (Heap Addr Int Heap Addr Int) Bool)
(declare-fun check9 (Heap Addr Int Heap Addr Int Addr Int) Bool)
(declare-fun check_post (Heap Addr Int Heap) Bool)
(declare-fun check_pre (Heap Addr Int) Bool)
(declare-fun inv_main2 (Heap) Bool)
(declare-fun inv_main3 (Heap) Bool)
(declare-fun inv_main7 (Heap Addr Addr) Bool)
(declare-fun inv_main9 (Heap Addr Int Addr Int) Bool)
(declare-fun max0 (Heap Addr Heap Addr) Bool)
(declare-fun max1 (Heap Addr Heap Addr Int) Bool)
(declare-fun max10 (Heap Addr Heap Addr Int Int) Bool)
(declare-fun max3 (Heap Addr Heap Addr) Bool)
(declare-fun max4 (Heap Addr Heap Addr) Bool)
(declare-fun max5 (Heap Addr Heap Addr Addr) Bool)
(declare-fun max6 (Heap Addr Heap Addr Int) Bool)
(declare-fun max7 (Heap Addr Heap Addr Int Addr) Bool)
(declare-fun max8 (Heap Addr Heap Addr Int Int) Bool)
(declare-fun max9 (Heap Addr Heap Addr Int Int) Bool)
(declare-fun max_post (Heap Addr Heap Int) Bool)
(declare-fun max_pre (Heap Addr) Bool)
(declare-fun nondet_tree0 (Heap Heap) Bool)
(declare-fun nondet_tree1 (Heap Heap Addr) Bool)
(declare-fun nondet_tree10 (Heap Heap Addr) Bool)
(declare-fun nondet_tree11 (Heap Heap Addr) Bool)
(declare-fun nondet_tree12 (Heap Heap Addr) Bool)
(declare-fun nondet_tree3 (Heap Heap) Bool)
(declare-fun nondet_tree4 (Heap Heap) Bool)
(declare-fun nondet_tree5 (Heap Heap) Bool)
(declare-fun nondet_tree6 (Heap Heap Addr) Bool)
(declare-fun nondet_tree7 (Heap Heap Addr) Bool)
(declare-fun nondet_tree8 (Heap Heap Addr) Bool)
(declare-fun nondet_tree9 (Heap Heap Addr) Bool)
(declare-fun nondet_tree_post (Heap Heap Addr) Bool)
(declare-fun nondet_tree_pre (Heap) Bool)
(assert (inv_main2 emptyHeap))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Heap)) (or (not (and (inv_main3 var0) (nondet_tree_post var0 var2 var1))) (inv_main7 var2 var1 var1))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap)) (or (not (and (inv_main7 var0 var1 var2) (max_post var0 var2 var4 var3))) (inv_main9 var4 var1 var3 var1 var3))))
(assert (forall ((var0 Heap)) (or (not (inv_main2 var0)) (inv_main3 var0))))
(assert (forall ((var0 Heap)) (or (not (inv_main3 var0)) (nondet_tree_pre var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr)) (or (not (inv_main7 var0 var1 var2)) (max_pre var0 var2))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Addr) (var3 Addr) (var4 Int)) (or (not (inv_main9 var0 var3 var4 var2 var1)) (check_pre var0 var2 var1))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Addr)) (or (not (check_pre var0 var2 var1)) (check0 var0 var2 var1 var0 var2 var1))))
(assert (forall ((var0 Heap) (var1 Heap) (var2 Addr) (var3 Int) (var4 Int) (var5 Addr)) (or (not (and (check0 var0 var5 var4 var1 var2 var3) (not (= var5 nullAddr)))) (check3 var0 var5 var4 var1 var2 var3))))
(assert (forall ((var0 Heap) (var1 Heap) (var2 Addr) (var3 Int) (var4 Int) (var5 Addr)) (or (not (and (check0 var0 var5 var4 var1 var2 var3) (= var5 nullAddr))) (check4 var0 var5 var4 var1 var2 var3))))
(assert (forall ((var0 Heap) (var1 Heap) (var2 Addr) (var3 Int) (var4 Int) (var5 Addr)) (or (not (check3 var0 var5 var4 var1 var2 var3)) (check5 var0 var5 var4 var1 var2 var3))))
(assert (forall ((var0 Heap) (var1 Heap) (var2 Addr) (var3 Int) (var4 Int) (var5 Addr)) (or (not (check5 var0 var5 var4 var1 var2 var3)) (check8 var0 var5 var4 var1 var2 var3))))
(assert (forall ((var0 Heap) (var1 Heap) (var2 Int) (var3 Addr) (var4 Int) (var5 Int) (var6 Addr)) (or (not (and (check8 var0 var6 var5 var1 var3 var4) (not (= var2 0)))) (check6 var0 var6 var5 var1 var3 var4))))
(assert (forall ((var0 Heap) (var1 Heap) (var2 Int) (var3 Addr) (var4 Int) (var5 Int) (var6 Addr)) (or (not (and (check8 var0 var6 var5 var1 var3 var4) (= var2 0))) (check7 var0 var6 var5 var1 var3 var4))))
(assert (forall ((var0 Heap) (var1 Heap) (var2 Addr) (var3 Int) (var4 Int) (var5 Addr)) (or (not (check6 var0 var5 var4 var1 var2 var3)) (check9 var0 var5 var4 var1 var2 var3 (left (getnode (read var0 var5))) var4))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Heap) (var5 Int) (var6 Int) (var7 Int) (var8 Addr)) (or (not (and (check9 var0 var8 var6 var2 var3 var5 var1 var7) (check_post var0 var1 var7 var4))) (check2 var4 var8 var6 var2 var3 var5))))
(assert (forall ((var0 Heap) (var1 Heap) (var2 Addr) (var3 Int) (var4 Int) (var5 Addr)) (or (not (check7 var0 var5 var4 var1 var2 var3)) (check10 var0 var5 var4 var1 var2 var3 (right (getnode (read var0 var5))) var4))))
(assert (forall ((var0 Heap) (var1 Heap) (var2 Heap) (var3 Addr) (var4 Int) (var5 Addr) (var6 Int) (var7 Int) (var8 Addr)) (or (not (and (check10 var0 var8 var7 var2 var5 var6 var3 var4) (check_post var0 var3 var4 var1))) (check2 var1 var8 var7 var2 var5 var6))))
(assert (forall ((var0 Heap) (var1 Heap) (var2 Addr) (var3 Int) (var4 Int) (var5 Addr)) (or (not (check4 var0 var5 var4 var1 var2 var3)) (check2 var0 var5 var4 var1 var2 var3))))
(assert (forall ((var0 Heap) (var1 Heap) (var2 Addr) (var3 Int) (var4 Int) (var5 Addr)) (or (not (check2 var0 var5 var4 var1 var2 var3)) (check1 var0 var5 var4 var1 var2 var3))))
(assert (forall ((var0 Heap) (var1 Heap) (var2 Addr) (var3 Int) (var4 Int) (var5 Addr)) (or (not (check1 var0 var5 var4 var1 var2 var3)) (check_post var1 var2 var3 var0))))
(assert (forall ((var0 Heap) (var1 Heap) (var2 Addr) (var3 Int) (var4 Int) (var5 Addr)) (not (and (check3 var0 var5 var4 var1 var2 var3) (not (is-O_node (read var0 var5)))))))
(assert (forall ((var0 Heap) (var1 Heap) (var2 Addr) (var3 Int) (var4 Int) (var5 Addr)) (not (and (check3 var0 var5 var4 var1 var2 var3) (not (<= 0 (+ var4 (* (- 1) (data (getnode (read var0 var5)))))))))))
(assert (forall ((var0 Heap) (var1 Heap) (var2 Addr) (var3 Int) (var4 Int) (var5 Addr)) (not (and (check6 var0 var5 var4 var1 var2 var3) (not (is-O_node (read var0 var5)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Int) (var5 Int) (var6 Int) (var7 Addr)) (or (not (check9 var0 var7 var5 var2 var3 var4 var1 var6)) (check_pre var0 var1 var6))))
(assert (forall ((var0 Heap) (var1 Heap) (var2 Addr) (var3 Int) (var4 Int) (var5 Addr)) (not (and (check7 var0 var5 var4 var1 var2 var3) (not (is-O_node (read var0 var5)))))))
(assert (forall ((var0 Heap) (var1 Heap) (var2 Addr) (var3 Int) (var4 Addr) (var5 Int) (var6 Int) (var7 Addr)) (or (not (check10 var0 var7 var6 var1 var4 var5 var2 var3)) (check_pre var0 var2 var3))))
(assert (forall ((var0 Heap) (var1 Addr)) (or (not (max_pre var0 var1)) (max0 var0 var1 var0 var1))))
(assert (forall ((var0 Heap) (var1 Heap) (var2 Addr) (var3 Addr)) (or (not (and (max0 var0 var3 var1 var2) (= var3 nullAddr))) (max3 var0 var3 var1 var2))))
(assert (forall ((var0 Heap) (var1 Heap) (var2 Addr) (var3 Addr)) (or (not (and (max0 var0 var3 var1 var2) (not (= var3 nullAddr)))) (max4 var0 var3 var1 var2))))
(assert (forall ((var0 Heap) (var1 Heap) (var2 Addr) (var3 Addr)) (or (not (max3 var0 var3 var1 var2)) (max1 var0 var3 var1 var2 (- 2147483648)))))
(assert (forall ((var0 Heap) (var1 Heap) (var2 Addr) (var3 Addr)) (or (not (max4 var0 var3 var1 var2)) (max5 var0 var3 var1 var2 (left (getnode (read var0 var3)))))))
(assert (forall ((var0 Heap) (var1 Heap) (var2 Addr) (var3 Int) (var4 Heap) (var5 Addr) (var6 Addr)) (or (not (and (max5 var0 var6 var1 var5 var2) (max_post var0 var2 var4 var3))) (max6 var4 var6 var1 var5 var3))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Heap) (var3 Addr) (var4 Addr)) (or (not (max6 var0 var4 var2 var3 var1)) (max7 var0 var4 var2 var3 var1 (right (getnode (read var0 var4)))))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Heap) (var3 Heap) (var4 Addr) (var5 Int) (var6 Addr) (var7 Addr)) (or (not (and (max7 var0 var7 var3 var6 var1 var4) (max_post var0 var4 var2 var5))) (max8 var2 var7 var3 var6 var1 var5))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Heap) (var3 Int) (var4 Addr) (var5 Addr)) (or (not (and (max8 var0 var5 var2 var4 var1 var3) (<= 0 (+ var1 (* (- 1) var3))))) (max9 var0 var5 var2 var4 var1 var3))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Heap) (var3 Int) (var4 Addr) (var5 Addr)) (or (not (and (max8 var0 var5 var2 var4 var1 var3) (not (<= 0 (+ var1 (* (- 1) var3)))))) (max10 var0 var5 var2 var4 var1 var3))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Heap) (var3 Int) (var4 Addr) (var5 Addr)) (or (not (max9 var0 var5 var2 var4 var1 var3)) (max1 var0 var5 var2 var4 var1))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Heap) (var3 Int) (var4 Addr) (var5 Addr)) (or (not (max10 var0 var5 var2 var4 var1 var3)) (max1 var0 var5 var2 var4 var3))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Heap) (var3 Addr) (var4 Addr)) (or (not (max1 var0 var4 var2 var3 var1)) (max_post var2 var3 var0 var1))))
(assert (forall ((var0 Heap) (var1 Heap) (var2 Addr) (var3 Addr)) (not (and (max4 var0 var3 var1 var2) (not (is-O_node (read var0 var3)))))))
(assert (forall ((var0 Heap) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Addr)) (or (not (max5 var0 var4 var1 var3 var2)) (max_pre var0 var2))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Heap) (var3 Addr) (var4 Addr)) (not (and (max6 var0 var4 var2 var3 var1) (not (is-O_node (read var0 var4)))))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr)) (or (not (max7 var0 var5 var2 var4 var1 var3)) (max_pre var0 var3))))
(assert (forall ((var0 Heap)) (or (not (nondet_tree_pre var0)) (nondet_tree0 var0 var0))))
(assert (forall ((var0 Heap) (var1 Heap)) (or (not (nondet_tree0 var0 var1)) (nondet_tree5 var0 var1))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Heap)) (or (not (and (nondet_tree5 var0 var2) (not (= var1 0)))) (nondet_tree3 var0 var2))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Heap)) (or (not (and (nondet_tree5 var0 var2) (= var1 0))) (nondet_tree4 var0 var2))))
(assert (forall ((var0 Heap) (var1 Heap)) (or (not (nondet_tree3 var0 var1)) (nondet_tree1 var0 var1 0))))
(assert (forall ((var0 Heap) (var1 Heap) (var2 node)) (or (not (nondet_tree4 var0 var1)) (nondet_tree6 (newHeap (alloc var0 (O_node var2))) var1 (newAddr (alloc var0 (O_node var2)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Heap)) (or (not (nondet_tree6 var0 var2 var1)) (nondet_tree8 var0 var2 var1))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Heap) (var3 Int)) (or (not (nondet_tree8 var0 var2 var1)) (nondet_tree7 (write var0 var1 (O_node (node var3 (left (getnode (read var0 var1))) (right (getnode (read var0 var1)))))) var2 var1))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Heap)) (or (not (nondet_tree7 var0 var2 var1)) (nondet_tree10 var0 var2 var1))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Heap) (var3 Heap) (var4 Addr)) (or (not (and (nondet_tree10 var0 var3 var1) (nondet_tree_post var0 var2 var4))) (nondet_tree9 (write var0 var1 (O_node (node (data (getnode (read var0 var1))) var4 (right (getnode (read var0 var1)))))) var3 var1))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Heap)) (or (not (nondet_tree9 var0 var2 var1)) (nondet_tree12 var0 var2 var1))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Heap)) (or (not (and (nondet_tree12 var0 var2 var1) (nondet_tree_post var0 var4 var3))) (nondet_tree11 (write var0 var1 (O_node (node (data (getnode (read var0 var1))) (left (getnode (read var0 var1))) var3))) var2 var1))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Heap)) (or (not (nondet_tree11 var0 var2 var1)) (nondet_tree1 var0 var2 var1))))
(assert (forall ((var0 Heap) (var1 Heap) (var2 Addr)) (or (not (nondet_tree1 var0 var1 var2)) (nondet_tree_post var1 var0 var2))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Heap)) (not (and (nondet_tree8 var0 var2 var1) (not (is-O_node (read var0 var1)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Heap)) (or (not (nondet_tree10 var0 var2 var1)) (nondet_tree_pre var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Heap) (var3 Heap) (var4 Addr)) (not (and (and (nondet_tree10 var0 var3 var1) (nondet_tree_post var0 var2 var4)) (not (is-O_node (read var0 var1)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Heap)) (or (not (nondet_tree12 var0 var2 var1)) (nondet_tree_pre var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Heap)) (not (and (and (nondet_tree12 var0 var2 var1) (nondet_tree_post var0 var4 var3)) (not (is-O_node (read var0 var1)))))))
(check-sat)
