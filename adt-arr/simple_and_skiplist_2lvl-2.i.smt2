(set-info :source |
    Benchmark: C_VC
    Output by Princess (http://www.philipp.ruemmer.org/princess.shtml)
|)
(set-info :status sat)
;===============================================================================
; Encoding of Heap sorts and operations
;-------------------------------------------------------------------------------
(define-sort Addr() Int)
(declare-datatypes ((HeapObject 0) (node 0) (sl_item 0) (sl 0))
                   (((O_Int (getInt Int)) (O_Addr (getAddr Addr)) (O_node (getnode node)) (O_sl_item (getsl_item sl_item)) (O_sl (getsl sl)) (defObj))
                   ((node (h Int) (n Addr)))
                   ((sl_item (n1 Addr) (n2 Addr)))
                   ((sl (head Addr) (tail Addr)))))
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
(declare-fun inv_main12 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main13 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main18 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main2 (Heap) Bool)
(declare-fun inv_main21 (Heap Addr Addr Addr Int) Bool)
(declare-fun inv_main24 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main26 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main30 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main31 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main32 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main42 (Heap Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main43 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main44 (Heap Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main45 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main46 (Heap Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main47 (Heap Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main49 (Heap Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main50 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main58 (Heap Addr Addr Addr Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main59 (Heap Addr Addr Addr Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main62 (Heap Addr Addr Addr Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main63 (Heap Addr Addr Addr Addr Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main68 (Heap Addr Addr Addr Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main7 (Heap Addr Int) Bool)
(declare-fun inv_main70 (Heap Addr Addr Addr Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main71 (Heap Addr Addr Addr Addr Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main76 (Heap Addr Addr Addr Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main78 (Heap Addr Addr Addr Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main79 (Heap Addr Addr Addr Addr Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main81 (Heap Addr Addr Addr Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main84 (Heap Addr Addr Addr Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main85 (Heap Addr Addr Addr Addr Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main90 (Heap Addr Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main92 (Heap Addr Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main93 (Heap Addr Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main96 (Heap Addr Addr Addr Addr Addr Addr Addr) Bool)
(assert (inv_main2 emptyHeap))
(assert (forall ((var0 node) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap) (var11 Addr) (var12 Addr) (var13 Addr)) (or (not (and (inv_main13 var4 var2 var8 var1) (and (not (= var13 nullAddr)) (and (and (and (and (and (= var10 (newHeap (alloc var3 (O_node var0)))) (= var6 var12)) (= var11 var7)) (= var5 var9)) (= var13 (newAddr (alloc var3 (O_node var0))))) (and (and (and (= var3 (write var4 var1 (O_node (node 1 (n (getnode (read var4 var1))))))) (= var12 var2)) (= var7 var8)) (= var9 var1)))))) (inv_main18 var10 var6 var13 var5))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr)) (or (not (inv_main43 var2 var1 var4 var0 var3)) (inv_main46 var2 var1 var4 var0 var3 (tail (getsl (read var2 var3)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Heap) (var14 Addr)) (or (not (and (inv_main92 var6 var3 var10 var0 var11 var7 var1) (and (and (and (and (and (and (and (= var13 var6) (= var9 var3)) (= var8 var10)) (= var14 var0)) (= var4 var11)) (= var5 var7)) (= var2 var1)) (= var12 (head (getsl (read var6 var7))))))) (inv_main93 var13 var9 var8 var14 var4 var5 var12))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr)) (or (not (inv_main68 var2 var1 var6 var0 var7 var3 var8 var4 var5)) (inv_main71 var2 var1 var6 var0 var7 var3 var8 var4 var5 (n1 (getsl_item (read var2 var8)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr)) (or (not (and (inv_main96 var6 var5 var10 var1 var11 var8 var2 var7) (and (and (and (and (and (and (= var9 (write var6 var8 (O_sl (sl var7 (tail (getsl (read var6 var8))))))) (= var0 var5)) (= var14 var10)) (= var3 var1)) (= var4 var11)) (= var12 var8)) (= var13 var2)))) (inv_main90 (write var9 var13 defObj) var0 var14 var3 var4 var12 var13))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap) (var5 Addr) (var6 Addr)) (or (not (and (inv_main50 var4 var2 var5 var1 var6) (= var3 0))) (inv_main90 var4 var2 var5 var1 var6 var6 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Addr)) (or (not (and (inv_main50 var6 var2 var7 var0 var8) (not (= var1 0)))) (inv_main58 var6 var2 var7 var0 var8 var8 var5 var4 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 sl) (var10 Addr) (var11 sl_item) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Heap)) (or (not (and (inv_main31 var3 var1 var7 var0) (and (and (and (and (and (and (= var15 (newHeap (alloc var2 (O_sl var9)))) (= var14 var5)) (= var10 var13)) (= var4 var6)) (= var8 (newAddr (alloc var2 (O_sl var9))))) (= var6 nullAddr)) (and (and (and (and (= var2 var3) (= var5 var1)) (= var13 var7)) (= var12 var0)) (= var6 (n (getnode (read var3 var0)))))))) (inv_main42 (newHeap (alloc var15 (O_sl_item var11))) var14 var10 var4 var8 (newAddr (alloc var15 (O_sl_item var11)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 sl) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Addr) (var11 sl_item) (var12 Addr) (var13 Addr) (var14 Addr)) (or (not (and (inv_main26 var3 var2 var5 var0) (and (and (and (and (and (and (= var1 (newHeap (alloc var7 (O_sl var6)))) (= var14 var9)) (= var12 var10)) (= var8 var9)) (= var4 (newAddr (alloc var7 (O_sl var6))))) (= var9 nullAddr)) (and (and (and (= var7 (write var3 var0 (O_node (node (h (getnode (read var3 var0))) 0)))) (= var9 var2)) (= var10 var5)) (= var13 var0))))) (inv_main42 (newHeap (alloc var1 (O_sl_item var11))) var14 var12 var8 var4 (newAddr (alloc var1 (O_sl_item var11)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 sl_item) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr)) (or (not (and (inv_main42 var5 var3 var10 var1 var8 var9) (and (and (and (and (= var0 (write var5 var8 (O_sl (sl var9 (tail (getsl (read var5 var8))))))) (= var7 var3)) (= var2 var10)) (= var11 var1)) (= var6 var8)))) (inv_main44 (newHeap (alloc var0 (O_sl_item var4))) var7 var2 var11 var6 (newAddr (alloc var0 (O_sl_item var4)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Int) (var8 Addr)) (or (not (and (inv_main30 var4 var2 var8 var0) (and (= var7 1) (and (and (and (and (= var1 var4) (= var6 var2)) (= var5 var8)) (= var3 var0)) (= var7 (h (getnode (read var4 var0)))))))) (inv_main31 var1 var6 var5 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr)) (or (not (inv_main81 var2 var1 var6 var0 var7 var3 var8 var4 var5)) (inv_main85 var2 var1 var6 var0 var7 var3 var8 var4 var5 (n2 (getsl_item (read var2 var4)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr)) (or (not (inv_main79 var3 var1 var7 var0 var8 var4 var9 var5 var6 var2)) (inv_main78 (write var3 var6 (O_sl_item (sl_item var2 (n2 (getsl_item (read var3 var6)))))) var1 var7 var0 var8 var4 var9 var5 var6))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr)) (or (not (inv_main12 var2 var1 var3 var0)) (inv_main26 (write var2 var0 (O_node (node 1 (n (getnode (read var2 var0)))))) var1 var3 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Int) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main24 var5 var3 var8 var0) (and (= var6 0) (and (and (and (and (= var9 var5) (= var4 var3)) (= var1 var8)) (= var7 var0)) (= var2 (n (getnode (read var5 var0)))))))) (inv_main12 var9 var4 var1 var2))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 node) (var3 Heap) (var4 Addr) (var5 Int)) (or (not (and (inv_main2 var3) (and (= var5 0) (and (not (= var4 nullAddr)) (and (= var1 (newHeap (alloc var3 (O_node var2)))) (= var4 (newAddr (alloc var3 (O_node var2))))))))) (inv_main12 var1 var4 var0 var4))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr)) (or (not (inv_main59 var2 var1 var6 var0 var7 var3 var8 var4 var5)) (inv_main63 var2 var1 var6 var0 var7 var3 var8 var4 var5 (n2 (getsl_item (read var2 var4)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr)) (or (not (inv_main45 var2 var1 var4 var0 var3)) (inv_main49 (write var2 (tail (getsl (read var2 var3))) (O_sl_item (sl_item nullAddr (n2 (getsl_item (read var2 (tail (getsl (read var2 var3))))))))) var1 var4 var0 var3 nullAddr))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Int) (var4 Addr)) (or (not (inv_main21 var2 var1 var4 var0 var3)) (inv_main21 var2 var1 var4 var0 var3))))
(assert (forall ((var0 node) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap) (var11 Addr) (var12 Addr) (var13 Addr)) (or (not (and (inv_main13 var4 var2 var8 var1) (and (= var13 nullAddr) (and (and (and (and (and (= var10 (newHeap (alloc var3 (O_node var0)))) (= var6 var12)) (= var11 var7)) (= var5 var9)) (= var13 (newAddr (alloc var3 (O_node var0))))) (and (and (and (= var3 (write var4 var1 (O_node (node 1 (n (getnode (read var4 var1))))))) (= var12 var2)) (= var7 var8)) (= var9 var1)))))) (inv_main21 var10 var6 var13 var5 1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr)) (or (not (inv_main44 var3 var1 var5 var0 var4 var2)) (inv_main43 (write var3 var4 (O_sl (sl (head (getsl (read var3 var4))) var2))) var1 var5 var0 var4))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr)) (or (not (inv_main47 var2 var1 var5 var0 var4 var3)) (inv_main45 (write var2 (head (getsl (read var2 var4))) (O_sl_item (sl_item (n1 (getsl_item (read var2 (head (getsl (read var2 var4)))))) var3))) var1 var5 var0 var4))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr)) (or (not (inv_main85 var2 var1 var7 var0 var8 var3 var9 var4 var5 var6)) (inv_main84 (write var2 var5 (O_sl_item (sl_item (n1 (getsl_item (read var2 var5))) var6))) var1 var7 var0 var8 var3 var9 var4 var5))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Int) (var17 Addr) (var18 Addr)) (or (not (and (inv_main78 var4 var2 var7 var0 var8 var12 var9 var5 var13) (and (not (= var16 0)) (and (and (and (and (and (and (and (and (= var3 (write var4 var9 (O_sl_item (sl_item var13 (n2 (getsl_item (read var4 var9))))))) (= var17 var2)) (= var15 var7)) (= var1 var0)) (= var10 var8)) (= var6 var12)) (= var18 var9)) (= var14 var5)) (= var11 var13))))) (inv_main81 var3 var17 var15 var1 var10 var6 var18 var14 var11))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Int) (var6 Heap) (var7 Addr) (var8 Addr)) (or (not (and (inv_main30 var6 var3 var8 var1) (and (not (= var5 1)) (and (and (and (and (= var4 var6) (= var7 var3)) (= var2 var8)) (= var0 var1)) (= var5 (h (getnode (read var6 var1)))))))) (inv_main32 var4 var7 var2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Heap) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr)) (or (not (and (inv_main58 var5 var4 var8 var0 var9 var14 var11 var7 var16) (and (and (and (and (and (and (and (and (and (= var13 var5) (= var12 var4)) (= var2 var8)) (= var3 var0)) (= var18 var9)) (= var15 var14)) (= var17 var11)) (= var1 var7)) (= var6 var16)) (= var10 (head (getsl (read var5 var14))))))) (inv_main59 var13 var12 var2 var3 var18 var15 var17 var10 var6))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Heap) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr)) (or (not (and (inv_main62 var4 var3 var7 var2 var8 var15 var9 var6 var18) (and (and (and (and (and (and (and (and (and (= var11 var4) (= var10 var3)) (= var0 var7)) (= var1 var2)) (= var5 var8)) (= var14 var15)) (= var12 var9)) (= var13 var6)) (= var17 var18)) (= var16 (n2 (getsl_item (read var4 var6))))))) (inv_main59 var11 var10 var0 var1 var5 var14 var12 var16 var17))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr)) (or (not (inv_main18 var2 var1 var3 var0)) (inv_main24 (write var2 var0 (O_node (node (h (getnode (read var2 var0))) var3))) var1 var3 var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Int) (var6 Int) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Addr)) (or (not (and (inv_main63 var7 var4 var13 var2 var14 var17 var15 var8 var18 var1) (and (not (= var5 0)) (and (not (= var6 0)) (and (and (and (and (and (and (and (and (and (= var0 var7) (= var19 var4)) (= var12 var13)) (= var9 var2)) (= var20 var14)) (= var11 var17)) (= var16 var15)) (= var10 var8)) (= var3 var18)) (or (and (not (= var1 (tail (getsl (read var7 var17))))) (= var6 1)) (and (= var1 (tail (getsl (read var7 var17)))) (= var6 0)))))))) (inv_main62 var0 var19 var12 var9 var20 var11 var16 var10 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr)) (or (not (inv_main76 var2 var1 var6 var0 var7 var3 var8 var4 var5)) (inv_main79 var2 var1 var6 var0 var7 var3 var8 var4 var5 (n1 (getsl_item (read var2 var8)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr)) (or (not (and (inv_main90 var3 var2 var5 var0 var6 var4 var1) (not (= (head (getsl (read var3 var4))) nullAddr)))) (inv_main92 var3 var2 var5 var0 var6 var4 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Heap)) (or (not (and (inv_main70 var5 var3 var10 var0 var11 var15 var12 var7 var16) (and (and (and (and (and (and (and (and (and (= var18 var5) (= var13 var3)) (= var6 var10)) (= var9 var0)) (= var1 var11)) (= var17 var15)) (= var14 var12)) (= var4 var7)) (= var8 var16)) (= var2 (n1 (getsl_item (read var5 var12))))))) (inv_main68 var18 var13 var6 var9 var1 var17 var2 var4 var8))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Int) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Heap)) (or (not (and (inv_main63 var6 var5 var9 var2 var10 var16 var11 var7 var18 var1) (and (= var13 0) (and (and (and (and (and (and (and (and (and (= var19 var6) (= var14 var5)) (= var17 var9)) (= var12 var2)) (= var0 var10)) (= var15 var16)) (= var8 var11)) (= var4 var7)) (= var3 var18)) (or (and (not (= var1 (tail (getsl (read var6 var16))))) (= var13 1)) (and (= var1 (tail (getsl (read var6 var16)))) (= var13 0))))))) (inv_main68 var19 var14 var17 var12 var0 var15 var4 var4 var3))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Int) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Int) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Addr)) (or (not (and (inv_main63 var6 var4 var13 var2 var14 var17 var15 var7 var18 var1) (and (= var12 0) (and (not (= var5 0)) (and (and (and (and (and (and (and (and (and (= var0 var6) (= var19 var4)) (= var11 var13)) (= var8 var2)) (= var20 var14)) (= var10 var17)) (= var16 var15)) (= var9 var7)) (= var3 var18)) (or (and (not (= var1 (tail (getsl (read var6 var17))))) (= var5 1)) (and (= var1 (tail (getsl (read var6 var17)))) (= var5 0)))))))) (inv_main68 var0 var19 var11 var8 var20 var10 var9 var9 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Heap) (var6 Addr) (var7 Addr) (var8 sl_item) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Int) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Heap) (var23 Addr) (var24 Addr) (var25 Addr) (var26 Addr) (var27 Addr) (var28 Addr) (var29 Addr) (var30 Addr)) (or (not (and (inv_main71 var5 var20 var24 var17 var9 var15 var11 var21 var26 var25) (and (and (and (and (and (and (and (and (and (and (= var22 (newHeap (alloc var4 (O_sl_item var8)))) (= var10 var3)) (= var19 var16)) (= var0 var13)) (= var28 var30)) (= var14 var29)) (= var23 var6)) (= var12 var2)) (= var7 var27)) (= var1 (newAddr (alloc var4 (O_sl_item var8))))) (and (= var18 0) (and (and (and (and (and (and (and (and (and (= var4 var5) (= var3 var20)) (= var16 var24)) (= var13 var17)) (= var30 var9)) (= var29 var15)) (= var6 var11)) (= var2 var21)) (= var27 var26)) (or (and (not (= var25 (n2 (getsl_item (read var5 var21))))) (= var18 1)) (and (= var25 (n2 (getsl_item (read var5 var21)))) (= var18 0)))))))) (inv_main76 var22 var10 var19 var0 var28 var14 var23 var12 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Heap) (var5 sl_item) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Int) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Heap) (var22 Addr) (var23 Int) (var24 Addr) (var25 Addr) (var26 Addr) (var27 Addr) (var28 Addr) (var29 Addr) (var30 Addr) (var31 Addr)) (or (not (and (inv_main71 var4 var17 var22 var15 var9 var12 var11 var18 var28 var26) (and (and (and (and (and (and (and (and (and (and (= var2 (newHeap (alloc var21 (O_sl_item var5)))) (= var7 var6)) (= var14 var8)) (= var10 var30)) (= var20 var27)) (= var19 var25)) (= var31 var29)) (= var1 var0)) (= var3 var16)) (= var24 (newAddr (alloc var21 (O_sl_item var5))))) (and (= var23 0) (and (not (= var13 0)) (and (and (and (and (and (and (and (and (and (= var21 var4) (= var6 var17)) (= var8 var22)) (= var30 var15)) (= var27 var9)) (= var25 var12)) (= var29 var11)) (= var0 var18)) (= var16 var28)) (or (and (not (= var26 (n2 (getsl_item (read var4 var18))))) (= var13 1)) (and (= var26 (n2 (getsl_item (read var4 var18)))) (= var13 0))))))))) (inv_main76 var2 var7 var14 var10 var20 var19 var31 var1 var24))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr)) (or (not (and (inv_main31 var3 var1 var8 var0) (and (not (= var7 nullAddr)) (and (and (and (and (= var2 var3) (= var4 var1)) (= var6 var8)) (= var5 var0)) (= var7 (n (getnode (read var3 var0)))))))) (inv_main30 var2 var4 var6 var7))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr)) (or (not (and (inv_main26 var5 var2 var7 var1) (and (not (= var3 nullAddr)) (and (and (and (= var0 (write var5 var1 (O_node (node (h (getnode (read var5 var1))) 0)))) (= var3 var2)) (= var4 var7)) (= var6 var1))))) (inv_main30 var0 var3 var4 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr)) (or (not (inv_main46 var2 var1 var4 var0 var3 var5)) (inv_main47 (write var2 (head (getsl (read var2 var3))) (O_sl_item (sl_item var5 (n2 (getsl_item (read var2 (head (getsl (read var2 var3))))))))) var1 var4 var0 var3 var5))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap)) (or (not (inv_main7 var2 var1 var0)) (inv_main7 var2 var1 var0))))
(assert (forall ((var0 node) (var1 Heap) (var2 Addr) (var3 Heap)) (or (not (and (inv_main2 var1) (and (= var2 nullAddr) (and (= var3 (newHeap (alloc var1 (O_node var0)))) (= var2 (newAddr (alloc var1 (O_node var0)))))))) (inv_main7 var3 var2 1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr)) (or (not (and (inv_main49 var6 var4 var9 var0 var7 var3) (and (and (and (and (= var2 (write var6 (tail (getsl (read var6 var7))) (O_sl_item (sl_item (n1 (getsl_item (read var6 (tail (getsl (read var6 var7)))))) var3)))) (= var1 var4)) (= var8 var9)) (= var10 var0)) (= var5 var7)))) (inv_main50 var2 var1 var8 var10 var5))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Heap)) (or (not (and (inv_main84 var2 var1 var5 var0 var6 var10 var8 var3 var13) (and (and (and (and (and (= var14 (write var2 var3 (O_sl_item (sl_item (n1 (getsl_item (read var2 var3))) var13)))) (= var7 var1)) (= var4 var5)) (= var12 var0)) (= var9 var6)) (= var11 var10)))) (inv_main50 var14 var7 var4 var12 var9))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Heap) (var5 Addr) (var6 Int) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr)) (or (not (and (inv_main78 var4 var2 var8 var0 var9 var13 var10 var5 var14) (and (= var6 0) (and (and (and (and (and (and (and (and (= var3 (write var4 var10 (O_sl_item (sl_item var14 (n2 (getsl_item (read var4 var10))))))) (= var17 var2)) (= var16 var8)) (= var1 var0)) (= var11 var9)) (= var7 var13)) (= var18 var10)) (= var15 var5)) (= var12 var14))))) (inv_main50 var3 var17 var16 var1 var11))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Int) (var17 Addr) (var18 Int) (var19 Addr) (var20 Addr)) (or (not (and (inv_main71 var4 var3 var9 var1 var10 var15 var11 var5 var17 var13) (and (not (= var18 0)) (and (not (= var16 0)) (and (and (and (and (and (and (and (and (and (= var8 var4) (= var6 var3)) (= var7 var9)) (= var20 var1)) (= var14 var10)) (= var12 var15)) (= var19 var11)) (= var0 var5)) (= var2 var17)) (or (and (not (= var13 (n2 (getsl_item (read var4 var5))))) (= var16 1)) (and (= var13 (n2 (getsl_item (read var4 var5)))) (= var16 0)))))))) (inv_main70 var8 var6 var7 var20 var14 var12 var19 var0 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main24 var6 var4 var8 var0) (and (not (= var3 0)) (and (and (and (and (= var9 var6) (= var5 var4)) (= var1 var8)) (= var7 var0)) (= var2 (n (getnode (read var6 var0)))))))) (inv_main13 var9 var5 var1 var2))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 node) (var3 Int) (var4 Heap) (var5 Addr)) (or (not (and (inv_main2 var4) (and (not (= var3 0)) (and (not (= var5 nullAddr)) (and (= var1 (newHeap (alloc var4 (O_node var2)))) (= var5 (newAddr (alloc var4 (O_node var2))))))))) (inv_main13 var1 var5 var0 var5))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr)) (or (not (inv_main93 var3 var2 var5 var0 var6 var4 var1)) (inv_main96 var3 var2 var5 var0 var6 var4 var1 (n1 (getsl_item (read var3 (head (getsl (read var3 var4))))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr)) (not (and (inv_main13 var2 var1 var3 var0) (not (is-O_node (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr)) (not (and (inv_main18 var2 var1 var3 var0) (not (is-O_node (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr)) (not (and (inv_main24 var2 var1 var3 var0) (not (is-O_node (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr)) (not (and (inv_main12 var2 var1 var3 var0) (not (is-O_node (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr)) (not (and (inv_main26 var2 var1 var3 var0) (not (is-O_node (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr)) (not (and (inv_main30 var2 var1 var3 var0) (not (is-O_node (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr)) (not (inv_main32 var2 var1 var3 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr)) (not (and (inv_main31 var2 var1 var3 var0) (not (is-O_node (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr)) (not (and (inv_main42 var2 var1 var5 var0 var3 var4) (not (is-O_sl (read var2 var3)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr)) (not (and (inv_main44 var3 var1 var5 var0 var4 var2) (not (is-O_sl (read var3 var4)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr)) (not (and (inv_main43 var2 var1 var4 var0 var3) (not (is-O_sl (read var2 var3)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr)) (not (and (inv_main46 var2 var1 var4 var0 var3 var5) (not (is-O_sl (read var2 var3)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr)) (not (and (inv_main46 var2 var1 var4 var0 var3 var5) (not (is-O_sl_item (read var2 (head (getsl (read var2 var3))))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr)) (not (and (inv_main47 var2 var1 var5 var0 var4 var3) (not (is-O_sl (read var2 var4)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr)) (not (and (inv_main47 var2 var1 var5 var0 var4 var3) (not (is-O_sl_item (read var2 (head (getsl (read var2 var4))))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr)) (not (and (inv_main45 var2 var1 var4 var0 var3) (not (is-O_sl (read var2 var3)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr)) (not (and (inv_main45 var2 var1 var4 var0 var3) (not (is-O_sl_item (read var2 (tail (getsl (read var2 var3))))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr)) (not (and (inv_main49 var3 var2 var5 var0 var4 var1) (not (is-O_sl (read var3 var4)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr)) (not (and (inv_main49 var3 var2 var5 var0 var4 var1) (not (is-O_sl_item (read var3 (tail (getsl (read var3 var4))))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr)) (not (and (inv_main58 var2 var1 var6 var0 var7 var3 var8 var4 var5) (not (is-O_sl (read var2 var3)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr)) (not (and (inv_main59 var2 var1 var6 var0 var7 var3 var8 var4 var5) (not (is-O_sl_item (read var2 var4)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr)) (not (and (inv_main63 var3 var2 var7 var1 var8 var4 var9 var5 var6 var0) (not (is-O_sl (read var3 var4)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr)) (not (and (inv_main62 var2 var1 var6 var0 var7 var3 var8 var4 var5) (not (is-O_sl_item (read var2 var4)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr)) (not (and (inv_main68 var2 var1 var6 var0 var7 var3 var8 var4 var5) (not (is-O_sl_item (read var2 var8)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr)) (not (and (inv_main71 var3 var2 var7 var0 var8 var4 var9 var5 var6 var1) (not (is-O_sl_item (read var3 var5)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr)) (not (and (inv_main70 var2 var1 var6 var0 var7 var3 var8 var4 var5) (not (is-O_sl_item (read var2 var8)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr)) (not (and (inv_main76 var2 var1 var6 var0 var7 var3 var8 var4 var5) (not (is-O_sl_item (read var2 var8)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr)) (not (and (inv_main79 var3 var1 var7 var0 var8 var4 var9 var5 var6 var2) (not (is-O_sl_item (read var3 var6)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr)) (not (and (inv_main78 var2 var1 var6 var0 var7 var3 var8 var4 var5) (not (is-O_sl_item (read var2 var8)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr)) (not (and (inv_main81 var2 var1 var6 var0 var7 var3 var8 var4 var5) (not (is-O_sl_item (read var2 var4)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr)) (not (and (inv_main85 var2 var1 var7 var0 var8 var3 var9 var4 var5 var6) (not (is-O_sl_item (read var2 var5)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr)) (not (and (inv_main84 var2 var1 var6 var0 var7 var3 var8 var4 var5) (not (is-O_sl_item (read var2 var4)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr)) (not (and (inv_main90 var3 var2 var5 var0 var6 var4 var1) (not (is-O_sl (read var3 var4)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr)) (not (and (inv_main92 var3 var2 var5 var0 var6 var4 var1) (not (is-O_sl (read var3 var4)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr)) (not (and (inv_main93 var3 var2 var5 var0 var6 var4 var1) (not (is-O_sl (read var3 var4)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr)) (not (and (inv_main93 var3 var2 var5 var0 var6 var4 var1) (not (is-O_sl_item (read var3 (head (getsl (read var3 var4))))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr)) (not (and (inv_main96 var3 var2 var6 var0 var7 var5 var1 var4) (not (is-O_sl (read var3 var5)))))))
(check-sat)
