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
                   ((node (next Addr) (data Int)))))
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
(declare-fun inv_main12 (Heap Int Int Int Int Int Addr) Bool)
(declare-fun inv_main15 (Heap Int Int Int Int Int Addr Int) Bool)
(declare-fun inv_main18 (Heap Int Int Int Int Int Addr) Bool)
(declare-fun inv_main21 (Heap Int Int Int Int Addr Addr) Bool)
(declare-fun inv_main22 (Heap Int Int Int Int Addr Addr) Bool)
(declare-fun inv_main28 (Heap Int Int Int Int Addr Addr Int Addr) Bool)
(declare-fun inv_main31 (Heap Int Int Int Int Addr Addr Int Addr Int) Bool)
(declare-fun inv_main34 (Heap Int Int Int Int Addr Addr Int Addr) Bool)
(declare-fun inv_main36 (Heap Int Int Int Int Addr Addr Addr) Bool)
(declare-fun inv_main4 (Heap Int Int) Bool)
(declare-fun inv_main43 (Heap Int Int Addr Int) Bool)
(declare-fun inv_main50 (Heap Int Int Addr Int Int Addr Int Int) Bool)
(declare-fun inv_main51 (Heap Int Int Addr Int Int Addr Int Int) Bool)
(declare-fun inv_main55 (Heap Int Int Addr Int) Bool)
(declare-fun inv_main64 (Heap Int Int Addr Int Int Addr Int) Bool)
(declare-fun inv_main65 (Heap Int Int Addr Int Int Addr Int) Bool)
(declare-fun inv_main72 (Heap Int Int Addr Int Addr) Bool)
(declare-fun inv_main76 (Heap Int Int Addr Int Addr Addr) Bool)
(declare-fun inv_main79 (Heap Int Int Addr Int) Bool)
(assert (forall ((var0 Heap)) (or (not (= var0 emptyHeap)) (inv_main4 var0 2 1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Heap)) (or (not (and (inv_main43 var4 var3 var0 var1 var2) (not (<= 0 (+ (+ var2 1) (- 1)))))) (inv_main55 var4 var3 var0 var1 (+ var3 (- 1))))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Int) (var4 Addr) (var5 Heap) (var6 Int) (var7 Int) (var8 Addr) (var9 Int) (var10 Int) (var11 Int) (var12 Heap) (var13 Int) (var14 Int)) (or (not (and (inv_main64 var5 var11 var7 var8 var0 var1 var2 var13) (and (= var10 var6) (and (and (and (and (and (and (= var12 var5) (= var9 var11)) (= var14 var7)) (= var4 var8)) (= var3 var0)) (= var10 var1)) (= var6 (data (getnode (read var5 var2)))))))) (inv_main55 var12 var9 var14 var4 (+ var3 (- 1))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Int) (var4 Int) (var5 Addr) (var6 Int) (var7 Heap) (var8 Addr)) (or (not (inv_main28 var7 var4 var1 var3 var6 var0 var8 var2 var5)) (inv_main34 (write var7 var5 (O_node (node nullAddr (data (getnode (read var7 var5)))))) var4 var1 var3 var6 var0 var8 var2 var5))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Heap) (var9 Int) (var10 Int) (var11 Int) (var12 Addr) (var13 Int) (var14 Int) (var15 Int) (var16 Int) (var17 Int) (var18 Int)) (or (not (and (inv_main51 var5 var14 var10 var12 var2 var18 var0 var13 var15) (and (not (<= 0 (+ (+ var16 (- 1)) (- 1)))) (and (and (and (and (and (and (and (and (and (= var8 var5) (= var3 var14)) (= var9 var10)) (= var1 var12)) (= var11 var2)) (= var4 var18)) (= var7 var0)) (= var17 var13)) (= var16 var15)) (= var6 (next (getnode (read var5 var0)))))))) (inv_main50 var8 var3 var9 var1 var11 var4 var6 var17 (+ var16 (- 1))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Heap)) (or (not (and (inv_main43 var4 var3 var0 var1 var2) (and (not (<= 0 (+ var2 (- 1)))) (<= 0 (+ (+ var2 1) (- 1)))))) (inv_main50 var4 var3 var0 var1 var2 (+ var2 var3) var1 (+ var2 var3) var2))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Heap)) (or (not (inv_main15 var7 var4 var1 var3 var6 var0 var2 var5)) (inv_main15 var7 var4 var1 var3 var6 var0 var2 var5))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Int) (var4 node) (var5 Int) (var6 Int) (var7 Heap) (var8 Addr) (var9 Heap) (var10 Int)) (or (not (and (inv_main4 var9 var5 var1) (and (= nullAddr var8) (and (and (and (and (and (and (= var7 (newHeap (alloc var9 (O_node var4)))) (= var0 var5)) (= var6 var1)) (= var2 var5)) (= var3 var1)) (= var10 var1)) (= var8 (newAddr (alloc var9 (O_node var4)))))))) (inv_main15 var7 var0 var6 var2 var3 var10 var8 1))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Int) (var4 Int) (var5 Addr) (var6 Int) (var7 Int) (var8 Heap) (var9 Addr)) (or (not (inv_main31 var8 var4 var1 var3 var7 var0 var9 var2 var5 var6)) (inv_main31 var8 var4 var1 var3 var7 var0 var9 var2 var5 var6))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Heap) (var6 Heap) (var7 Addr) (var8 Int) (var9 Int) (var10 node) (var11 Int) (var12 Int) (var13 Addr) (var14 Addr) (var15 Int) (var16 Addr)) (or (not (and (inv_main21 var5 var12 var9 var11 var15 var1 var16) (and (and (= nullAddr var14) (and (and (and (and (and (and (and (and (= var6 (newHeap (alloc var5 (O_node var10)))) (= var4 var12)) (= var2 var9)) (= var0 var11)) (= var8 var15)) (= var13 var1)) (= var7 var16)) (= var3 var15)) (= var14 (newAddr (alloc var5 (O_node var10)))))) (<= 0 (+ (+ var11 (- 1)) (- 1)))))) (inv_main31 var6 var4 var2 var0 var8 var13 var7 var3 var14 1))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Heap)) (or (not (inv_main12 var6 var4 var1 var3 var5 var0 var2)) (inv_main18 (write var6 var2 (O_node (node nullAddr (data (getnode (read var6 var2)))))) var4 var1 var3 var5 var0 var2))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Heap) (var6 Int) (var7 Int) (var8 Int) (var9 Int) (var10 Addr) (var11 Int) (var12 Int) (var13 Int) (var14 Int) (var15 Heap) (var16 Addr) (var17 Int)) (or (not (and (inv_main50 var5 var12 var8 var10 var3 var17 var1 var11 var14) (and (and (and (and (and (and (and (and (= var15 (write var5 var1 (O_node (node (next (getnode (read var5 var1))) var11)))) (= var13 var12)) (= var0 var8)) (= var16 var10)) (= var7 var3)) (= var4 var17)) (= var2 var1)) (= var6 var11)) (= var9 var14)))) (inv_main43 var15 var13 var0 var16 (+ var7 (- 1))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Int) (var3 Addr) (var4 Int) (var5 Heap) (var6 Int) (var7 Int) (var8 Int) (var9 Int) (var10 Int) (var11 Addr) (var12 Int) (var13 Addr)) (or (not (and (inv_main22 var5 var9 var7 var8 var10 var1 var13) (and (and (and (and (and (and (= var0 (write var5 var13 (O_node (node var1 (data (getnode (read var5 var13))))))) (= var2 var9)) (= var4 var7)) (= var12 var8)) (= var6 var10)) (= var3 var1)) (= var11 var13)))) (inv_main43 var0 var2 var4 var3 (+ var2 (- 1))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Int) (var6 Addr) (var7 Int) (var8 Int) (var9 Heap) (var10 Int) (var11 Heap) (var12 Addr)) (or (not (and (inv_main72 var9 var8 var2 var4 var7 var1) (and (not (= var12 var3)) (and (and (and (and (and (and (= var11 var9) (= var10 var8)) (= var5 var2)) (= var6 var4)) (= var0 var7)) (= var3 var1)) (= var12 (next (getnode (read var9 var1)))))))) (inv_main76 var11 var10 var5 var6 var0 var3 var12))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Int) (var3 Heap) (var4 Int) (var5 Int) (var6 Int) (var7 Int) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Int) (var13 Int) (var14 Addr) (var15 Addr) (var16 Int) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Int)) (or (not (and (inv_main76 var8 var16 var12 var14 var6 var1 var15) (and (not (= var18 var17)) (and (and (and (and (and (and (and (and (= var0 var8) (= var4 var16)) (= var7 var12)) (= var9 var14)) (= var13 var6)) (= var20 var1)) (= var21 var15)) (= var10 (next (getnode (read var8 var15))))) (and (and (and (and (and (and (and (= var3 (write var0 var21 defObj)) (= var2 var4)) (= var22 var7)) (= var19 var9)) (= var5 var13)) (= var17 var20)) (= var11 var21)) (= var18 var10)))))) (inv_main76 var3 var2 var22 var19 var5 var17 var18))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Addr) (var4 Heap) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Int) (var9 Addr) (var10 Int) (var11 Int) (var12 Int) (var13 Int) (var14 Addr) (var15 Int)) (or (not (and (inv_main36 var5 var11 var8 var10 var13 var0 var14 var9) (and (and (and (and (and (and (and (= var4 (write var5 var9 (O_node (node var0 (data (getnode (read var5 var9))))))) (= var1 var11)) (= var12 var8)) (= var2 var10)) (= var15 var13)) (= var6 var0)) (= var3 var14)) (= var7 var9)))) (inv_main21 var4 var1 var12 (+ var2 (- 1)) var15 var7 var3))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Int) (var4 Heap) (var5 Int) (var6 Int) (var7 Int) (var8 Int) (var9 Int) (var10 Int) (var11 Heap) (var12 Int) (var13 Int)) (or (not (and (inv_main18 var4 var10 var6 var8 var12 var1 var2) (and (and (and (and (and (and (= var11 (write var4 var2 (O_node (node (next (getnode (read var4 var2))) var1)))) (= var5 var10)) (= var13 var6)) (= var3 var8)) (= var9 var12)) (= var7 var1)) (= var0 var2)))) (inv_main21 var11 var5 var13 var3 var9 var0 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Int) (var4 Int) (var5 Addr) (var6 Heap) (var7 Heap) (var8 Addr) (var9 Int) (var10 Addr) (var11 Int) (var12 Int) (var13 Addr) (var14 Int) (var15 Int) (var16 Addr)) (or (not (and (inv_main65 var6 var12 var9 var10 var2 var4 var5 var15) (and (<= 0 (+ (+ var0 (- 1)) (- 1))) (and (and (and (and (and (and (and (and (= var7 var6) (= var1 var12)) (= var3 var9)) (= var16 var10)) (= var11 var2)) (= var14 var4)) (= var13 var5)) (= var0 var15)) (= var8 (next (getnode (read var6 var5)))))))) (inv_main65 var7 var1 var3 var16 var11 var14 var8 (+ var0 (- 1))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Heap)) (or (not (and (inv_main55 var4 var3 var0 var1 var2) (and (<= 0 (+ var2 (- 1))) (<= 0 (+ (+ var2 1) (- 1)))))) (inv_main65 var4 var3 var0 var1 var2 (+ var2 var3) var1 var2))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Int) (var4 Int) (var5 Heap) (var6 Addr) (var7 Heap) (var8 Int) (var9 node) (var10 Int)) (or (not (and (inv_main4 var7 var3 var1) (and (not (= nullAddr var6)) (and (and (and (and (and (and (= var5 (newHeap (alloc var7 (O_node var9)))) (= var8 var3)) (= var2 var1)) (= var4 var3)) (= var10 var1)) (= var0 var1)) (= var6 (newAddr (alloc var7 (O_node var9)))))))) (inv_main12 var5 var8 var2 var4 var10 var0 var6))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Heap) (var9 Int) (var10 Int) (var11 Int) (var12 Addr) (var13 Int) (var14 Int) (var15 Int) (var16 Int) (var17 Int) (var18 Int)) (or (not (and (inv_main51 var5 var14 var10 var12 var2 var18 var0 var13 var15) (and (<= 0 (+ (+ var16 (- 1)) (- 1))) (and (and (and (and (and (and (and (and (and (= var8 var5) (= var3 var14)) (= var9 var10)) (= var1 var12)) (= var11 var2)) (= var4 var18)) (= var7 var0)) (= var17 var13)) (= var16 var15)) (= var6 (next (getnode (read var5 var0)))))))) (inv_main51 var8 var3 var9 var1 var11 var4 var6 var17 (+ var16 (- 1))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Heap)) (or (not (and (inv_main43 var4 var3 var0 var1 var2) (and (<= 0 (+ var2 (- 1))) (<= 0 (+ (+ var2 1) (- 1)))))) (inv_main51 var4 var3 var0 var1 var2 (+ var2 var3) var1 (+ var2 var3) var2))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Int) (var4 Int) (var5 Addr) (var6 Heap) (var7 Heap) (var8 Addr) (var9 Int) (var10 Addr) (var11 Int) (var12 Int) (var13 Addr) (var14 Int) (var15 Int) (var16 Addr)) (or (not (and (inv_main65 var6 var12 var9 var10 var2 var4 var5 var15) (and (not (<= 0 (+ (+ var0 (- 1)) (- 1)))) (and (and (and (and (and (and (and (and (= var7 var6) (= var1 var12)) (= var3 var9)) (= var16 var10)) (= var11 var2)) (= var14 var4)) (= var13 var5)) (= var0 var15)) (= var8 (next (getnode (read var6 var5)))))))) (inv_main64 var7 var1 var3 var16 var11 var14 var8 (+ var0 (- 1))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Heap)) (or (not (and (inv_main55 var4 var3 var0 var1 var2) (and (not (<= 0 (+ var2 (- 1)))) (<= 0 (+ (+ var2 1) (- 1)))))) (inv_main64 var4 var3 var0 var1 var2 (+ var2 var3) var1 var2))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Int) (var4 Addr) (var5 Heap) (var6 Int) (var7 Int) (var8 Int) (var9 Addr) (var10 Int) (var11 Int) (var12 Int) (var13 Int) (var14 Int)) (or (not (and (inv_main64 var5 var10 var8 var9 var2 var3 var4 var11) (and (not (= var6 var14)) (and (and (and (and (and (and (= var1 var5) (= var13 var10)) (= var12 var8)) (= var0 var9)) (= var7 var2)) (= var6 var3)) (= var14 (data (getnode (read var5 var4)))))))) (inv_main79 var1 var13 var12 var0 var7))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Int) (var7 Heap) (var8 node) (var9 Int) (var10 Int) (var11 Int) (var12 Int) (var13 Int) (var14 Int) (var15 Int) (var16 Addr)) (or (not (and (inv_main21 var7 var13 var11 var12 var15 var2 var16) (and (and (not (= nullAddr var0)) (and (and (and (and (and (and (and (and (= var3 (newHeap (alloc var7 (O_node var8)))) (= var9 var13)) (= var14 var11)) (= var6 var12)) (= var1 var15)) (= var4 var2)) (= var5 var16)) (= var10 var15)) (= var0 (newAddr (alloc var7 (O_node var8)))))) (<= 0 (+ (+ var12 (- 1)) (- 1)))))) (inv_main28 var3 var9 var14 var6 var1 var4 var5 var10 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Int) (var4 Int) (var5 Heap) (var6 Addr)) (or (not (and (inv_main21 var5 var3 var1 var2 var4 var0 var6) (not (<= 0 (+ (+ var2 (- 1)) (- 1)))))) (inv_main22 var5 var3 var1 var2 var4 var0 var6))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Heap)) (or (not (and (inv_main55 var4 var3 var0 var1 var2) (and (not (= nullAddr var1)) (not (<= 0 (+ (+ var2 1) (- 1))))))) (inv_main72 var4 var3 var0 var1 var2 var1))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Int) (var4 Heap) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Int) (var9 Int) (var10 Int) (var11 Int) (var12 Int) (var13 Int) (var14 Addr) (var15 Int) (var16 Addr) (var17 Addr)) (or (not (and (inv_main34 var4 var11 var8 var10 var15 var0 var17 var9 var14) (and (and (and (and (and (and (and (and (= var5 (write var4 var14 (O_node (node (next (getnode (read var4 var14))) var9)))) (= var13 var11)) (= var3 var8)) (= var12 var10)) (= var2 var15)) (= var16 var0)) (= var7 var17)) (= var1 var9)) (= var6 var14)))) (inv_main36 var5 var13 var3 var12 var2 var16 var7 var6))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Heap)) (not (and (inv_main12 var6 var4 var1 var3 var5 var0 var2) (not (is-O_node (read var6 var2)))))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Heap)) (not (and (inv_main18 var6 var4 var1 var3 var5 var0 var2) (not (is-O_node (read var6 var2)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Int) (var4 Int) (var5 Addr) (var6 Int) (var7 Heap) (var8 Addr)) (not (and (inv_main28 var7 var4 var1 var3 var6 var0 var8 var2 var5) (not (is-O_node (read var7 var5)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Int) (var4 Int) (var5 Addr) (var6 Int) (var7 Heap) (var8 Addr)) (not (and (inv_main34 var7 var4 var1 var3 var6 var0 var8 var2 var5) (not (is-O_node (read var7 var5)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Heap) (var7 Addr)) (not (and (inv_main36 var6 var4 var1 var3 var5 var0 var7 var2) (not (is-O_node (read var6 var2)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Int) (var4 Int) (var5 Heap) (var6 Addr)) (not (and (inv_main22 var5 var3 var1 var2 var4 var0 var6) (not (is-O_node (read var5 var6)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Heap) (var8 Int)) (not (and (inv_main51 var7 var5 var1 var2 var4 var8 var0 var3 var6) (not (is-O_node (read var7 var0)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Heap) (var8 Int)) (not (and (inv_main50 var7 var5 var1 var2 var4 var8 var0 var3 var6) (not (is-O_node (read var7 var0)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Addr) (var6 Int) (var7 Heap)) (not (and (inv_main65 var7 var3 var0 var1 var2 var4 var5 var6) (not (is-O_node (read var7 var5)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Addr) (var6 Int) (var7 Heap)) (not (and (inv_main64 var7 var3 var0 var1 var2 var4 var5 var6) (not (is-O_node (read var7 var5)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Int) (var4 Int) (var5 Heap)) (not (and (inv_main72 var5 var4 var1 var2 var3 var0) (not (is-O_node (read var5 var0)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Int) (var5 Int) (var6 Heap)) (not (and (inv_main76 var6 var5 var1 var2 var4 var0 var3) (not (is-O_node (read var6 var3)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Heap)) (not (inv_main79 var4 var3 var0 var1 var2))))
(check-sat)
