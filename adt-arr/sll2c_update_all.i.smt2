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
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Heap) (var4 Int) (var5 Int) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Int) (var13 Heap) (var14 Int) (var15 Int) (var16 Int) (var17 Int)) (or (not (and (inv_main34 var3 var4 var16 var0 var15 var9 var8 var12 var7) (and (and (and (and (and (and (and (and (= var13 (write var3 var7 (O_node (node (next (getnode (read var3 var7))) var12)))) (= var5 var4)) (= var2 var16)) (= var17 var0)) (= var1 var15)) (= var6 var9)) (= var11 var8)) (= var14 var12)) (= var10 var7)))) (inv_main36 var13 var5 var2 var17 var1 var6 var11 var10))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Heap) (var4 Int) (var5 Addr) (var6 Int) (var7 Int) (var8 Int) (var9 Int) (var10 Heap) (var11 Int) (var12 Addr) (var13 Int) (var14 Int) (var15 Addr) (var16 Addr)) (or (not (and (inv_main65 var3 var4 var11 var12 var6 var13 var2 var8) (and (not (<= 0 (+ (+ var7 (- 1)) (- 1)))) (and (and (and (and (and (and (and (and (= var10 var3) (= var9 var4)) (= var1 var11)) (= var15 var12)) (= var14 var6)) (= var0 var13)) (= var5 var2)) (= var7 var8)) (= var16 (next (getnode (read var3 var2)))))))) (inv_main64 var10 var9 var1 var15 var14 var0 var16 (+ var7 (- 1))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Int) (var4 Int)) (or (not (and (inv_main55 var2 var3 var0 var1 var4) (and (not (<= 0 (+ var4 (- 1)))) (<= 0 (+ (+ var3 (* (- 1) var4)) (- 1)))))) (inv_main64 var2 var3 var0 var1 var4 (+ var4 var3) var1 var4))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr)) (or (not (and (inv_main21 var3 var4 var2 var0 var1 var6 var5) (not (<= 0 (+ (+ var0 (- 1)) (- 1)))))) (inv_main22 var3 var4 var2 var0 var1 var6 var5))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Int) (var7 Addr) (var8 Addr) (var9 Int) (var10 Heap) (var11 Int) (var12 Addr)) (or (not (and (inv_main72 var5 var6 var2 var4 var9 var8) (and (not (= var3 var7)) (and (and (and (and (and (and (= var10 var5) (= var1 var6)) (= var0 var2)) (= var12 var4)) (= var11 var9)) (= var7 var8)) (= var3 (next (getnode (read var5 var8)))))))) (inv_main76 var10 var1 var0 var12 var11 var7 var3))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Int) (var6 Addr) (var7 Int) (var8 Addr) (var9 Int) (var10 Addr) (var11 Int) (var12 Int) (var13 Addr) (var14 Addr) (var15 Heap) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Int) (var21 Int) (var22 Heap)) (or (not (and (inv_main76 var4 var5 var12 var14 var9 var17 var16) (and (not (= var2 var19)) (and (and (and (and (and (and (and (and (= var15 var4) (= var21 var5)) (= var20 var12)) (= var8 var14)) (= var1 var9)) (= var18 var17)) (= var13 var16)) (= var3 (next (getnode (read var4 var16))))) (and (and (and (and (and (and (and (= var22 (write var15 var13 defObj)) (= var11 var21)) (= var7 var20)) (= var10 var8)) (= var0 var1)) (= var19 var18)) (= var6 var13)) (= var2 var3)))))) (inv_main76 var22 var11 var7 var10 var0 var19 var2))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Int) (var3 Addr) (var4 Int) (var5 Int) (var6 Heap) (var7 Int) (var8 Int) (var9 Int) (var10 Addr) (var11 Int) (var12 Addr) (var13 Int) (var14 Int) (var15 Addr) (var16 Addr) (var17 Int) (var18 Int)) (or (not (and (inv_main51 var6 var7 var13 var15 var11 var17 var3 var2 var1) (and (not (<= 0 (+ (+ var14 (- 1)) (- 1)))) (and (and (and (and (and (and (and (and (and (= var0 var6) (= var5 var7)) (= var18 var13)) (= var12 var15)) (= var9 var11)) (= var8 var17)) (= var10 var3)) (= var4 var2)) (= var14 var1)) (= var16 (next (getnode (read var6 var3)))))))) (inv_main50 var0 var5 var18 var12 var9 var8 var16 var4 (+ var14 (- 1))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Int) (var4 Int)) (or (not (and (inv_main43 var2 var3 var0 var1 var4) (and (not (<= 0 (+ var4 (- 1)))) (<= 0 (+ (+ var3 (* (- 1) var4)) (- 1)))))) (inv_main50 var2 var3 var0 var1 var4 (+ var4 var3) var1 (+ var4 var3) var4))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Int) (var4 Int)) (or (not (and (inv_main55 var2 var3 var0 var1 var4) (and (not (= nullAddr var1)) (not (<= 0 (+ (+ var3 (* (- 1) var4)) (- 1))))))) (inv_main72 var2 var3 var0 var1 var4 var1))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Int) (var3 Addr) (var4 Int) (var5 Int) (var6 Heap) (var7 Int) (var8 Int) (var9 Int) (var10 Addr) (var11 Int) (var12 Addr) (var13 Int) (var14 Int) (var15 Addr) (var16 Addr) (var17 Int) (var18 Int)) (or (not (and (inv_main51 var6 var7 var13 var15 var11 var17 var3 var2 var1) (and (<= 0 (+ (+ var14 (- 1)) (- 1))) (and (and (and (and (and (and (and (and (and (= var0 var6) (= var5 var7)) (= var18 var13)) (= var12 var15)) (= var9 var11)) (= var8 var17)) (= var10 var3)) (= var4 var2)) (= var14 var1)) (= var16 (next (getnode (read var6 var3)))))))) (inv_main51 var0 var5 var18 var12 var9 var8 var16 var4 (+ var14 (- 1))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Int) (var4 Int)) (or (not (and (inv_main43 var2 var3 var0 var1 var4) (and (<= 0 (+ var4 (- 1))) (<= 0 (+ (+ var3 (* (- 1) var4)) (- 1)))))) (inv_main51 var2 var3 var0 var1 var4 (+ var4 var3) var1 (+ var4 var3) var4))))
(assert (forall ((var0 Int) (var1 Heap) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Heap) (var7 Int) (var8 Addr) (var9 Int) (var10 node)) (or (not (and (inv_main4 var6 var7 var2) (and (not (= nullAddr var8)) (and (and (and (and (and (and (= var1 (newHeap (alloc var6 (O_node var10)))) (= var0 var7)) (= var4 var2)) (= var9 var7)) (= var5 var2)) (= var3 var2)) (= var8 (newAddr (alloc var6 (O_node var10)))))))) (inv_main12 var1 var0 var4 var9 var5 var3 var8))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Heap) (var5 Int) (var6 Int) (var7 Int)) (or (not (inv_main15 var4 var5 var2 var0 var1 var6 var3 var7)) (inv_main15 var4 var5 var2 var0 var1 var6 var3 var7))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 node) (var7 Heap) (var8 Int) (var9 Addr) (var10 Heap)) (or (not (and (inv_main4 var7 var8 var2) (and (= nullAddr var9) (and (and (and (and (and (and (= var10 (newHeap (alloc var7 (O_node var6)))) (= var4 var8)) (= var3 var2)) (= var0 var8)) (= var5 var2)) (= var1 var2)) (= var9 (newAddr (alloc var7 (O_node var6)))))))) (inv_main15 var10 var4 var3 var0 var5 var1 var9 1))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Int) (var5 Heap) (var6 Int) (var7 Int) (var8 Int) (var9 Int) (var10 Addr) (var11 Heap) (var12 Int) (var13 Addr) (var14 Addr) (var15 Int) (var16 Int) (var17 Int)) (or (not (and (inv_main50 var5 var6 var12 var13 var8 var16 var3 var1 var0) (and (and (and (and (and (and (and (and (= var11 (write var5 var3 (O_node (node (next (getnode (read var5 var3))) var1)))) (= var4 var6)) (= var9 var12)) (= var10 var13)) (= var15 var8)) (= var7 var16)) (= var14 var3)) (= var2 var1)) (= var17 var0)))) (inv_main43 var11 var4 var9 var10 (+ var15 1)))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Heap) (var5 Int) (var6 Addr) (var7 Int) (var8 Addr) (var9 Addr) (var10 Int) (var11 Int) (var12 Int) (var13 Heap)) (or (not (and (inv_main22 var4 var5 var12 var1 var11 var8 var6) (and (and (and (and (and (and (= var13 (write var4 var6 (O_node (node var8 (data (getnode (read var4 var6))))))) (= var7 var5)) (= var10 var12)) (= var2 var1)) (= var0 var11)) (= var9 var8)) (= var3 var6)))) (inv_main43 var13 var7 var10 var9 0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Heap) (var5 Int) (var6 Addr) (var7 Int) (var8 Int) (var9 Int) (var10 Int) (var11 Int) (var12 Addr) (var13 Int) (var14 Heap)) (or (not (and (inv_main64 var4 var5 var11 var12 var7 var13 var3 var9) (and (not (= var1 var2)) (and (and (and (and (and (and (= var14 var4) (= var8 var5)) (= var0 var11)) (= var6 var12)) (= var10 var7)) (= var1 var13)) (= var2 (data (getnode (read var4 var3)))))))) (inv_main79 var14 var8 var0 var6 var10))))
(assert (forall ((var0 Int) (var1 Int) (var2 Heap) (var3 Heap) (var4 Int) (var5 Addr) (var6 Int) (var7 Int) (var8 Addr) (var9 Int) (var10 Addr) (var11 Int) (var12 Int) (var13 Int) (var14 node) (var15 Addr) (var16 Addr)) (or (not (and (inv_main21 var3 var4 var12 var1 var11 var8 var5) (and (and (not (= nullAddr var10)) (and (and (and (and (and (and (and (and (= var2 (newHeap (alloc var3 (O_node var14)))) (= var13 var4)) (= var7 var12)) (= var6 var1)) (= var0 var11)) (= var16 var8)) (= var15 var5)) (= var9 var11)) (= var10 (newAddr (alloc var3 (O_node var14)))))) (<= 0 (+ (+ var1 (- 1)) (- 1)))))) (inv_main28 var2 var13 var7 var6 var0 var16 var15 var9 var10))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Heap) (var4 Int) (var5 Addr) (var6 Int) (var7 Int) (var8 Int) (var9 Int) (var10 Heap) (var11 Int) (var12 Addr) (var13 Int) (var14 Int) (var15 Addr) (var16 Addr)) (or (not (and (inv_main65 var3 var4 var11 var12 var6 var13 var2 var8) (and (<= 0 (+ (+ var7 (- 1)) (- 1))) (and (and (and (and (and (and (and (and (= var10 var3) (= var9 var4)) (= var1 var11)) (= var15 var12)) (= var14 var6)) (= var0 var13)) (= var5 var2)) (= var7 var8)) (= var16 (next (getnode (read var3 var2)))))))) (inv_main65 var10 var9 var1 var15 var14 var0 var16 (+ var7 (- 1))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Int) (var4 Int)) (or (not (and (inv_main55 var2 var3 var0 var1 var4) (and (<= 0 (+ var4 (- 1))) (<= 0 (+ (+ var3 (* (- 1) var4)) (- 1)))))) (inv_main65 var2 var3 var0 var1 var4 (+ var4 var3) var1 var4))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Heap) (var5 Int) (var6 Int)) (or (not (inv_main12 var4 var5 var2 var0 var1 var6 var3)) (inv_main18 (write var4 var3 (O_node (node nullAddr (data (getnode (read var4 var3)))))) var5 var2 var0 var1 var6 var3))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Int) (var4 Int)) (or (not (and (inv_main43 var2 var3 var0 var1 var4) (not (<= 0 (+ (+ var3 (* (- 1) var4)) (- 1)))))) (inv_main55 var2 var3 var0 var1 0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Heap) (var3 Int) (var4 Int) (var5 Int) (var6 Heap) (var7 Addr) (var8 Int) (var9 Int) (var10 Addr) (var11 Int) (var12 Int) (var13 Int) (var14 Int)) (or (not (and (inv_main64 var2 var3 var9 var10 var5 var11 var0 var8) (and (= var1 var12) (and (and (and (and (and (and (= var6 var2) (= var4 var3)) (= var14 var9)) (= var7 var10)) (= var13 var5)) (= var1 var11)) (= var12 (data (getnode (read var2 var0)))))))) (inv_main55 var6 var4 var14 var7 (+ var13 1)))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Int) (var7 Addr) (var8 Addr) (var9 Int) (var10 Int) (var11 Int) (var12 Heap) (var13 Addr) (var14 Addr) (var15 Int)) (or (not (and (inv_main36 var5 var6 var11 var1 var10 var8 var7 var14) (and (and (and (and (and (and (and (= var12 (write var5 var14 (O_node (node var8 (data (getnode (read var5 var14))))))) (= var9 var6)) (= var15 var11)) (= var0 var1)) (= var2 var10)) (= var4 var8)) (= var3 var7)) (= var13 var14)))) (inv_main21 var12 var9 var15 (+ var0 (- 1)) var2 var13 var3))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Heap) (var5 Int) (var6 Int) (var7 Addr) (var8 Int) (var9 Int) (var10 Int) (var11 Heap) (var12 Int) (var13 Int)) (or (not (and (inv_main18 var4 var5 var10 var1 var9 var12 var3) (and (and (and (and (and (and (= var11 (write var4 var3 (O_node (node (next (getnode (read var4 var3))) var12)))) (= var0 var5)) (= var6 var10)) (= var8 var1)) (= var2 var9)) (= var13 var12)) (= var7 var3)))) (inv_main21 var11 var0 var6 var8 var2 var7 var7))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Int)) (or (not (inv_main28 var3 var4 var2 var0 var1 var7 var6 var8 var5)) (inv_main34 (write var3 var5 (O_node (node nullAddr (data (getnode (read var3 var5)))))) var4 var2 var0 var1 var7 var6 var8 var5))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr) (var7 Int) (var8 Addr) (var9 Int)) (or (not (inv_main31 var3 var4 var2 var0 var1 var8 var6 var9 var5 var7)) (inv_main31 var3 var4 var2 var0 var1 var8 var6 var9 var5 var7))))
(assert (forall ((var0 Int) (var1 node) (var2 Addr) (var3 Int) (var4 Heap) (var5 Int) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Int) (var10 Addr) (var11 Int) (var12 Int) (var13 Addr) (var14 Int) (var15 Int) (var16 Int)) (or (not (and (inv_main21 var4 var5 var12 var0 var11 var8 var7) (and (and (= nullAddr var2) (and (and (and (and (and (and (and (and (= var6 (newHeap (alloc var4 (O_node var1)))) (= var9 var5)) (= var14 var12)) (= var15 var0)) (= var16 var11)) (= var13 var8)) (= var10 var7)) (= var3 var11)) (= var2 (newAddr (alloc var4 (O_node var1)))))) (<= 0 (+ (+ var0 (- 1)) (- 1)))))) (inv_main31 var6 var9 var14 var15 var16 var13 var10 var3 var2 1))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Heap) (var5 Int) (var6 Int)) (not (and (inv_main12 var4 var5 var2 var0 var1 var6 var3) (not (is-O_node (read var4 var3)))))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Heap) (var5 Int) (var6 Int)) (not (and (inv_main18 var4 var5 var2 var0 var1 var6 var3) (not (is-O_node (read var4 var3)))))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Int)) (not (and (inv_main28 var3 var4 var2 var0 var1 var7 var6 var8 var5) (not (is-O_node (read var3 var5)))))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Int)) (not (and (inv_main34 var3 var4 var2 var0 var1 var7 var6 var8 var5) (not (is-O_node (read var3 var5)))))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr) (var7 Addr)) (not (and (inv_main36 var3 var4 var2 var0 var1 var7 var6 var5) (not (is-O_node (read var3 var5)))))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr)) (not (and (inv_main22 var3 var4 var2 var0 var1 var6 var5) (not (is-O_node (read var3 var5)))))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Int) (var7 Int) (var8 Int)) (not (and (inv_main51 var5 var6 var2 var4 var8 var7 var3 var1 var0) (not (is-O_node (read var5 var3)))))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Int) (var7 Int) (var8 Int)) (not (and (inv_main50 var5 var6 var2 var4 var8 var7 var3 var1 var0) (not (is-O_node (read var5 var3)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Addr) (var4 Heap) (var5 Int) (var6 Int) (var7 Int)) (not (and (inv_main65 var4 var5 var0 var3 var6 var2 var1 var7) (not (is-O_node (read var4 var1)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Addr) (var4 Heap) (var5 Int) (var6 Int) (var7 Int)) (not (and (inv_main64 var4 var5 var0 var3 var6 var2 var1 var7) (not (is-O_node (read var4 var1)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Int) (var4 Addr) (var5 Int)) (not (and (inv_main72 var2 var3 var0 var1 var5 var4) (not (is-O_node (read var2 var4)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Int) (var4 Addr) (var5 Addr) (var6 Int)) (not (and (inv_main76 var2 var3 var0 var1 var6 var5 var4) (not (is-O_node (read var2 var4)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Int) (var4 Int)) (not (inv_main79 var2 var3 var0 var1 var4))))
(check-sat)
