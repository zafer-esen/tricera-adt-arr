(set-logic HORN)
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
                   ((node (next Addr)))))
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
(declare-fun inv_main15 (Heap Int Int Addr) Bool)
(declare-fun inv_main19 (Heap Int Int Addr Addr) Bool)
(declare-fun inv_main2 (Heap) Bool)
(declare-fun inv_main22 (Heap Int Int Addr Addr Int) Bool)
(declare-fun inv_main30 (Heap Int Addr Int Int Int) Bool)
(declare-fun inv_main36 (Heap Int Addr Int Int) Bool)
(declare-fun inv_main37 (Heap Int Addr Int Int) Bool)
(declare-fun inv_main44 (Heap Int Addr Int Int Int Int Int) Bool)
(declare-fun inv_main49 (Heap Int Addr Int Int Int) Bool)
(declare-fun inv_main58 (Heap Int Addr Int Int Int Int Int Addr Int) Bool)
(declare-fun inv_main6 (Heap Int Int Int) Bool)
(declare-fun inv_main63 (Heap Int Addr Int Int Int Int Int Addr Addr Addr) Bool)
(declare-fun inv_main65 (Heap Int Addr Int Int Int Int Int Addr Addr Addr) Bool)
(declare-fun inv_main68 (Heap Int Addr Int Int Int Int Int Addr Addr Addr) Bool)
(declare-fun inv_main79 (Heap Int Addr Int Int Addr Int) Bool)
(declare-fun inv_main85 (Heap Int Addr Int Int Addr) Bool)
(declare-fun inv_main88 (Heap Int Addr Int Int) Bool)
(assert (inv_main2 emptyHeap))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Addr) (var8 Int) (var9 Heap) (var10 Heap) (var11 Addr) (var12 Int) (var13 Int) (var14 Addr)) (or (not (and (inv_main79 var9 var8 var14 var5 var13 var11 var6) (and (not (= (+ var3 var0) var12)) (and (= var2 nullAddr) (and (and (and (and (and (and (and (= var10 var9) (= var0 var8)) (= var1 var14)) (= var3 var5)) (= var4 var13)) (= var7 var11)) (= var12 var6)) (= var2 (next (getnode (read var9 var11))))))))) (inv_main88 var10 var0 var1 var3 var4))))
(assert (forall ((var0 Int) (var1 Heap) (var2 Int) (var3 Int) (var4 Addr)) (or (not (and (inv_main37 var1 var0 var4 var3 var2) (and (not (= (+ var3 var0) 0)) (= var4 nullAddr)))) (inv_main88 var1 var0 var4 var3 var2))))
(assert (forall ((var0 Int) (var1 Heap) (var2 Int) (var3 Int) (var4 Int) (var5 Addr) (var6 Int)) (or (not (and (inv_main30 var1 var0 var5 var3 var4 var6) (and (not (= var2 0)) (<= 0 (+ (+ var4 (* (- 1) var6)) (- 1)))))) (inv_main30 var1 var0 var5 var3 var4 (+ var6 1)))))
(assert (forall ((var0 Int) (var1 Heap) (var2 Int) (var3 Addr)) (or (not (and (inv_main15 var1 var0 var2 var3) (not (<= 0 (+ var2 (- 1)))))) (inv_main30 var1 var0 var3 0 (+ var0 (- 1)) 0))))
(assert (forall ((var0 Int) (var1 Heap) (var2 Int) (var3 Int) (var4 Addr)) (or (not (and (inv_main36 var1 var0 var4 var3 var2) (not (<= 0 (+ (+ var3 (* (- 1) var2)) (- 1)))))) (inv_main37 var1 var0 var4 var3 var2))))
(assert (forall ((var0 Int) (var1 Heap) (var2 Int) (var3 Int) (var4 Int) (var5 Addr)) (or (not (and (inv_main36 var1 var0 var5 var4 var3) (and (= var2 0) (<= 0 (+ (+ var4 (* (- 1) var3)) (- 1)))))) (inv_main37 var1 var0 var5 var4 var3))))
(assert (forall ((var0 Int) (var1 Heap) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Addr) (var7 Int) (var8 Heap) (var9 Int) (var10 Int) (var11 Int) (var12 Addr) (var13 Int) (var14 Int) (var15 Addr) (var16 Int) (var17 Addr) (var18 Addr)) (or (not (and (inv_main68 var8 var7 var17 var2 var16 var9 var5 var4 var15 var18 var12) (and (and (and (and (and (and (and (= var1 (write var8 var18 (O_node (node var15)))) (= var14 var7)) (= var6 var17)) (= var13 var2)) (= var10 var16)) (= var0 var9)) (= var11 var5)) (= var3 var4)))) (inv_main36 var1 var14 var6 var13 (+ var10 1)))))
(assert (forall ((var0 Int) (var1 Int) (var2 Heap) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Int) (var8 Addr) (var9 Int) (var10 Heap) (var11 Int) (var12 Int) (var13 Addr) (var14 Int) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Int) (var20 Addr) (var21 Addr)) (or (not (and (inv_main63 var10 var9 var20 var4 var19 var12 var7 var6 var18 var21 var15) (and (= var17 nullAddr) (and (and (and (and (and (and (and (and (and (and (= var2 (write var10 var18 (O_node (node var15)))) (= var11 var9)) (= var8 var20)) (= var5 var4)) (= var0 var19)) (= var1 var12)) (= var3 var7)) (= var14 var6)) (= var13 var18)) (= var17 var21)) (= var16 var15))))) (inv_main36 var2 var11 var13 var5 (+ var0 1)))))
(assert (forall ((var0 Int) (var1 Heap) (var2 Int) (var3 Int) (var4 Addr) (var5 Int)) (or (not (and (inv_main30 var1 var0 var4 var2 var3 var5) (not (<= 0 (+ (+ var3 (* (- 1) var5)) (- 1)))))) (inv_main36 var1 var0 var4 var5 0))))
(assert (forall ((var0 Int) (var1 Heap) (var2 Int) (var3 Int) (var4 Addr) (var5 Int) (var6 Int)) (or (not (and (inv_main30 var1 var0 var4 var2 var3 var6) (and (= var5 0) (<= 0 (+ (+ var3 (* (- 1) var6)) (- 1)))))) (inv_main36 var1 var0 var4 var6 0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Addr) (var8 Int) (var9 Heap) (var10 Heap) (var11 Addr) (var12 Int) (var13 Int) (var14 Addr)) (or (not (and (inv_main79 var9 var8 var14 var5 var13 var11 var6) (and (not (= var2 nullAddr)) (and (and (and (and (and (and (and (= var10 var9) (= var0 var8)) (= var1 var14)) (= var3 var5)) (= var4 var13)) (= var7 var11)) (= var12 var6)) (= var2 (next (getnode (read var9 var11)))))))) (inv_main79 var10 var0 var1 var3 var4 var2 (+ var12 1)))))
(assert (forall ((var0 Int) (var1 Heap) (var2 Int) (var3 Int) (var4 Addr)) (or (not (and (inv_main37 var1 var0 var4 var3 var2) (not (= var4 nullAddr)))) (inv_main79 var1 var0 var4 var3 var2 var4 1))))
(assert (forall ((var0 Int) (var1 Heap) (var2 Int) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Int) (var7 Int) (var8 node) (var9 Addr)) (or (not (and (inv_main15 var3 var2 var7 var9) (and (and (not (= nullAddr var5)) (and (and (and (and (= var1 (newHeap (alloc var3 (O_node var8)))) (= var0 var2)) (= var6 (+ var7 (- 1)))) (= var4 var9)) (= var5 (newAddr (alloc var3 (O_node var8)))))) (<= 0 (+ var7 (- 1)))))) (inv_main19 var1 var0 var6 var4 var5))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Heap) (var4 Int) (var5 Int) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main19 var3 var2 var5 var7 var8) (and (and (and (and (= var9 (write var3 var8 (O_node (node var7)))) (= var0 var2)) (= var4 var5)) (= var1 var7)) (= var6 var8)))) (inv_main15 var9 var0 var4 var6))))
(assert (forall ((var0 Int) (var1 Heap) (var2 Int) (var3 Int)) (or (not (and (inv_main6 var1 var0 var2 var3) (not (<= 0 (+ (+ var2 (* (- 1) var3)) (- 1)))))) (inv_main15 var1 var3 var3 nullAddr))))
(assert (forall ((var0 Int) (var1 Int) (var2 Heap) (var3 Int) (var4 Int)) (or (not (and (inv_main6 var2 var0 var3 var4) (and (= var1 0) (<= 0 (+ (+ var3 (* (- 1) var4)) (- 1)))))) (inv_main15 var2 var4 var4 nullAddr))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap) (var6 Addr) (var7 Int) (var8 Int) (var9 Int) (var10 Int) (var11 Heap) (var12 Int) (var13 Int) (var14 Addr) (var15 Addr) (var16 Int) (var17 Addr) (var18 Int) (var19 Int) (var20 Addr) (var21 Addr)) (or (not (and (inv_main63 var11 var10 var20 var4 var19 var12 var8 var7 var17 var21 var15) (and (not (= var6 nullAddr)) (and (and (and (and (and (and (and (and (and (and (= var5 (write var11 var17 (O_node (node var15)))) (= var1 var10)) (= var3 var20)) (= var18 var4)) (= var13 var19)) (= var16 var12)) (= var9 var8)) (= var0 var7)) (= var14 var17)) (= var6 var21)) (= var2 var15))))) (inv_main68 var5 var1 var3 var18 var13 var16 var9 var0 var14 var6 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap) (var5 Int) (var6 Addr) (var7 Addr) (var8 Int) (var9 Int) (var10 Int) (var11 Heap) (var12 Addr) (var13 Int) (var14 Int) (var15 Int) (var16 Heap) (var17 Int) (var18 Addr) (var19 Addr)) (or (not (and (inv_main85 var11 var10 var18 var8 var17 var1) (and (not (= var7 nullAddr)) (and (and (and (and (and (and (and (= var4 var11) (= var13 var10)) (= var2 var18)) (= var5 var8)) (= var15 var17)) (= var19 var1)) (= var12 (next (getnode (read var11 var1))))) (and (and (and (and (and (and (= var16 (write var4 var19 defObj)) (= var9 var13)) (= var0 var2)) (= var14 var5)) (= var3 var15)) (= var6 var19)) (= var7 var12)))))) (inv_main85 var16 var9 var0 var14 var3 var7))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Addr) (var8 Int) (var9 Heap) (var10 Heap) (var11 Addr) (var12 Int) (var13 Int) (var14 Addr)) (or (not (and (inv_main79 var9 var8 var14 var5 var13 var11 var6) (and (not (= var1 nullAddr)) (and (= (+ var3 var0) var12) (and (= var2 nullAddr) (and (and (and (and (and (and (and (= var10 var9) (= var0 var8)) (= var1 var14)) (= var3 var5)) (= var4 var13)) (= var7 var11)) (= var12 var6)) (= var2 (next (getnode (read var9 var11)))))))))) (inv_main85 var10 var0 var1 var3 var4 var1))))
(assert (forall ((var0 Int) (var1 Heap) (var2 Int) (var3 Int) (var4 Addr)) (or (not (and (inv_main37 var1 var0 var4 var3 var2) (and (not (= var4 nullAddr)) (and (= (+ var3 var0) 0) (= var4 nullAddr))))) (inv_main85 var1 var0 var4 var3 var2 var4))))
(assert (forall ((var0 Int) (var1 Heap) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Addr)) (or (not (and (inv_main44 var1 var0 var7 var6 var5 var2 var4 var3) (not (<= 0 (+ (+ var4 (* (- 1) var3)) (- 1)))))) (inv_main49 var1 var0 var7 var6 var5 var3))))
(assert (forall ((var0 Int) (var1 Heap) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Int) (var8 Addr)) (or (not (and (inv_main44 var1 var0 var8 var7 var6 var2 var5 var3) (and (= var4 0) (<= 0 (+ (+ var5 (* (- 1) var3)) (- 1)))))) (inv_main49 var1 var0 var8 var7 var6 var3))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Heap) (var4 Int) (var5 Addr) (var6 Int) (var7 Int) (var8 Addr) (var9 Int)) (or (not (inv_main58 var3 var2 var8 var7 var6 var4 var0 var9 var5 var1)) (inv_main58 var3 var2 var8 var7 var6 var4 var0 var9 var5 var1))))
(assert (forall ((var0 Int) (var1 Int) (var2 Heap) (var3 Addr) (var4 Int) (var5 Int) (var6 Addr) (var7 node) (var8 Int) (var9 Heap) (var10 Int) (var11 Int) (var12 Int) (var13 Int) (var14 Int) (var15 Addr)) (or (not (and (inv_main49 var9 var8 var15 var4 var14 var10) (and (= nullAddr var6) (and (and (and (and (and (and (and (and (= var2 (newHeap (alloc var9 (O_node var7)))) (= var1 var8)) (= var3 var15)) (= var0 var4)) (= var5 var14)) (= var13 var10)) (= var12 2)) (= var11 var10)) (= var6 (newAddr (alloc var9 (O_node var7)))))))) (inv_main58 var2 var1 var3 var0 var5 var13 var12 var11 var6 1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Int) (var5 Int) (var6 Heap) (var7 Int) (var8 Int) (var9 Int) (var10 Heap) (var11 Int) (var12 Int) (var13 Int) (var14 Addr) (var15 Int) (var16 Addr) (var17 Addr) (var18 Int) (var19 Addr) (var20 Addr) (var21 Int) (var22 Addr)) (or (not (and (inv_main65 var10 var9 var19 var2 var18 var11 var8 var7 var16 var22 var14) (and (<= 0 (+ var15 (- 1))) (and (and (and (and (and (and (and (and (and (and (and (= var6 var10) (= var21 var9)) (= var20 var19)) (= var5 var2)) (= var13 var18)) (= var4 var11)) (= var12 var8)) (= var15 var7)) (= var3 var16)) (= var0 var22)) (= var17 var14)) (= var1 (next (getnode (read var10 var14)))))))) (inv_main65 var6 var21 var20 var5 var13 var4 var12 (+ var15 (- 1)) var3 var1 var1))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Int) (var4 Int) (var5 node) (var6 Addr) (var7 Int) (var8 Int) (var9 Int) (var10 Int) (var11 Int) (var12 Int) (var13 Addr) (var14 Addr) (var15 Int) (var16 Heap) (var17 Int) (var18 Int) (var19 Heap) (var20 Int) (var21 Heap) (var22 Int) (var23 Addr) (var24 Int) (var25 Addr)) (or (not (and (inv_main49 var16 var15 var23 var10 var22 var17) (and (and (<= 0 (+ var12 (- 1))) (and (and (and (and (and (and (and (and (and (= var19 var21) (= var11 var9)) (= var14 var25)) (= var2 var3)) (= var24 var1)) (= var20 var7)) (= var8 var18)) (= var12 var4)) (= var13 var0)) (= var6 nullAddr))) (and (not (= nullAddr var0)) (and (and (and (and (and (and (and (and (= var21 (newHeap (alloc var16 (O_node var5)))) (= var9 var15)) (= var25 var23)) (= var3 var10)) (= var1 var22)) (= var7 var17)) (= var18 2)) (= var4 var17)) (= var0 (newAddr (alloc var16 (O_node var5))))))))) (inv_main65 var19 var11 var14 var2 var24 var20 var8 (+ var12 (- 1)) var13 var14 var14))))
(assert (forall ((var0 Int) (var1 Int) (var2 Heap) (var3 Int) (var4 Int)) (or (not (and (inv_main6 var2 var0 var3 var4) (and (not (= var1 0)) (<= 0 (+ (+ var3 (* (- 1) var4)) (- 1)))))) (inv_main6 var2 var0 var3 (+ var4 1)))))
(assert (forall ((var0 Heap)) (or (not (inv_main2 var0)) (inv_main6 var0 2 5 2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Int) (var5 Int) (var6 Heap) (var7 Int) (var8 Int) (var9 Int) (var10 Heap) (var11 Int) (var12 Int) (var13 Int) (var14 Addr) (var15 Int) (var16 Addr) (var17 Addr) (var18 Int) (var19 Addr) (var20 Addr) (var21 Int) (var22 Addr)) (or (not (and (inv_main65 var10 var9 var19 var2 var18 var11 var8 var7 var16 var22 var14) (and (not (<= 0 (+ var15 (- 1)))) (and (and (and (and (and (and (and (and (and (and (and (= var6 var10) (= var21 var9)) (= var20 var19)) (= var5 var2)) (= var13 var18)) (= var4 var11)) (= var12 var8)) (= var15 var7)) (= var3 var16)) (= var0 var22)) (= var17 var14)) (= var1 (next (getnode (read var10 var14)))))))) (inv_main63 var6 var21 var20 var5 var13 var4 var12 (+ var15 (- 1)) var3 var0 var1))))
(assert (forall ((var0 Int) (var1 Int) (var2 Heap) (var3 Int) (var4 Int) (var5 Int) (var6 node) (var7 Int) (var8 Int) (var9 Int) (var10 Addr) (var11 Addr) (var12 Int) (var13 Int) (var14 Heap) (var15 Int) (var16 Heap) (var17 Int) (var18 Int) (var19 Int) (var20 Int) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Int) (var25 Addr)) (or (not (and (inv_main49 var14 var13 var21 var8 var20 var15) (and (and (not (<= 0 (+ var9 (- 1)))) (and (and (and (and (and (and (and (and (and (= var2 var16) (= var7 var18)) (= var10 var11)) (= var24 var4)) (= var12 var3)) (= var1 var19)) (= var17 var5)) (= var9 var0)) (= var23 var25)) (= var22 nullAddr))) (and (not (= nullAddr var25)) (and (and (and (and (and (and (and (and (= var16 (newHeap (alloc var14 (O_node var6)))) (= var18 var13)) (= var11 var21)) (= var4 var8)) (= var3 var20)) (= var19 var15)) (= var5 2)) (= var0 var15)) (= var25 (newAddr (alloc var14 (O_node var6))))))))) (inv_main63 var2 var7 var10 var24 var12 var1 var17 (+ var9 (- 1)) var23 var22 var10))))
(assert (forall ((var0 Int) (var1 Heap) (var2 Int) (var3 Int) (var4 Addr) (var5 Addr)) (or (not (inv_main22 var1 var0 var2 var4 var5 var3)) (inv_main22 var1 var0 var2 var4 var5 var3))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Heap) (var3 Int) (var4 Int) (var5 Int) (var6 Heap) (var7 Addr) (var8 node) (var9 Addr)) (or (not (and (inv_main15 var2 var1 var5 var7) (and (and (= nullAddr var0) (and (and (and (and (= var6 (newHeap (alloc var2 (O_node var8)))) (= var3 var1)) (= var4 (+ var5 (- 1)))) (= var9 var7)) (= var0 (newAddr (alloc var2 (O_node var8)))))) (<= 0 (+ var5 (- 1)))))) (inv_main22 var6 var3 var4 var9 var0 1))))
(assert (forall ((var0 Int) (var1 Heap) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Int) (var8 Addr)) (or (not (and (inv_main44 var1 var0 var8 var7 var6 var2 var5 var3) (and (not (= var4 0)) (<= 0 (+ (+ var5 (* (- 1) var3)) (- 1)))))) (inv_main44 var1 var0 var8 var7 var6 var2 var5 (+ var3 1)))))
(assert (forall ((var0 Int) (var1 Heap) (var2 Int) (var3 Int) (var4 Addr) (var5 Int)) (or (not (and (inv_main36 var1 var0 var4 var3 var2) (and (not (= var5 0)) (<= 0 (+ (+ var3 (* (- 1) var2)) (- 1)))))) (inv_main44 var1 var0 var4 var3 var2 0 (+ var2 (+ var0 (- 1))) 0))))
(assert (forall ((var0 Int) (var1 Heap) (var2 Int) (var3 Addr) (var4 Addr)) (not (and (inv_main19 var1 var0 var2 var3 var4) (not (is-O_node (read var1 var4)))))))
(assert (forall ((var0 Int) (var1 Int) (var2 Heap) (var3 Int) (var4 Addr) (var5 Addr) (var6 Int) (var7 Int) (var8 Addr) (var9 Addr) (var10 Int)) (not (and (inv_main65 var2 var1 var8 var7 var6 var3 var0 var10 var5 var9 var4) (not (is-O_node (read var2 var4)))))))
(assert (forall ((var0 Int) (var1 Int) (var2 Heap) (var3 Int) (var4 Addr) (var5 Addr) (var6 Int) (var7 Int) (var8 Addr) (var9 Addr) (var10 Int)) (not (and (inv_main63 var2 var1 var8 var7 var6 var3 var0 var10 var5 var9 var4) (not (is-O_node (read var2 var5)))))))
(assert (forall ((var0 Int) (var1 Int) (var2 Heap) (var3 Int) (var4 Addr) (var5 Addr) (var6 Int) (var7 Int) (var8 Addr) (var9 Addr) (var10 Int)) (not (and (inv_main68 var2 var1 var8 var7 var6 var3 var0 var10 var5 var9 var4) (not (is-O_node (read var2 var9)))))))
(assert (forall ((var0 Int) (var1 Heap) (var2 Addr) (var3 Int) (var4 Int) (var5 Addr) (var6 Int)) (not (and (inv_main79 var1 var0 var5 var4 var3 var2 var6) (not (is-O_node (read var1 var2)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Heap) (var3 Int) (var4 Int) (var5 Addr)) (not (and (inv_main85 var2 var1 var5 var4 var3 var0) (not (is-O_node (read var2 var0)))))))
(assert (forall ((var0 Int) (var1 Heap) (var2 Int) (var3 Int) (var4 Addr)) (not (inv_main88 var1 var0 var4 var3 var2))))
(check-sat)
