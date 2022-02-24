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
(declare-fun inv_main34 (Heap Int Int Addr Int Int Int Int Addr) Bool)
(declare-fun inv_main37 (Heap Int Int Addr Int Int Int Int Addr Int) Bool)
(declare-fun inv_main4 (Heap Int Int) Bool)
(declare-fun inv_main40 (Heap Int Int Addr Int Int Int Int Addr) Bool)
(declare-fun inv_main41 (Heap Int Int Addr Int Int Int Int Addr) Bool)
(declare-fun inv_main45 (Heap Int Int Addr Int Int Int Addr Addr Addr) Bool)
(declare-fun inv_main48 (Heap Int Int Addr Int Int Int Addr Addr Addr) Bool)
(declare-fun inv_main51 (Heap Int Int Addr Int Int Int Addr Addr Addr) Bool)
(declare-fun inv_main52 (Heap Int Int Addr Int Int Int Addr Addr Addr) Bool)
(declare-fun inv_main53 (Heap Int Int Addr Int Int Int Addr Addr Addr) Bool)
(declare-fun inv_main54 (Heap Int Int Addr Int Int Int Addr Addr Addr) Bool)
(declare-fun inv_main56 (Heap Int Int Addr Int Int Int Addr Addr Addr) Bool)
(declare-fun inv_main60 (Heap Int Int Addr Int Int Int Addr Addr Addr) Bool)
(declare-fun inv_main63 (Heap Int Int Addr Addr Int) Bool)
(declare-fun inv_main65 (Heap Int Int Addr Addr Int) Bool)
(declare-fun inv_main66 (Heap Int Int Addr Addr Int Addr) Bool)
(declare-fun inv_main78 (Heap Int Int Addr Addr Int Addr) Bool)
(declare-fun inv_main8 (Heap Int Int Int Int Addr) Bool)
(declare-fun inv_main81 (Heap Int Int Addr Addr Int) Bool)
(assert (forall ((var0 Heap)) (or (not (= var0 emptyHeap)) (inv_main4 var0 2 1))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Int) (var4 Addr) (var5 Heap) (var6 Int) (var7 Addr) (var8 Int) (var9 Int)) (or (not (inv_main37 var5 var6 var1 var4 var8 var9 var3 var0 var7 var2)) (inv_main37 var5 var6 var1 var4 var8 var9 var3 var0 var7 var2))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Addr) (var4 Int) (var5 Addr) (var6 Int) (var7 Heap) (var8 Int) (var9 Heap) (var10 Int) (var11 node) (var12 Int) (var13 Addr) (var14 Int) (var15 Int) (var16 Int) (var17 Int) (var18 Int) (var19 Int) (var20 Int) (var21 Int) (var22 Heap) (var23 Int)) (or (not (and (inv_main8 var7 var8 var16 var6 var2 var13) (and (and (and (= nullAddr var1) (and (and (and (and (and (and (and (and (= var9 (newHeap (alloc var22 (O_node var11)))) (= var19 var17)) (= var14 var4)) (= var5 var3)) (= var12 var10)) (= var18 var15)) (= var21 var20)) (= var0 var15)) (= var1 (newAddr (alloc var22 (O_node var11)))))) (and (and (and (and (and (and (= var22 var7) (= var17 var8)) (= var4 var16)) (= var3 var13)) (= var10 3)) (= var15 var16)) (and (and (and (and (<= 0 (+ (+ 2 (* (- 1) (+ var8 (* (- 2) var23)))) (- 1))) (<= 0 (+ (+ 2 (* 1 (+ var8 (* (- 2) var23)))) (- 1)))) (or (not (<= 0 (+ (+ var8 (* (- 2) var23)) (- 1)))) (<= 0 (+ var8 (- 1))))) (or (not (<= 0 (+ (* (- 1) (+ var8 (* (- 2) var23))) (- 1)))) (<= 0 (+ (* (- 1) var8) (- 1))))) (= var20 var23)))) (not (<= 0 (+ var6 (- 1))))))) (inv_main37 var9 var19 var14 var5 var12 var18 var21 var0 var1 1))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Int) (var4 Heap) (var5 Int) (var6 Int) (var7 Int) (var8 Heap) (var9 Int) (var10 node) (var11 Addr) (var12 Int) (var13 Int) (var14 Heap) (var15 Addr) (var16 Int) (var17 Int) (var18 Int) (var19 Int) (var20 Addr) (var21 Addr) (var22 Int) (var23 Int)) (or (not (and (inv_main8 var8 var9 var13 var7 var5 var11) (and (and (and (not (= nullAddr var20)) (and (and (and (and (and (and (and (and (= var14 (newHeap (alloc var4 (O_node var10)))) (= var1 var3)) (= var17 var0)) (= var15 var21)) (= var6 var2)) (= var16 var19)) (= var22 var12)) (= var18 var19)) (= var20 (newAddr (alloc var4 (O_node var10)))))) (and (and (and (and (and (and (= var4 var8) (= var3 var9)) (= var0 var13)) (= var21 var11)) (= var2 3)) (= var19 var13)) (and (and (and (and (<= 0 (+ (+ 2 (* (- 1) (+ var9 (* (- 2) var23)))) (- 1))) (<= 0 (+ (+ 2 (* 1 (+ var9 (* (- 2) var23)))) (- 1)))) (or (not (<= 0 (+ (+ var9 (* (- 2) var23)) (- 1)))) (<= 0 (+ var9 (- 1))))) (or (not (<= 0 (+ (* (- 1) (+ var9 (* (- 2) var23))) (- 1)))) (<= 0 (+ (* (- 1) var9) (- 1))))) (= var12 var23)))) (not (<= 0 (+ var7 (- 1))))))) (inv_main34 var14 var1 var17 var15 var6 var16 var22 var18 var20))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Addr) (var4 Heap) (var5 Int) (var6 Int) (var7 Addr) (var8 Addr) (var9 Int)) (or (not (and (inv_main45 var4 var5 var1 var3 var6 var9 var2 var0 var7 var8) (and (= var7 nullAddr) (not (<= 0 (+ var2 (- 1))))))) (inv_main52 var4 var5 var1 var3 var6 var9 var2 var0 var7 var8))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Heap) (var5 Int) (var6 Addr) (var7 Addr) (var8 Int) (var9 Addr) (var10 Int) (var11 Int) (var12 Heap) (var13 Addr) (var14 Int) (var15 Int) (var16 Int) (var17 Addr) (var18 Addr) (var19 Int)) (or (not (and (inv_main54 var4 var5 var11 var13 var15 var8 var3 var0 var17 var7) (and (not (= var6 nullAddr)) (and (and (and (and (and (and (and (and (and (= var12 (write var4 var0 (O_node (node (data (getnode (read var4 var0))) var7 (prev (getnode (read var4 var0))))))) (= var14 var5)) (= var10 var11)) (= var1 var13)) (= var2 var15)) (= var19 var8)) (= var16 var3)) (= var18 var0)) (= var9 var17)) (= var6 var7))))) (inv_main56 var12 var14 var10 var1 var2 var19 var16 var18 var9 var6))))
(assert (forall ((var0 Int) (var1 Int) (var2 Heap) (var3 Int) (var4 Addr) (var5 Int) (var6 Addr) (var7 Addr) (var8 Int) (var9 Int) (var10 Addr) (var11 Int) (var12 Int) (var13 Heap)) (or (not (and (inv_main19 var2 var3 var8 var1 var0 var7 var4) (and (not (= var6 nullAddr)) (and (and (and (and (and (and (= var13 (write var2 var4 (O_node (node (data (getnode (read var2 var4))) (next (getnode (read var2 var4))) nullAddr)))) (= var11 var3)) (= var9 var8)) (= var12 var1)) (= var5 var0)) (= var6 var7)) (= var10 var4))))) (inv_main22 var13 var11 var9 var12 var5 var6 var10))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Addr) (var4 Heap) (var5 Int) (var6 Int) (var7 Addr) (var8 Addr) (var9 Int)) (or (not (inv_main51 var4 var5 var1 var3 var6 var9 var2 var0 var7 var8)) (inv_main53 (write var4 var7 (O_node (node (data (getnode (read var4 var7))) var0 (prev (getnode (read var4 var7)))))) var5 var1 var3 var6 var9 var2 var0 var7 var8))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Int) (var4 Heap) (var5 Int) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Int) (var11 Int) (var12 Int) (var13 Heap)) (or (not (and (inv_main22 var4 var5 var11 var3 var1 var9 var8) (and (and (and (and (and (and (= var13 (write var4 var9 (O_node (node (data (getnode (read var4 var9))) (next (getnode (read var4 var9))) var8)))) (= var10 var5)) (= var0 var11)) (= var12 var3)) (= var2 var1)) (= var6 var9)) (= var7 var8)))) (inv_main8 var13 var10 var0 (+ var12 (- 1)) var2 var7))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Heap) (var6 Int) (var7 Addr) (var8 Int) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Int) (var13 Int)) (or (not (and (inv_main19 var5 var6 var12 var4 var0 var10 var7) (and (= var11 nullAddr) (and (and (and (and (and (and (= var9 (write var5 var7 (O_node (node (data (getnode (read var5 var7))) (next (getnode (read var5 var7))) nullAddr)))) (= var8 var6)) (= var13 var12)) (= var2 var4)) (= var3 var0)) (= var11 var10)) (= var1 var7))))) (inv_main8 var9 var8 var13 (+ var2 (- 1)) var3 var1))))
(assert (forall ((var0 Int) (var1 Heap) (var2 Int)) (or (not (inv_main4 var1 var2 var0)) (inv_main8 var1 var2 var0 var2 var0 nullAddr))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Heap) (var5 Int) (var6 Int) (var7 Addr) (var8 Int) (var9 Heap) (var10 Addr) (var11 Int) (var12 Int) (var13 Addr) (var14 Int) (var15 Int) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Int)) (or (not (and (inv_main52 var4 var5 var12 var13 var14 var8 var3 var0 var17 var7) (and (not (= var16 nullAddr)) (and (and (and (and (and (and (and (and (and (= var9 (write var4 var0 (O_node (node (data (getnode (read var4 var0))) var13 (prev (getnode (read var4 var0))))))) (= var15 var5)) (= var6 var12)) (= var16 var13)) (= var2 var14)) (= var19 var8)) (= var11 var3)) (= var10 var0)) (= var1 var17)) (= var18 var7))))) (inv_main60 var9 var15 var6 var16 var2 var19 var11 var10 var1 var18))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Int) (var4 Addr) (var5 Int)) (or (not (inv_main65 var2 var3 var0 var1 var4 var5)) (inv_main66 var2 var3 var0 var1 var4 var5 (next (getnode (read var2 var4)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Heap) (var3 Int) (var4 Heap) (var5 Int) (var6 Int) (var7 Addr) (var8 Addr) (var9 Int) (var10 Addr) (var11 Int) (var12 Int) (var13 Addr) (var14 Addr) (var15 Int) (var16 Int) (var17 Addr) (var18 Int) (var19 Addr) (var20 Addr)) (or (not (and (inv_main48 var4 var5 var12 var14 var15 var11 var3 var0 var19 var10) (and (and (and (and (and (and (and (and (and (and (= var2 var4) (= var18 var5)) (= var9 var12)) (= var7 var14)) (= var6 var15)) (= var16 var11)) (= var1 var3)) (= var13 var0)) (= var8 var19)) (= var17 var10)) (= var20 (next (getnode (read var4 var10))))))) (inv_main45 var2 var18 var9 var7 var6 var16 (+ var1 (- 1)) var13 var8 var20))))
(assert (forall ((var0 Heap) (var1 Heap) (var2 Int) (var3 Int) (var4 Addr) (var5 Int) (var6 Heap) (var7 Int) (var8 Int) (var9 Addr) (var10 Addr) (var11 Int) (var12 Int) (var13 Int) (var14 Int) (var15 Int) (var16 Int) (var17 Int) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Int) (var22 Int) (var23 Int) (var24 Int) (var25 Int) (var26 Addr)) (or (not (and (inv_main41 var6 var7 var15 var18 var21 var11 var5 var14 var20) (and (and (and (and (and (and (and (and (and (= var1 var0) (= var13 var2)) (= var24 var22)) (= var9 var4)) (= var12 var3)) (= var8 var23)) (= var17 var16)) (= var19 var26)) (= var10 nullAddr)) (and (and (and (and (and (and (and (and (= var0 (write var6 var20 (O_node (node var14 (next (getnode (read var6 var20))) (prev (getnode (read var6 var20))))))) (= var2 var7)) (= var22 var15)) (= var4 var18)) (= var3 var21)) (= var23 var11)) (= var16 var5)) (= var25 var14)) (= var26 var20))))) (inv_main45 var1 var13 var24 var9 var12 var8 var17 var19 var10 var9))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Heap) (var5 Int) (var6 Addr) (var7 Int) (var8 Int)) (or (not (inv_main40 var4 var5 var1 var3 var7 var8 var2 var0 var6)) (inv_main41 (write var4 var6 (O_node (node (data (getnode (read var4 var6))) (next (getnode (read var4 var6))) nullAddr))) var5 var1 var3 var7 var8 var2 var0 var6))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Heap) (var5 Int) (var6 Addr) (var7 Int) (var8 Int)) (or (not (inv_main34 var4 var5 var1 var3 var7 var8 var2 var0 var6)) (inv_main40 (write var4 var6 (O_node (node (data (getnode (read var4 var6))) nullAddr (prev (getnode (read var4 var6)))))) var5 var1 var3 var7 var8 var2 var0 var6))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Int) (var4 Addr) (var5 Int)) (or (not (and (inv_main63 var2 var3 var0 var1 var4 var5) (not (= var4 nullAddr)))) (inv_main65 var2 var3 var0 var1 var4 var5))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Int) (var4 Addr) (var5 Int) (var6 Heap) (var7 Int) (var8 Addr) (var9 Addr) (var10 Int) (var11 Int) (var12 Heap) (var13 Heap) (var14 Addr) (var15 Int) (var16 Int) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Int) (var22 Addr)) (or (not (and (inv_main78 var6 var7 var15 var17 var8 var21 var20) (and (not (= var2 nullAddr)) (and (and (and (and (and (and (and (and (= var12 var6) (= var5 var7)) (= var16 var15)) (= var19 var17)) (= var22 var8)) (= var10 var21)) (= var0 var20)) (= var14 (next (getnode (read var6 var20))))) (and (and (and (and (and (and (and (= var13 (write var12 var0 defObj)) (= var3 var5)) (= var1 var16)) (= var4 var19)) (= var18 var22)) (= var11 var10)) (= var9 var0)) (= var2 var14)))))) (inv_main78 var13 var3 var1 var4 var18 var11 var2))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Int) (var4 Addr) (var5 Int)) (or (not (and (inv_main63 var2 var3 var0 var1 var4 var5) (and (not (= var1 nullAddr)) (and (= var5 (+ 1 var3)) (= var4 nullAddr))))) (inv_main78 var2 var3 var0 var1 var4 var5 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Int) (var4 Addr) (var5 Int) (var6 Addr)) (or (not (and (inv_main66 var2 var3 var0 var1 var4 var5 var6) (not (= var0 (data (getnode (read var2 var4))))))) (inv_main81 var2 var3 var0 var1 var4 var5))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Int) (var4 Addr) (var5 Int)) (or (not (and (inv_main63 var2 var3 var0 var1 var4 var5) (and (not (= var5 (+ 1 var3))) (= var4 nullAddr)))) (inv_main81 var2 var3 var0 var1 var4 var5))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Int) (var4 Heap) (var5 Int) (var6 Addr) (var7 Addr)) (or (not (inv_main15 var4 var5 var0 var3 var1 var7 var6 var2)) (inv_main15 var4 var5 var0 var3 var1 var7 var6 var2))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Heap) (var4 Int) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Int) (var9 Int) (var10 node) (var11 Int) (var12 Int) (var13 Int)) (or (not (and (inv_main8 var3 var4 var11 var2 var1 var7) (and (and (= nullAddr var5) (and (and (and (and (and (and (= var6 (newHeap (alloc var3 (O_node var10)))) (= var13 var4)) (= var9 var11)) (= var12 var2)) (= var8 var1)) (= var0 var7)) (= var5 (newAddr (alloc var3 (O_node var10)))))) (<= 0 (+ var2 (- 1)))))) (inv_main15 var6 var13 var9 var12 var8 var0 var5 1))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr)) (or (not (inv_main18 var3 var4 var0 var2 var1 var6 var5)) (inv_main19 (write var3 var5 (O_node (node (data (getnode (read var3 var5))) var6 (prev (getnode (read var3 var5)))))) var4 var0 var2 var1 var6 var5))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Int) (var4 Addr) (var5 Int) (var6 Addr)) (or (not (and (inv_main66 var2 var3 var0 var1 var4 var5 var6) (= var0 (data (getnode (read var2 var4)))))) (inv_main63 var2 var3 var0 var1 var6 (+ var5 1)))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Heap) (var4 Int) (var5 Addr) (var6 Int) (var7 Addr) (var8 Int) (var9 Int) (var10 Int) (var11 Heap) (var12 Addr) (var13 Int) (var14 Addr) (var15 Int) (var16 Int)) (or (not (and (inv_main56 var3 var4 var10 var12 var13 var9 var2 var0 var14 var7) (and (and (and (and (and (and (= var11 (write var3 var7 (O_node (node (data (getnode (read var3 var7))) (next (getnode (read var3 var7))) var0)))) (= var6 var4)) (= var1 var10)) (= var5 var12)) (= var16 var13)) (= var8 var9)) (= var15 var2)))) (inv_main63 var11 var6 var1 var5 var5 0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Heap) (var4 Int) (var5 Heap) (var6 Int) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Int) (var11 Int) (var12 Int) (var13 Int) (var14 Addr) (var15 Int) (var16 Addr) (var17 Int) (var18 Addr) (var19 Int)) (or (not (and (inv_main54 var5 var6 var15 var16 var17 var11 var4 var0 var18 var9) (and (= var8 nullAddr) (and (and (and (and (and (and (and (and (and (= var3 (write var5 var0 (O_node (node (data (getnode (read var5 var0))) var9 (prev (getnode (read var5 var0))))))) (= var19 var6)) (= var1 var15)) (= var7 var16)) (= var12 var17)) (= var10 var11)) (= var13 var4)) (= var14 var0)) (= var2 var18)) (= var8 var9))))) (inv_main63 var3 var19 var1 var7 var7 0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap) (var6 Int) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Int) (var11 Int) (var12 Int) (var13 Addr) (var14 Int) (var15 Int) (var16 Int) (var17 Addr) (var18 Addr) (var19 Int)) (or (not (and (inv_main60 var5 var6 var12 var13 var16 var10 var4 var1 var18 var8) (and (and (and (and (and (and (and (and (and (= var7 (write var5 var13 (O_node (node (data (getnode (read var5 var13))) (next (getnode (read var5 var13))) var1)))) (= var19 var6)) (= var14 var12)) (= var9 var13)) (= var11 var16)) (= var0 var10)) (= var15 var4)) (= var17 var1)) (= var3 var18)) (= var2 var8)))) (inv_main63 var7 var19 var14 var17 var17 0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap) (var6 Int) (var7 Int) (var8 Addr) (var9 Int) (var10 Addr) (var11 Addr) (var12 Int) (var13 Int) (var14 Addr) (var15 Addr) (var16 Int) (var17 Heap) (var18 Addr) (var19 Int)) (or (not (and (inv_main52 var5 var6 var13 var15 var16 var12 var4 var2 var18 var11) (and (= var10 nullAddr) (and (and (and (and (and (and (and (and (and (= var17 (write var5 var2 (O_node (node (data (getnode (read var5 var2))) var15 (prev (getnode (read var5 var2))))))) (= var0 var6)) (= var19 var13)) (= var10 var15)) (= var7 var16)) (= var1 var12)) (= var9 var4)) (= var14 var2)) (= var8 var18)) (= var3 var11))))) (inv_main63 var17 var0 var19 var14 var14 0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Addr) (var4 Heap) (var5 Int) (var6 Int) (var7 Addr) (var8 Addr) (var9 Int)) (or (not (and (inv_main45 var4 var5 var1 var3 var6 var9 var2 var0 var7 var8) (<= 0 (+ var2 (- 1))))) (inv_main48 var4 var5 var1 var3 var6 var9 var2 var0 var8 var8))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Addr) (var4 Heap) (var5 Int) (var6 Int) (var7 Addr) (var8 Addr) (var9 Int)) (or (not (and (inv_main45 var4 var5 var1 var3 var6 var9 var2 var0 var7 var8) (and (not (= var7 nullAddr)) (not (<= 0 (+ var2 (- 1))))))) (inv_main51 var4 var5 var1 var3 var6 var9 var2 var0 var7 var8))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Addr) (var4 Heap) (var5 Int) (var6 Int) (var7 Addr) (var8 Addr) (var9 Int)) (or (not (inv_main53 var4 var5 var1 var3 var6 var9 var2 var0 var7 var8)) (inv_main54 (write var4 var0 (O_node (node (data (getnode (read var4 var0))) (next (getnode (read var4 var0))) var7))) var5 var1 var3 var6 var9 var2 var0 var7 var8))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Int) (var4 Int) (var5 Heap) (var6 Int) (var7 Addr) (var8 Int) (var9 Int) (var10 Addr) (var11 node) (var12 Int) (var13 Heap)) (or (not (and (inv_main8 var5 var6 var12 var4 var3 var10) (and (and (not (= nullAddr var2)) (and (and (and (and (and (and (= var13 (newHeap (alloc var5 (O_node var11)))) (= var0 var6)) (= var1 var12)) (= var9 var4)) (= var8 var3)) (= var7 var10)) (= var2 (newAddr (alloc var5 (O_node var11)))))) (<= 0 (+ var4 (- 1)))))) (inv_main12 var13 var0 var1 var9 var8 var7 var2))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr)) (or (not (inv_main12 var3 var4 var0 var2 var1 var6 var5)) (inv_main18 (write var3 var5 (O_node (node var1 (next (getnode (read var3 var5))) (prev (getnode (read var3 var5)))))) var4 var0 var2 var1 var6 var5))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr)) (not (and (inv_main12 var3 var4 var0 var2 var1 var6 var5) (not (is-O_node (read var3 var5)))))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr)) (not (and (inv_main18 var3 var4 var0 var2 var1 var6 var5) (not (is-O_node (read var3 var5)))))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr)) (not (and (inv_main19 var3 var4 var0 var2 var1 var6 var5) (not (is-O_node (read var3 var5)))))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr)) (not (and (inv_main22 var3 var4 var0 var2 var1 var6 var5) (not (is-O_node (read var3 var6)))))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Heap) (var5 Int) (var6 Addr) (var7 Int) (var8 Int)) (not (and (inv_main34 var4 var5 var1 var3 var7 var8 var2 var0 var6) (not (is-O_node (read var4 var6)))))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Heap) (var5 Int) (var6 Addr) (var7 Int) (var8 Int)) (not (and (inv_main40 var4 var5 var1 var3 var7 var8 var2 var0 var6) (not (is-O_node (read var4 var6)))))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Heap) (var5 Int) (var6 Addr) (var7 Int) (var8 Int)) (not (and (inv_main41 var4 var5 var1 var3 var7 var8 var2 var0 var6) (not (is-O_node (read var4 var6)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Addr) (var4 Heap) (var5 Int) (var6 Int) (var7 Addr) (var8 Addr) (var9 Int)) (not (and (inv_main48 var4 var5 var1 var3 var6 var9 var2 var0 var7 var8) (not (is-O_node (read var4 var8)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Addr) (var4 Heap) (var5 Int) (var6 Int) (var7 Addr) (var8 Addr) (var9 Int)) (not (and (inv_main51 var4 var5 var1 var3 var6 var9 var2 var0 var7 var8) (not (is-O_node (read var4 var7)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Addr) (var4 Heap) (var5 Int) (var6 Int) (var7 Addr) (var8 Addr) (var9 Int)) (not (and (inv_main53 var4 var5 var1 var3 var6 var9 var2 var0 var7 var8) (not (is-O_node (read var4 var0)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Addr) (var4 Heap) (var5 Int) (var6 Int) (var7 Addr) (var8 Addr) (var9 Int)) (not (and (inv_main54 var4 var5 var1 var3 var6 var9 var2 var0 var7 var8) (not (is-O_node (read var4 var0)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Addr) (var4 Heap) (var5 Int) (var6 Int) (var7 Addr) (var8 Addr) (var9 Int)) (not (and (inv_main56 var4 var5 var1 var3 var6 var9 var2 var0 var7 var8) (not (is-O_node (read var4 var8)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Addr) (var4 Heap) (var5 Int) (var6 Int) (var7 Addr) (var8 Addr) (var9 Int)) (not (and (inv_main52 var4 var5 var1 var3 var6 var9 var2 var0 var7 var8) (not (is-O_node (read var4 var0)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Addr) (var4 Heap) (var5 Int) (var6 Int) (var7 Addr) (var8 Addr) (var9 Int)) (not (and (inv_main60 var4 var5 var1 var3 var6 var9 var2 var0 var7 var8) (not (is-O_node (read var4 var3)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Int) (var4 Addr) (var5 Int)) (not (and (inv_main65 var2 var3 var0 var1 var4 var5) (not (is-O_node (read var2 var4)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Int) (var4 Addr) (var5 Int) (var6 Addr)) (not (and (inv_main66 var2 var3 var0 var1 var4 var5 var6) (not (is-O_node (read var2 var4)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Int) (var4 Addr) (var5 Addr) (var6 Int)) (not (and (inv_main78 var2 var3 var0 var1 var5 var6 var4) (not (is-O_node (read var2 var4)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Int) (var4 Addr) (var5 Int)) (not (inv_main81 var2 var3 var0 var1 var4 var5))))
(check-sat)
