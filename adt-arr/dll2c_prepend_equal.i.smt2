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
                   ((node (next Addr) (prev Addr) (data Int)))))
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
(declare-fun inv_main19 (Heap Int Int Int Int Int Addr) Bool)
(declare-fun inv_main22 (Heap Int Int Int Int Addr Addr) Bool)
(declare-fun inv_main23 (Heap Int Int Int Int Addr Addr) Bool)
(declare-fun inv_main29 (Heap Int Int Int Int Addr Addr Int Addr) Bool)
(declare-fun inv_main32 (Heap Int Int Int Int Addr Addr Int Addr Int) Bool)
(declare-fun inv_main35 (Heap Int Int Int Int Addr Addr Int Addr) Bool)
(declare-fun inv_main36 (Heap Int Int Int Int Addr Addr Int Addr) Bool)
(declare-fun inv_main38 (Heap Int Int Int Int Addr Addr Addr) Bool)
(declare-fun inv_main4 (Heap Int Int) Bool)
(declare-fun inv_main41 (Heap Int Int Int Int Addr Addr Addr) Bool)
(declare-fun inv_main44 (Heap Int Int Int Int Addr Addr) Bool)
(declare-fun inv_main55 (Heap Int Int Addr Int Int Int Addr) Bool)
(declare-fun inv_main58 (Heap Int Int Addr Int Int Int Addr Int) Bool)
(declare-fun inv_main61 (Heap Int Int Addr Int Int Int Addr) Bool)
(declare-fun inv_main62 (Heap Int Int Addr Int Int Int Addr) Bool)
(declare-fun inv_main66 (Heap Int Int Addr Int Int Addr) Bool)
(declare-fun inv_main67 (Heap Int Int Addr Int Int Addr) Bool)
(declare-fun inv_main68 (Heap Int Int Addr Int Int Addr) Bool)
(declare-fun inv_main71 (Heap Int Int Addr Int Int Addr Addr Addr) Bool)
(declare-fun inv_main72 (Heap Int Int Addr Int Int Addr Addr Addr) Bool)
(declare-fun inv_main73 (Heap Int Int Addr Int Int Addr Addr Addr) Bool)
(declare-fun inv_main74 (Heap Int Int Addr Int Int Addr Addr Addr) Bool)
(declare-fun inv_main76 (Heap Int Int Addr Addr Int) Bool)
(declare-fun inv_main79 (Heap Int Int Addr Addr Int) Bool)
(declare-fun inv_main91 (Heap Int Int Addr Addr Int Addr) Bool)
(declare-fun inv_main95 (Heap Int Int Addr Addr Int Addr Addr) Bool)
(declare-fun inv_main98 (Heap Int Int Addr Addr Int) Bool)
(assert (forall ((var0 Heap)) (or (not (= var0 emptyHeap)) (inv_main4 var0 2 1))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Int) (var4 Addr) (var5 Int) (var6 Int)) (or (not (inv_main23 var1 var2 var3 var6 var5 var4 var0)) (inv_main44 (write var1 var0 (O_node (node var4 (prev (getnode (read var1 var0))) (data (getnode (read var1 var0)))))) var2 var3 var6 var5 var4 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Int) (var4 Addr) (var5 Heap) (var6 Int) (var7 Int)) (or (not (inv_main61 var5 var6 var7 var0 var1 var2 var3 var4)) (inv_main62 (write var5 var4 (O_node (node (next (getnode (read var5 var4))) nullAddr (data (getnode (read var5 var4)))))) var6 var7 var0 var1 var2 var3 var4))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Int) (var7 Int) (var8 Addr) (var9 Int) (var10 Int) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Int)) (or (not (and (inv_main91 var4 var10 var14 var8 var5 var9 var13) (and (not (= var2 var12)) (and (and (and (and (and (and (and (= var0 var4) (= var1 var10)) (= var6 var14)) (= var3 var8)) (= var11 var5)) (= var7 var9)) (= var12 var13)) (= var2 (next (getnode (read var4 var13)))))))) (inv_main95 var0 var1 var6 var3 var11 var7 var12 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Addr) (var5 Int) (var6 Int) (var7 Addr) (var8 Heap) (var9 Addr) (var10 Heap) (var11 Heap) (var12 Addr) (var13 Int) (var14 Addr) (var15 Int) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Int) (var22 Int) (var23 Int) (var24 Addr) (var25 Int)) (or (not (and (inv_main95 var8 var22 var25 var14 var9 var21 var24 var12) (and (not (= var1 var0)) (and (and (and (and (and (and (and (and (and (= var10 var8) (= var6 var22)) (= var23 var25)) (= var18 var14)) (= var20 var9)) (= var15 var21)) (= var2 var24)) (= var4 var12)) (= var19 (next (getnode (read var8 var12))))) (and (and (and (and (and (and (and (and (= var11 (write var10 var4 defObj)) (= var5 var6)) (= var3 var23)) (= var17 var18)) (= var16 var20)) (= var13 var15)) (= var0 var2)) (= var7 var4)) (= var1 var19)))))) (inv_main95 var11 var5 var3 var17 var16 var13 var0 var1))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Int) (var7 Int) (var8 Addr) (var9 node) (var10 Int) (var11 Addr) (var12 Int) (var13 Heap) (var14 Int) (var15 Int) (var16 Int)) (or (not (and (inv_main22 var3 var14 var15 var7 var6 var5 var2) (and (and (not (= nullAddr var11)) (and (and (and (and (and (and (and (and (= var13 (newHeap (alloc var3 (O_node var9)))) (= var16 var14)) (= var0 var15)) (= var12 var7)) (= var1 var6)) (= var8 var5)) (= var4 var2)) (= var10 var6)) (= var11 (newAddr (alloc var3 (O_node var9)))))) (<= 0 (+ (+ var7 (- 1)) (- 1)))))) (inv_main29 var13 var16 var0 var12 var1 var8 var4 var10 var11))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Int) (var4 Addr) (var5 Int) (var6 Heap) (var7 Int) (var8 Int)) (or (not (inv_main58 var6 var7 var8 var0 var1 var2 var3 var4 var5)) (inv_main58 var6 var7 var8 var0 var1 var2 var3 var4 var5))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Addr) (var4 Addr) (var5 Int) (var6 Heap) (var7 Addr) (var8 Int) (var9 Addr) (var10 Int) (var11 Int) (var12 Int) (var13 Int) (var14 Heap) (var15 Addr) (var16 Int) (var17 Int) (var18 Int) (var19 Int) (var20 Int) (var21 node) (var22 Int)) (or (not (and (inv_main44 var6 var19 var22 var11 var10 var9 var4) (and (and (= nullAddr var3) (and (and (and (and (and (and (and (= var14 (newHeap (alloc var1 (O_node var21)))) (= var20 var2)) (= var5 var17)) (= var7 var15)) (= var16 3)) (= var8 var17)) (= var13 var17)) (= var3 (newAddr (alloc var1 (O_node var21)))))) (and (and (and (and (and (and (= var1 (write var6 var9 (O_node (node (next (getnode (read var6 var9))) var4 (data (getnode (read var6 var9))))))) (= var2 var19)) (= var17 var22)) (= var18 var11)) (= var12 var10)) (= var15 var9)) (= var0 var4))))) (inv_main58 var14 var20 var5 var7 var16 var8 var13 var3 1))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Int)) (or (not (inv_main12 var1 var2 var4 var6 var5 var3 var0)) (inv_main18 (write var1 var0 (O_node (node nullAddr (prev (getnode (read var1 var0))) (data (getnode (read var1 var0)))))) var2 var4 var6 var5 var3 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Int) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Int) (var9 Addr) (var10 Addr) (var11 Int) (var12 Int) (var13 Int) (var14 Int) (var15 Int)) (or (not (and (inv_main41 var6 var14 var15 var12 var11 var10 var4 var7) (and (and (and (and (and (and (and (= var2 (write var6 var10 (O_node (node (next (getnode (read var6 var10))) var7 (data (getnode (read var6 var10))))))) (= var0 var14)) (= var3 var15)) (= var13 var12)) (= var8 var11)) (= var9 var10)) (= var5 var4)) (= var1 var7)))) (inv_main22 var2 var0 var3 (+ var13 (- 1)) var8 var1 var5))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Int) (var7 Int) (var8 Addr) (var9 Int) (var10 Addr) (var11 Int) (var12 Addr) (var13 Int) (var14 Int) (var15 Int)) (or (not (and (inv_main38 var3 var13 var15 var7 var6 var5 var2 var4) (and (= var10 nullAddr) (and (and (and (and (and (and (and (= var0 (write var3 var4 (O_node (node var5 (prev (getnode (read var3 var4))) (data (getnode (read var3 var4))))))) (= var14 var13)) (= var11 var15)) (= var1 var7)) (= var9 var6)) (= var10 var5)) (= var8 var2)) (= var12 var4))))) (inv_main22 var0 var14 var11 (+ var1 (- 1)) var9 var12 var8))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Heap) (var4 Int) (var5 Int) (var6 Int) (var7 Int) (var8 Int) (var9 Addr) (var10 Addr) (var11 Int) (var12 Heap) (var13 Int)) (or (not (and (inv_main19 var3 var11 var13 var7 var6 var5 var9) (and (and (and (and (and (and (= var12 (write var3 var9 (O_node (node (next (getnode (read var3 var9))) (prev (getnode (read var3 var9))) var5)))) (= var0 var11)) (= var1 var13)) (= var8 var7)) (= var4 var6)) (= var2 var5)) (= var10 var9)))) (inv_main22 var12 var0 var1 var8 var4 var10 var10))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Int) (var8 Int)) (or (not (inv_main71 var6 var7 var8 var0 var1 var2 var4 var3 var5)) (inv_main72 (write var6 var4 (O_node (node var5 (prev (getnode (read var6 var4))) (data (getnode (read var6 var4)))))) var7 var8 var0 var1 var2 var4 var3 var5))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Int)) (or (not (inv_main18 var1 var2 var4 var6 var5 var3 var0)) (inv_main19 (write var1 var0 (O_node (node (next (getnode (read var1 var0))) nullAddr (data (getnode (read var1 var0)))))) var2 var4 var6 var5 var3 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Heap) (var5 Int) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Int) (var10 Int) (var11 Int) (var12 Addr)) (or (not (and (inv_main79 var7 var10 var11 var0 var8 var9) (and (not (= var6 var12)) (and (and (and (and (and (and (= var4 var7) (= var5 var10)) (= var3 var11)) (= var12 var0)) (= var1 var8)) (= var2 var9)) (= var6 (next (getnode (read var7 var8)))))))) (inv_main76 var4 var5 var3 var12 var6 (+ var2 1)))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Int) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Int) (var8 Int) (var9 Heap) (var10 Int) (var11 Int) (var12 Int)) (or (not (and (inv_main68 var6 var8 var10 var0 var1 var2 var4) (and (and (and (and (and (= var9 (write var6 var4 (O_node (node (next (getnode (read var6 var4))) var4 (data (getnode (read var6 var4))))))) (= var11 var8)) (= var3 var10)) (= var5 var0)) (= var12 var1)) (= var7 var2)))) (inv_main76 var9 var11 var3 var5 var5 0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Int) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Int) (var9 Heap) (var10 Int) (var11 Addr) (var12 Addr) (var13 Int) (var14 Int)) (or (not (and (inv_main74 var9 var13 var14 var11 var1 var2 var5 var12 var7) (and (and (and (and (and (= var4 (write var9 var5 (O_node (node (next (getnode (read var9 var5))) var12 (data (getnode (read var9 var5))))))) (= var8 var13)) (= var3 var14)) (= var6 var11)) (= var0 var1)) (= var10 var2)))) (inv_main76 var4 var8 var3 var6 var6 0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Int) (var8 Int)) (or (not (inv_main73 var6 var7 var8 var0 var1 var2 var4 var3 var5)) (inv_main74 (write var6 var3 (O_node (node var4 (prev (getnode (read var6 var3))) (data (getnode (read var6 var3)))))) var7 var8 var0 var1 var2 var4 var3 var5))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Heap) (var4 Heap) (var5 Int) (var6 Addr) (var7 Int) (var8 Int) (var9 Addr) (var10 Int) (var11 Addr) (var12 Int) (var13 Addr) (var14 Int) (var15 Int)) (or (not (and (inv_main62 var4 var14 var15 var9 var1 var2 var10 var13) (and (= nullAddr var11) (and (and (and (and (and (and (and (= var3 (write var4 var13 (O_node (node (next (getnode (read var4 var13))) (prev (getnode (read var4 var13))) var10)))) (= var12 var14)) (= var0 var15)) (= var11 var9)) (= var5 var1)) (= var8 var2)) (= var7 var10)) (= var6 var13))))) (inv_main67 var3 var12 var0 var6 var5 var8 var6))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Int) (var3 Int) (var4 Addr) (var5 Heap) (var6 Int) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Int) (var11 Addr) (var12 Int) (var13 Int) (var14 Int)) (or (not (and (inv_main66 var5 var13 var14 var7 var1 var2 var4) (and (and (and (and (and (and (and (= var0 var5) (= var3 var13)) (= var10 var14)) (= var8 var7)) (= var12 var1)) (= var6 var2)) (= var11 var4)) (= var9 (prev (getnode (read var5 var7))))))) (inv_main71 var0 var3 var10 var11 var12 var6 var11 var9 var8))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Addr) (var4 Heap) (var5 Int) (var6 Int) (var7 Addr) (var8 Int) (var9 Int)) (or (not (inv_main32 var4 var5 var6 var9 var8 var7 var3 var2 var0 var1)) (inv_main32 var4 var5 var6 var9 var8 var7 var3 var2 var0 var1))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap) (var6 Int) (var7 Addr) (var8 Heap) (var9 node) (var10 Addr) (var11 Int) (var12 Int) (var13 Addr) (var14 Int) (var15 Int) (var16 Int)) (or (not (and (inv_main22 var5 var15 var16 var12 var11 var10 var2) (and (and (= nullAddr var13) (and (and (and (and (and (and (and (and (= var8 (newHeap (alloc var5 (O_node var9)))) (= var0 var15)) (= var14 var16)) (= var6 var12)) (= var1 var11)) (= var3 var10)) (= var7 var2)) (= var4 var11)) (= var13 (newAddr (alloc var5 (O_node var9)))))) (<= 0 (+ (+ var12 (- 1)) (- 1)))))) (inv_main32 var8 var0 var14 var6 var1 var3 var7 var4 var13 1))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Int) (var4 Addr) (var5 Int) (var6 Int)) (or (not (and (inv_main22 var1 var2 var3 var6 var5 var4 var0) (not (<= 0 (+ (+ var6 (- 1)) (- 1)))))) (inv_main23 var1 var2 var3 var6 var5 var4 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Int) (var8 Int)) (or (not (inv_main72 var6 var7 var8 var0 var1 var2 var4 var3 var5)) (inv_main73 (write var6 var5 (O_node (node (next (getnode (read var6 var5))) var4 (data (getnode (read var6 var5)))))) var7 var8 var0 var1 var2 var4 var3 var5))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Int) (var7 Addr) (var8 Int) (var9 Int) (var10 Addr) (var11 Int) (var12 Int) (var13 Int) (var14 Int) (var15 Heap) (var16 Int) (var17 Int)) (or (not (and (inv_main36 var3 var14 var17 var9 var8 var7 var2 var12 var10) (and (and (and (and (and (and (and (and (= var15 (write var3 var10 (O_node (node (next (getnode (read var3 var10))) (prev (getnode (read var3 var10))) var12)))) (= var13 var14)) (= var0 var17)) (= var16 var9)) (= var6 var8)) (= var4 var7)) (= var1 var2)) (= var11 var12)) (= var5 var10)))) (inv_main38 var15 var13 var0 var16 var6 var4 var1 var5))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Int)) (or (not (inv_main15 var2 var3 var5 var7 var6 var4 var1 var0)) (inv_main15 var2 var3 var5 var7 var6 var4 var1 var0))))
(assert (forall ((var0 Int) (var1 node) (var2 Int) (var3 Heap) (var4 Heap) (var5 Int) (var6 Int) (var7 Int) (var8 Addr) (var9 Int) (var10 Int)) (or (not (and (inv_main4 var4 var5 var9) (and (= nullAddr var8) (and (and (and (and (and (and (= var3 (newHeap (alloc var4 (O_node var1)))) (= var6 var5)) (= var2 var9)) (= var10 var5)) (= var0 var9)) (= var7 var9)) (= var8 (newAddr (alloc var4 (O_node var1)))))))) (inv_main15 var3 var6 var2 var10 var0 var7 var8 1))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Addr) (var4 Heap) (var5 Int) (var6 Int)) (or (not (inv_main67 var4 var5 var6 var0 var1 var2 var3)) (inv_main68 (write var4 var3 (O_node (node var3 (prev (getnode (read var4 var3))) (data (getnode (read var4 var3)))))) var5 var6 var0 var1 var2 var3))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Addr) (var4 Int) (var5 Heap) (var6 Int) (var7 Addr) (var8 Int) (var9 Int) (var10 Int) (var11 Addr) (var12 Addr) (var13 Int) (var14 Addr) (var15 Int) (var16 Int) (var17 Int) (var18 Heap) (var19 Int) (var20 Int) (var21 node) (var22 Int)) (or (not (and (inv_main44 var5 var19 var22 var9 var8 var7 var3) (and (and (not (= nullAddr var14)) (and (and (and (and (and (and (and (= var18 (newHeap (alloc var1 (O_node var21)))) (= var17 var2)) (= var13 var16)) (= var11 var12)) (= var6 3)) (= var20 var16)) (= var4 var16)) (= var14 (newAddr (alloc var1 (O_node var21)))))) (and (and (and (and (and (and (= var1 (write var5 var7 (O_node (node (next (getnode (read var5 var7))) var3 (data (getnode (read var5 var7))))))) (= var2 var19)) (= var16 var22)) (= var15 var9)) (= var10 var8)) (= var12 var7)) (= var0 var3))))) (inv_main55 var18 var17 var13 var11 var6 var20 var4 var14))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Heap) (var5 Addr) (var6 Int) (var7 Heap) (var8 Addr) (var9 Int) (var10 Int) (var11 Int) (var12 Addr)) (or (not (and (inv_main79 var7 var10 var11 var0 var8 var9) (and (not (= nullAddr var12)) (and (= (+ var3 1) (+ 1 var6)) (and (= var5 var12) (and (and (and (and (and (and (= var4 var7) (= var6 var10)) (= var2 var11)) (= var12 var0)) (= var1 var8)) (= var3 var9)) (= var5 (next (getnode (read var7 var8)))))))))) (inv_main91 var4 var6 var2 var12 var5 (+ var3 1) var12))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Int) (var4 Int) (var5 Int)) (or (not (and (inv_main76 var1 var4 var5 var0 var2 var3) (= var5 (data (getnode (read var1 var2)))))) (inv_main79 var1 var4 var5 var0 var2 var3))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Heap) (var4 Int) (var5 Int) (var6 Addr) (var7 Int) (var8 Int)) (or (not (inv_main35 var3 var4 var5 var8 var7 var6 var2 var1 var0)) (inv_main36 (write var3 var0 (O_node (node (next (getnode (read var3 var0))) nullAddr (data (getnode (read var3 var0)))))) var4 var5 var8 var7 var6 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Heap) (var4 Heap) (var5 Int) (var6 Addr) (var7 Int) (var8 Int) (var9 Addr) (var10 Int) (var11 Addr) (var12 Int) (var13 Addr) (var14 Int) (var15 Int)) (or (not (and (inv_main62 var4 var14 var15 var9 var1 var2 var10 var13) (and (not (= nullAddr var11)) (and (and (and (and (and (and (and (= var3 (write var4 var13 (O_node (node (next (getnode (read var4 var13))) (prev (getnode (read var4 var13))) var10)))) (= var12 var14)) (= var0 var15)) (= var11 var9)) (= var5 var1)) (= var8 var2)) (= var7 var10)) (= var6 var13))))) (inv_main66 var3 var12 var0 var11 var5 var8 var6))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Int) (var4 Heap) (var5 Addr) (var6 Int) (var7 Addr) (var8 Addr) (var9 Int) (var10 Int) (var11 Int) (var12 Addr) (var13 Int) (var14 Heap) (var15 Int)) (or (not (and (inv_main38 var4 var13 var15 var10 var9 var8 var2 var5) (and (not (= var12 nullAddr)) (and (and (and (and (and (and (and (= var14 (write var4 var5 (O_node (node var8 (prev (getnode (read var4 var5))) (data (getnode (read var4 var5))))))) (= var1 var13)) (= var3 var15)) (= var6 var10)) (= var11 var9)) (= var12 var8)) (= var7 var2)) (= var0 var5))))) (inv_main41 var14 var1 var3 var6 var11 var12 var7 var0))))
(assert (forall ((var0 node) (var1 Int) (var2 Int) (var3 Heap) (var4 Int) (var5 Heap) (var6 Int) (var7 Int) (var8 Int) (var9 Addr) (var10 Int)) (or (not (and (inv_main4 var5 var6 var8) (and (not (= nullAddr var9)) (and (and (and (and (and (and (= var3 (newHeap (alloc var5 (O_node var0)))) (= var10 var6)) (= var7 var8)) (= var1 var6)) (= var4 var8)) (= var2 var8)) (= var9 (newAddr (alloc var5 (O_node var0)))))))) (inv_main12 var3 var10 var7 var1 var4 var2 var9))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Int) (var4 Int) (var5 Int)) (or (not (and (inv_main76 var1 var4 var5 var0 var2 var3) (not (= var5 (data (getnode (read var1 var2))))))) (inv_main98 var1 var4 var5 var0 var2 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Heap) (var5 Addr) (var6 Int) (var7 Heap) (var8 Addr) (var9 Int) (var10 Int) (var11 Int) (var12 Addr)) (or (not (and (inv_main79 var7 var10 var11 var0 var8 var9) (and (not (= (+ var3 1) (+ 1 var6))) (and (= var5 var12) (and (and (and (and (and (and (= var4 var7) (= var6 var10)) (= var2 var11)) (= var12 var0)) (= var1 var8)) (= var3 var9)) (= var5 (next (getnode (read var7 var8))))))))) (inv_main98 var4 var6 var2 var12 var5 (+ var3 1)))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Int) (var4 Addr) (var5 Heap) (var6 Int) (var7 Int)) (or (not (inv_main55 var5 var6 var7 var0 var1 var2 var3 var4)) (inv_main61 (write var5 var4 (O_node (node nullAddr (prev (getnode (read var5 var4))) (data (getnode (read var5 var4)))))) var6 var7 var0 var1 var2 var3 var4))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Heap) (var4 Int) (var5 Int) (var6 Addr) (var7 Int) (var8 Int)) (or (not (inv_main29 var3 var4 var5 var8 var7 var6 var2 var1 var0)) (inv_main35 (write var3 var0 (O_node (node nullAddr (prev (getnode (read var3 var0))) (data (getnode (read var3 var0)))))) var4 var5 var8 var7 var6 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Int)) (not (and (inv_main12 var1 var2 var4 var6 var5 var3 var0) (not (is-O_node (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Int)) (not (and (inv_main18 var1 var2 var4 var6 var5 var3 var0) (not (is-O_node (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Int)) (not (and (inv_main19 var1 var2 var4 var6 var5 var3 var0) (not (is-O_node (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Heap) (var4 Int) (var5 Int) (var6 Addr) (var7 Int) (var8 Int)) (not (and (inv_main29 var3 var4 var5 var8 var7 var6 var2 var1 var0) (not (is-O_node (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Heap) (var4 Int) (var5 Int) (var6 Addr) (var7 Int) (var8 Int)) (not (and (inv_main35 var3 var4 var5 var8 var7 var6 var2 var1 var0) (not (is-O_node (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Heap) (var4 Int) (var5 Int) (var6 Addr) (var7 Int) (var8 Int)) (not (and (inv_main36 var3 var4 var5 var8 var7 var6 var2 var1 var0) (not (is-O_node (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Int) (var4 Int) (var5 Addr) (var6 Int) (var7 Int)) (not (and (inv_main38 var1 var3 var4 var7 var6 var5 var0 var2) (not (is-O_node (read var1 var2)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Int) (var4 Int) (var5 Addr) (var6 Int) (var7 Int)) (not (and (inv_main41 var1 var3 var4 var7 var6 var5 var0 var2) (not (is-O_node (read var1 var5)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Int) (var4 Addr) (var5 Int) (var6 Int)) (not (and (inv_main23 var1 var2 var3 var6 var5 var4 var0) (not (is-O_node (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Int) (var4 Addr) (var5 Int) (var6 Int)) (not (and (inv_main44 var1 var2 var3 var6 var5 var4 var0) (not (is-O_node (read var1 var4)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Int) (var4 Addr) (var5 Heap) (var6 Int) (var7 Int)) (not (and (inv_main55 var5 var6 var7 var0 var1 var2 var3 var4) (not (is-O_node (read var5 var4)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Int) (var4 Addr) (var5 Heap) (var6 Int) (var7 Int)) (not (and (inv_main61 var5 var6 var7 var0 var1 var2 var3 var4) (not (is-O_node (read var5 var4)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Int) (var4 Addr) (var5 Heap) (var6 Int) (var7 Int)) (not (and (inv_main62 var5 var6 var7 var0 var1 var2 var3 var4) (not (is-O_node (read var5 var4)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Addr) (var4 Heap) (var5 Int) (var6 Int)) (not (and (inv_main67 var4 var5 var6 var0 var1 var2 var3) (not (is-O_node (read var4 var3)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Addr) (var4 Heap) (var5 Int) (var6 Int)) (not (and (inv_main68 var4 var5 var6 var0 var1 var2 var3) (not (is-O_node (read var4 var3)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Addr) (var4 Heap) (var5 Int) (var6 Int)) (not (and (inv_main66 var4 var5 var6 var0 var1 var2 var3) (not (is-O_node (read var4 var0)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Int) (var8 Int)) (not (and (inv_main71 var6 var7 var8 var0 var1 var2 var4 var3 var5) (not (is-O_node (read var6 var4)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Int) (var8 Int)) (not (and (inv_main72 var6 var7 var8 var0 var1 var2 var4 var3 var5) (not (is-O_node (read var6 var5)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Int) (var8 Int)) (not (and (inv_main73 var6 var7 var8 var0 var1 var2 var4 var3 var5) (not (is-O_node (read var6 var3)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Int) (var8 Int)) (not (and (inv_main74 var6 var7 var8 var0 var1 var2 var4 var3 var5) (not (is-O_node (read var6 var4)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Int) (var4 Int) (var5 Int)) (not (and (inv_main76 var1 var4 var5 var0 var2 var3) (not (is-O_node (read var1 var2)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Int) (var4 Int) (var5 Int)) (not (and (inv_main79 var1 var4 var5 var0 var2 var3) (not (is-O_node (read var1 var2)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Int) (var4 Int) (var5 Addr) (var6 Int)) (not (and (inv_main91 var1 var4 var6 var0 var2 var3 var5) (not (is-O_node (read var1 var5)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Int) (var4 Int) (var5 Addr) (var6 Int) (var7 Addr)) (not (and (inv_main95 var1 var4 var6 var0 var2 var3 var5 var7) (not (is-O_node (read var1 var7)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Int) (var4 Int) (var5 Int)) (not (inv_main98 var1 var4 var5 var0 var2 var3))))
(check-sat)
