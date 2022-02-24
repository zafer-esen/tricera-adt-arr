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
                   ((node (data Int) (next Addr) (prev Addr)))))
(declare-datatypes ((AllocResHeap 0) (Heap 0))
                   (((AllocResHeap   (newHeap Heap) (newAddr Addr)))
                    ((HeapCtor (HeapSize Int)
                               (HeapContents (Array Addr HeapObject))))))
(define-fun nullAddr  () Addr 0)
(define-fun defHeapObject    () HeapObject defObj)
(define-fun valid     ((h Heap) (p Addr)) Bool
  (and (>= (HeapSize h) p) (> p 0)))
(define-fun emptyHeap () Heap (
  HeapCtor 0 (( as const (Array Addr HeapObject)) defHeapObject)))
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

;===============================================================================
(declare-fun inv_main15 (Heap Int Int Int Int Addr Int Addr) Bool)
(declare-fun inv_main18 (Heap Int Int Int Int Addr Int Addr Int) Bool)
(declare-fun inv_main21 (Heap Int Int Int Int Addr Int Addr) Bool)
(declare-fun inv_main22 (Heap Int Int Int Int Addr Int Addr) Bool)
(declare-fun inv_main24 (Heap Int Int Int Int Addr Addr) Bool)
(declare-fun inv_main25 (Heap Int Int Int Int Addr Addr) Bool)
(declare-fun inv_main28 (Heap Int Int Int Int Addr Addr) Bool)
(declare-fun inv_main4 (Heap Int Int) Bool)
(declare-fun inv_main40 (Heap Int Int Addr Int Int Int Addr) Bool)
(declare-fun inv_main43 (Heap Int Int Addr Int Int Int Addr Int) Bool)
(declare-fun inv_main46 (Heap Int Int Addr Int Int Int Addr) Bool)
(declare-fun inv_main47 (Heap Int Int Addr Int Int Int Addr) Bool)
(declare-fun inv_main52 (Heap Int Int Addr Int Int Addr Addr) Bool)
(declare-fun inv_main53 (Heap Int Int Addr Int Int Addr Addr) Bool)
(declare-fun inv_main54 (Heap Int Int Addr Int Int Addr Addr) Bool)
(declare-fun inv_main56 (Heap Int Int Addr Int Int Addr Addr) Bool)
(declare-fun inv_main58 (Heap Int Int Addr Addr Int) Bool)
(declare-fun inv_main60 (Heap Int Int Addr Addr Int) Bool)
(declare-fun inv_main61 (Heap Int Int Addr Addr Int) Bool)
(declare-fun inv_main73 (Heap Int Int Addr Addr Int Addr) Bool)
(declare-fun inv_main76 (Heap Int Int Addr Addr Int) Bool)
(declare-fun inv_main8 (Heap Int Int Int Int Addr) Bool)
(assert (forall ((var0 Heap)) (or (not (= var0 emptyHeap)) (inv_main4 var0 2 1))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Addr) (var7 Addr) (var8 Int) (var9 Heap) (var10 node) (var11 Int) (var12 Addr) (var13 Int) (var14 Int)) (or (not (and (inv_main8 var9 var8 var3 var13 var11 var12) (and (and (not (= nullAddr var6)) (and (and (and (and (and (and (and (= var0 (newHeap (alloc var9 (O_node var10)))) (= var2 var8)) (= var5 var3)) (= var7 var12)) (= var1 3)) (= var4 var3)) (= var14 var3)) (= var6 (newAddr (alloc var9 (O_node var10)))))) (not (<= 0 (+ var13 (- 1))))))) (inv_main40 var0 var2 var5 var7 var1 var4 var14 var6))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Addr) (var6 Int) (var7 Int) (var8 Int)) (or (not (inv_main18 var0 var7 var3 var6 var4 var5 var8 var1 var2)) (inv_main18 var0 var7 var3 var6 var4 var5 var8 var1 var2))))
(assert (forall ((var0 Int) (var1 Addr) (var2 node) (var3 Int) (var4 Addr) (var5 Int) (var6 Int) (var7 Heap) (var8 Int) (var9 Int) (var10 Int) (var11 Int) (var12 Addr) (var13 Int) (var14 Heap)) (or (not (and (inv_main8 var7 var5 var3 var13 var11 var12) (and (and (= nullAddr var1) (and (and (and (and (and (and (and (= var14 (newHeap (alloc var7 (O_node var2)))) (= var9 var5)) (= var8 var3)) (= var6 var13)) (= var10 var11)) (= var4 var12)) (= var0 var11)) (= var1 (newAddr (alloc var7 (O_node var2)))))) (<= 0 (+ var13 (- 1)))))) (inv_main18 var14 var9 var8 var6 var10 var4 var0 var1 1))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Addr) (var3 Int) (var4 Addr) (var5 Int)) (or (not (and (inv_main58 var0 var5 var3 var2 var4 var1) (not (= var4 nullAddr)))) (inv_main60 var0 var5 var3 var2 var4 var1))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Int) (var3 Int) (var4 Addr) (var5 Int) (var6 Int) (var7 Int)) (or (not (inv_main15 var0 var6 var2 var5 var3 var4 var7 var1)) (inv_main21 (write var0 var1 (O_node (node (data (getnode (read var0 var1))) nullAddr (prev (getnode (read var0 var1)))))) var6 var2 var5 var3 var4 var7 var1))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Addr) (var3 Int) (var4 Addr) (var5 Int)) (or (not (and (inv_main60 var0 var5 var3 var2 var4 var1) (not (= var3 (data (getnode (read var0 var4))))))) (inv_main76 var0 var5 var3 var2 var4 var1))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Addr) (var3 Int) (var4 Addr) (var5 Int)) (or (not (and (inv_main58 var0 var5 var3 var2 var4 var1) (and (not (= var1 (+ 1 var5))) (= var4 nullAddr)))) (inv_main76 var0 var5 var3 var2 var4 var1))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Addr) (var3 Int) (var4 Addr) (var5 Int) (var6 Int) (var7 Addr)) (or (not (inv_main53 var0 var5 var3 var2 var1 var6 var7 var4)) (inv_main56 (write var0 var4 (O_node (node (data (getnode (read var0 var4))) var7 (prev (getnode (read var0 var4)))))) var5 var3 var2 var1 var6 var7 var4))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Int) (var6 Addr) (var7 Int) (var8 Int) (var9 Int) (var10 Int) (var11 Addr) (var12 Addr)) (or (not (and (inv_main61 var0 var9 var5 var4 var6 var1) (and (and (and (and (and (and (= var2 var0) (= var10 var9)) (= var8 var5)) (= var12 var4)) (= var3 var6)) (= var7 var1)) (= var11 (next (getnode (read var0 var6))))))) (inv_main58 var2 var10 var8 var12 var11 (+ var7 1)))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Int) (var4 Addr) (var5 Int) (var6 Heap) (var7 Int) (var8 Heap) (var9 Int) (var10 Addr) (var11 Int) (var12 Int) (var13 Addr)) (or (not (and (inv_main56 var8 var5 var3 var10 var9 var11 var13 var4) (and (and (and (and (and (= var6 (write var8 var13 (O_node (node (data (getnode (read var8 var13))) (next (getnode (read var8 var13))) var4)))) (= var12 var5)) (= var1 var3)) (= var2 var10)) (= var7 var9)) (= var0 var11)))) (inv_main58 var6 var12 var1 var2 var2 0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Addr) (var8 Heap) (var9 Int) (var10 Addr) (var11 Int) (var12 Int) (var13 Heap) (var14 Int) (var15 Addr)) (or (not (and (inv_main47 var8 var4 var2 var10 var9 var14 var11 var7) (and (= nullAddr var15) (and (and (and (and (and (and (and (= var13 (write var8 var7 (O_node (node var11 (next (getnode (read var8 var7))) (prev (getnode (read var8 var7))))))) (= var12 var4)) (= var0 var2)) (= var15 var10)) (= var6 var9)) (= var3 var14)) (= var5 var11)) (= var1 var7))))) (inv_main58 var13 var12 var0 var1 var1 0))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Addr) (var3 Int) (var4 Addr) (var5 Int) (var6 Int) (var7 Addr)) (or (not (and (inv_main52 var0 var5 var3 var2 var1 var6 var7 var4) (= (next (getnode (read var0 var4))) nullAddr))) (inv_main53 var0 var5 var3 var2 var1 var6 var7 var4))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Addr)) (or (not (inv_main40 var0 var5 var3 var2 var1 var6 var4 var7)) (inv_main46 (write var0 var7 (O_node (node (data (getnode (read var0 var7))) nullAddr (prev (getnode (read var0 var7)))))) var5 var3 var2 var1 var6 var4 var7))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Int) (var3 Int) (var4 Addr) (var5 Int) (var6 Int) (var7 Int)) (or (not (inv_main21 var0 var6 var2 var5 var3 var4 var7 var1)) (inv_main22 (write var0 var1 (O_node (node (data (getnode (read var0 var1))) (next (getnode (read var0 var1))) nullAddr))) var6 var2 var5 var3 var4 var7 var1))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Addr)) (or (not (inv_main46 var0 var5 var3 var2 var1 var6 var4 var7)) (inv_main47 (write var0 var7 (O_node (node (data (getnode (read var0 var7))) (next (getnode (read var0 var7))) nullAddr))) var5 var3 var2 var1 var6 var4 var7))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Int) (var3 Addr) (var4 Int) (var5 Addr) (var6 Int) (var7 Int) (var8 Addr) (var9 Int) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Heap) (var15 Int) (var16 Int) (var17 Heap) (var18 Addr) (var19 Addr) (var20 Int) (var21 Int) (var22 Addr)) (or (not (and (inv_main73 var14 var7 var4 var18 var5 var15 var10) (and (not (= var13 nullAddr)) (and (and (and (and (and (and (and (and (= var17 var14) (= var2 var7)) (= var6 var4)) (= var22 var18)) (= var19 var5)) (= var21 var15)) (= var8 var10)) (= var12 (next (getnode (read var14 var10))))) (and (and (and (and (and (and (and (= var0 (write var17 var8 defObj)) (= var20 var2)) (= var9 var6)) (= var3 var22)) (= var1 var19)) (= var16 var21)) (= var11 var8)) (= var13 var12)))))) (inv_main73 var0 var20 var9 var3 var1 var16 var13))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Addr) (var3 Int) (var4 Addr) (var5 Int)) (or (not (and (inv_main58 var0 var5 var3 var2 var4 var1) (and (not (= var2 nullAddr)) (and (= var1 (+ 1 var5)) (= var4 nullAddr))))) (inv_main73 var0 var5 var3 var2 var4 var1 var2))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Addr) (var5 Int) (var6 Int) (var7 Heap) (var8 Int) (var9 Int) (var10 Addr) (var11 Int) (var12 Addr) (var13 Heap)) (or (not (and (inv_main25 var7 var5 var2 var11 var9 var10 var4) (and (not (= var12 nullAddr)) (and (and (and (and (and (and (= var13 (write var7 var4 (O_node (node (data (getnode (read var7 var4))) var10 (prev (getnode (read var7 var4))))))) (= var8 var5)) (= var3 var2)) (= var6 var11)) (= var0 var9)) (= var12 var10)) (= var1 var4))))) (inv_main28 var13 var8 var3 var6 var0 var12 var1))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Addr) (var3 Int) (var4 Addr) (var5 Int)) (or (not (and (inv_main60 var0 var5 var3 var2 var4 var1) (= var3 (data (getnode (read var0 var4)))))) (inv_main61 var0 var5 var3 var2 var4 var1))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Int) (var3 Addr) (var4 Int) (var5 Int) (var6 Int) (var7 Int) (var8 Addr)) (or (not (inv_main43 var0 var6 var4 var3 var1 var7 var5 var8 var2)) (inv_main43 var0 var6 var4 var3 var1 var7 var5 var8 var2))))
(assert (forall ((var0 node) (var1 Int) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Heap) (var8 Addr) (var9 Heap) (var10 Int) (var11 Addr) (var12 Int) (var13 Addr) (var14 Int)) (or (not (and (inv_main8 var7 var5 var3 var12 var10 var11) (and (and (= nullAddr var8) (and (and (and (and (and (and (and (= var9 (newHeap (alloc var7 (O_node var0)))) (= var14 var5)) (= var4 var3)) (= var13 var11)) (= var2 3)) (= var1 var3)) (= var6 var3)) (= var8 (newAddr (alloc var7 (O_node var0)))))) (not (<= 0 (+ var12 (- 1))))))) (inv_main43 var9 var14 var4 var13 var2 var1 var6 var8 1))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Addr) (var3 Int) (var4 Addr) (var5 Int) (var6 Int) (var7 Addr)) (or (not (and (inv_main52 var0 var5 var3 var2 var1 var6 var7 var4) (not (= (next (getnode (read var0 var4))) nullAddr)))) (inv_main54 var0 var5 var3 var2 var1 var6 var7 var4))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Int) (var5 Int) (var6 node) (var7 Addr) (var8 Int) (var9 Int) (var10 Heap) (var11 Heap) (var12 Int) (var13 Addr) (var14 Int)) (or (not (and (inv_main8 var10 var8 var4 var14 var12 var13) (and (and (not (= nullAddr var7)) (and (and (and (and (and (and (and (= var11 (newHeap (alloc var10 (O_node var6)))) (= var1 var8)) (= var9 var4)) (= var5 var14)) (= var0 var12)) (= var3 var13)) (= var2 var12)) (= var7 (newAddr (alloc var10 (O_node var6)))))) (<= 0 (+ var14 (- 1)))))) (inv_main15 var11 var1 var9 var5 var0 var3 var2 var7))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Heap) (var8 Int) (var9 Int) (var10 Addr) (var11 Int) (var12 Int) (var13 Addr) (var14 Int) (var15 Heap)) (or (not (and (inv_main22 var7 var5 var3 var11 var9 var10 var14 var1) (and (and (and (and (and (and (and (= var15 (write var7 var1 (O_node (node var14 (next (getnode (read var7 var1))) (prev (getnode (read var7 var1))))))) (= var8 var5)) (= var12 var3)) (= var6 var11)) (= var4 var9)) (= var2 var10)) (= var0 var14)) (= var13 var1)))) (inv_main24 var15 var8 var12 var6 var4 var2 var13))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Addr) (var4 Int) (var5 Int) (var6 Int) (var7 Addr) (var8 Int) (var9 Heap) (var10 Int) (var11 Int) (var12 Addr) (var13 Int)) (or (not (and (inv_main28 var9 var5 var2 var13 var11 var12 var3) (and (and (and (and (and (and (= var1 (write var9 var12 (O_node (node (data (getnode (read var9 var12))) (next (getnode (read var9 var12))) var3)))) (= var10 var5)) (= var4 var2)) (= var8 var13)) (= var6 var11)) (= var0 var12)) (= var7 var3)))) (inv_main8 var1 var10 var4 (+ var8 (- 1)) var6 var7))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap) (var4 Addr) (var5 Int) (var6 Int) (var7 Int) (var8 Heap) (var9 Int) (var10 Int) (var11 Addr) (var12 Int) (var13 Int)) (or (not (and (inv_main25 var8 var5 var2 var12 var10 var11 var4) (and (= var0 nullAddr) (and (and (and (and (and (and (= var3 (write var8 var4 (O_node (node (data (getnode (read var8 var4))) var11 (prev (getnode (read var8 var4))))))) (= var6 var5)) (= var9 var2)) (= var13 var12)) (= var7 var10)) (= var0 var11)) (= var1 var4))))) (inv_main8 var3 var6 var9 (+ var13 (- 1)) var7 var1))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Int)) (or (not (inv_main4 var0 var2 var1)) (inv_main8 var0 var2 var1 var2 var1 nullAddr))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Addr) (var7 Int) (var8 Addr) (var9 Heap) (var10 Int) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Int) (var15 Int) (var16 Addr)) (or (not (and (inv_main54 var9 var7 var3 var12 var10 var15 var16 var6) (and (and (and (and (and (and (and (and (= var0 var9) (= var2 var7)) (= var14 var3)) (= var8 var12)) (= var5 var10)) (= var4 var15)) (= var13 var16)) (= var11 var6)) (= var1 (next (getnode (read var9 var6))))))) (inv_main52 var0 var2 var14 var8 var5 var4 var13 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Addr) (var8 Heap) (var9 Int) (var10 Addr) (var11 Int) (var12 Int) (var13 Heap) (var14 Int) (var15 Addr)) (or (not (and (inv_main47 var8 var4 var2 var10 var9 var14 var11 var7) (and (not (= nullAddr var15)) (and (and (and (and (and (and (and (= var13 (write var8 var7 (O_node (node var11 (next (getnode (read var8 var7))) (prev (getnode (read var8 var7))))))) (= var12 var4)) (= var0 var2)) (= var15 var10)) (= var6 var9)) (= var3 var14)) (= var5 var11)) (= var1 var7))))) (inv_main52 var13 var12 var0 var15 var6 var3 var1 var15))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Addr) (var3 Int) (var4 Addr) (var5 Int) (var6 Int)) (or (not (inv_main24 var0 var6 var1 var5 var3 var4 var2)) (inv_main25 (write var0 var2 (O_node (node var3 (next (getnode (read var0 var2))) (prev (getnode (read var0 var2)))))) var6 var1 var5 var3 var4 var2))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Int) (var3 Int) (var4 Addr) (var5 Int) (var6 Int) (var7 Int)) (not (and (inv_main15 var0 var6 var2 var5 var3 var4 var7 var1) (not (is-O_node (read var0 var1)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Int) (var3 Int) (var4 Addr) (var5 Int) (var6 Int) (var7 Int)) (not (and (inv_main21 var0 var6 var2 var5 var3 var4 var7 var1) (not (is-O_node (read var0 var1)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Int) (var3 Int) (var4 Addr) (var5 Int) (var6 Int) (var7 Int)) (not (and (inv_main22 var0 var6 var2 var5 var3 var4 var7 var1) (not (is-O_node (read var0 var1)))))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Addr) (var3 Int) (var4 Addr) (var5 Int) (var6 Int)) (not (and (inv_main24 var0 var6 var1 var5 var3 var4 var2) (not (is-O_node (read var0 var2)))))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Addr) (var3 Int) (var4 Addr) (var5 Int) (var6 Int)) (not (and (inv_main25 var0 var6 var1 var5 var3 var4 var2) (not (is-O_node (read var0 var2)))))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Addr) (var3 Int) (var4 Addr) (var5 Int) (var6 Int)) (not (and (inv_main28 var0 var6 var1 var5 var3 var4 var2) (not (is-O_node (read var0 var4)))))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Addr)) (not (and (inv_main40 var0 var5 var3 var2 var1 var6 var4 var7) (not (is-O_node (read var0 var7)))))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Addr)) (not (and (inv_main46 var0 var5 var3 var2 var1 var6 var4 var7) (not (is-O_node (read var0 var7)))))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Addr)) (not (and (inv_main47 var0 var5 var3 var2 var1 var6 var4 var7) (not (is-O_node (read var0 var7)))))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Addr) (var3 Int) (var4 Addr) (var5 Int) (var6 Int) (var7 Addr)) (not (and (inv_main52 var0 var5 var3 var2 var1 var6 var7 var4) (not (is-O_node (read var0 var4)))))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Addr) (var3 Int) (var4 Addr) (var5 Int) (var6 Int) (var7 Addr)) (not (and (inv_main54 var0 var5 var3 var2 var1 var6 var7 var4) (not (is-O_node (read var0 var4)))))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Addr) (var3 Int) (var4 Addr) (var5 Int) (var6 Int) (var7 Addr)) (not (and (inv_main53 var0 var5 var3 var2 var1 var6 var7 var4) (not (is-O_node (read var0 var4)))))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Addr) (var3 Int) (var4 Addr) (var5 Int) (var6 Int) (var7 Addr)) (not (and (inv_main56 var0 var5 var3 var2 var1 var6 var7 var4) (not (is-O_node (read var0 var7)))))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Addr) (var3 Int) (var4 Addr) (var5 Int)) (not (and (inv_main60 var0 var5 var3 var2 var4 var1) (not (is-O_node (read var0 var4)))))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Addr) (var3 Int) (var4 Addr) (var5 Int)) (not (and (inv_main61 var0 var5 var3 var2 var4 var1) (not (is-O_node (read var0 var4)))))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Addr) (var3 Int) (var4 Addr) (var5 Int) (var6 Addr)) (not (and (inv_main73 var0 var5 var3 var2 var4 var1 var6) (not (is-O_node (read var0 var6)))))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Addr) (var3 Int) (var4 Addr) (var5 Int)) (not (inv_main76 var0 var5 var3 var2 var4 var1))))
(check-sat)
