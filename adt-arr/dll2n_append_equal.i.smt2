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
                   (((O_Int (getInt Int)) (O_UInt (getUInt Int)) (O_Addr (getAddr Addr)) (O_node (getnode node)) (defObj))
                   ((node (data Int) (next Addr) (prev Addr)))))
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
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Heap)) (or (not (and (inv_main60 var5 var4 var3 var2 var1 var0) (and (is-O_node (read var5 var1)) (not (= var3 (data (getnode (read var5 var1)))))))) (inv_main76 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Heap)) (or (not (and (inv_main58 var5 var4 var3 var2 var1 var0) (and (not (= var0 (+ 1 var4))) (= var1 nullAddr)))) (inv_main76 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Heap)) (or (not (and (inv_main58 var5 var4 var3 var2 var1 var0) (not (= var1 nullAddr)))) (inv_main60 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Int) (var4 Addr) (var5 Int) (var6 Int) (var7 Heap)) (or (not (and (inv_main40 var7 var6 var5 var4 var3 var2 var1 var0) (is-O_node (read var7 var0)))) (inv_main46 (write var7 var0 (O_node (node (data (getnode (read var7 var0))) nullAddr (prev (getnode (read var7 var0)))))) var6 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Addr) (var6 Int) (var7 Int) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Int) (var12 Int) (var13 Addr) (var14 Int) (var15 Int) (var16 Heap)) (or (not (and (inv_main54 var16 var15 var14 var13 var12 var11 var10 var9) (and (is-O_node (read var16 var9)) (and (and (and (and (and (and (and (and (= var8 var16) (= var7 var15)) (= var6 var14)) (= var5 var13)) (= var4 var12)) (= var3 var11)) (= var2 var10)) (= var1 var9)) (= var0 (next (getnode (read var16 var9)))))))) (inv_main52 var8 var7 var6 var5 var4 var3 var2 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Int) (var10 Int) (var11 Int) (var12 Addr) (var13 Int) (var14 Int) (var15 Heap)) (or (not (and (inv_main47 var15 var14 var13 var12 var11 var10 var9 var8) (and (not (= nullAddr var7)) (and (is-O_node (read var15 var8)) (and (and (and (and (and (and (and (= var6 (write var15 var8 (O_node (node var9 (next (getnode (read var15 var8))) (prev (getnode (read var15 var8))))))) (= var5 var14)) (= var4 var13)) (= var7 var12)) (= var3 var11)) (= var2 var10)) (= var1 var9)) (= var0 var8)))))) (inv_main52 var6 var5 var4 var7 var3 var2 var0 var7))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 node) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Int) (var11 Int) (var12 Int) (var13 Int) (var14 Heap)) (or (not (and (inv_main8 var14 var13 var12 var11 var10 var9) (and (and (not (= nullAddr var8)) (and (and (and (and (and (and (and (= var7 (newHeap (alloc var14 (O_node var6)))) (= var5 var13)) (= var4 var12)) (= var3 var11)) (= var2 var10)) (= var1 var9)) (= var0 var10)) (= var8 (newAddr (alloc var14 (O_node var6)))))) (<= 0 (+ var11 (- 1)))))) (inv_main15 var7 var5 var4 var3 var2 var1 var0 var8))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Addr) (var5 Int) (var6 Int) (var7 Heap)) (or (not (and (inv_main52 var7 var6 var5 var4 var3 var2 var1 var0) (and (is-O_node (read var7 var0)) (= (next (getnode (read var7 var0))) nullAddr)))) (inv_main53 var7 var6 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Addr) (var5 Int) (var6 Int) (var7 Heap)) (or (not (and (inv_main53 var7 var6 var5 var4 var3 var2 var1 var0) (is-O_node (read var7 var0)))) (inv_main56 (write var7 var0 (O_node (node (data (getnode (read var7 var0))) var1 (prev (getnode (read var7 var0)))))) var6 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Heap) (var8 Addr) (var9 Int) (var10 Addr) (var11 Int) (var12 Int) (var13 Int) (var14 Int) (var15 Heap)) (or (not (and (inv_main22 var15 var14 var13 var12 var11 var10 var9 var8) (and (is-O_node (read var15 var8)) (and (and (and (and (and (and (and (= var7 (write var15 var8 (O_node (node var9 (next (getnode (read var15 var8))) (prev (getnode (read var15 var8))))))) (= var6 var14)) (= var5 var13)) (= var4 var12)) (= var3 var11)) (= var2 var10)) (= var1 var9)) (= var0 var8))))) (inv_main24 var7 var6 var5 var4 var3 var2 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Heap)) (or (not (and (inv_main15 var7 var6 var5 var4 var3 var2 var1 var0) (is-O_node (read var7 var0)))) (inv_main21 (write var7 var0 (O_node (node (data (getnode (read var7 var0))) nullAddr (prev (getnode (read var7 var0)))))) var6 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Heap)) (or (not (and (inv_main21 var7 var6 var5 var4 var3 var2 var1 var0) (is-O_node (read var7 var0)))) (inv_main22 (write var7 var0 (O_node (node (data (getnode (read var7 var0))) (next (getnode (read var7 var0))) nullAddr))) var6 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Heap)) (or (not (and (inv_main60 var5 var4 var3 var2 var1 var0) (and (is-O_node (read var5 var1)) (= var3 (data (getnode (read var5 var1))))))) (inv_main61 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Int) (var4 Int) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Int) (var10 Int) (var11 Int) (var12 Int) (var13 Heap)) (or (not (and (inv_main25 var13 var12 var11 var10 var9 var8 var7) (and (and (not (= var6 nullAddr)) (is-O_node (read var13 var7))) (and (and (and (and (and (and (= var5 (write var13 var7 (O_node (node (data (getnode (read var13 var7))) var8 (prev (getnode (read var13 var7))))))) (= var4 var12)) (= var3 var11)) (= var2 var10)) (= var1 var9)) (= var6 var8)) (= var0 var7))))) (inv_main28 var5 var4 var3 var2 var1 var6 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Addr) (var5 Int) (var6 Int) (var7 Heap)) (or (not (and (inv_main52 var7 var6 var5 var4 var3 var2 var1 var0) (and (is-O_node (read var7 var0)) (not (= (next (getnode (read var7 var0))) nullAddr))))) (inv_main54 var7 var6 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Int) (var5 Int) (var6 node) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Int) (var11 Int) (var12 Int) (var13 Int) (var14 Heap)) (or (not (and (inv_main8 var14 var13 var12 var11 var10 var9) (and (and (not (= nullAddr var8)) (and (and (and (and (and (and (and (= var7 (newHeap (alloc var14 (O_node var6)))) (= var5 var13)) (= var4 var12)) (= var3 var9)) (= var2 3)) (= var1 var12)) (= var0 var12)) (= var8 (newAddr (alloc var14 (O_node var6)))))) (not (<= 0 (+ var11 (- 1))))))) (inv_main40 var7 var5 var4 var3 var2 var1 var0 var8))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Addr) (var4 Int) (var5 Int) (var6 Int) (var7 Int) (var8 Heap)) (or (not (inv_main18 var8 var7 var6 var5 var4 var3 var2 var1 var0)) (inv_main18 var8 var7 var6 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 node) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Int) (var11 Int) (var12 Int) (var13 Int) (var14 Heap)) (or (not (and (inv_main8 var14 var13 var12 var11 var10 var9) (and (and (= nullAddr var8) (and (and (and (and (and (and (and (= var7 (newHeap (alloc var14 (O_node var6)))) (= var5 var13)) (= var4 var12)) (= var3 var11)) (= var2 var10)) (= var1 var9)) (= var0 var10)) (= var8 (newAddr (alloc var14 (O_node var6)))))) (<= 0 (+ var11 (- 1)))))) (inv_main18 var7 var5 var4 var3 var2 var1 var0 var8 1))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Int) (var5 Int) (var6 Heap) (var7 Int) (var8 Addr) (var9 Addr) (var10 Int) (var11 Int) (var12 Heap)) (or (not (and (inv_main61 var12 var11 var10 var9 var8 var7) (and (is-O_node (read var12 var8)) (and (and (and (and (and (and (= var6 var12) (= var5 var11)) (= var4 var10)) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var0 (next (getnode (read var12 var8)))))))) (inv_main58 var6 var5 var4 var3 var0 (+ var1 1)))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Int) (var4 Int) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Int) (var9 Int) (var10 Addr) (var11 Int) (var12 Int) (var13 Heap)) (or (not (and (inv_main56 var13 var12 var11 var10 var9 var8 var7 var6) (and (is-O_node (read var13 var7)) (and (and (and (and (and (= var5 (write var13 var7 (O_node (node (data (getnode (read var13 var7))) (next (getnode (read var13 var7))) var6)))) (= var4 var12)) (= var3 var11)) (= var2 var10)) (= var1 var9)) (= var0 var8))))) (inv_main58 var5 var4 var3 var2 var2 0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Int) (var10 Int) (var11 Int) (var12 Addr) (var13 Int) (var14 Int) (var15 Heap)) (or (not (and (inv_main47 var15 var14 var13 var12 var11 var10 var9 var8) (and (= nullAddr var7) (and (is-O_node (read var15 var8)) (and (and (and (and (and (and (and (= var6 (write var15 var8 (O_node (node var9 (next (getnode (read var15 var8))) (prev (getnode (read var15 var8))))))) (= var5 var14)) (= var4 var13)) (= var7 var12)) (= var3 var11)) (= var2 var10)) (= var1 var9)) (= var0 var8)))))) (inv_main58 var6 var5 var4 var0 var0 0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Heap)) (or (not (and (inv_main24 var6 var5 var4 var3 var2 var1 var0) (is-O_node (read var6 var0)))) (inv_main25 (write var6 var0 (O_node (node var2 (next (getnode (read var6 var0))) (prev (getnode (read var6 var0)))))) var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Addr) (var6 Int) (var7 Int) (var8 Heap)) (or (not (inv_main43 var8 var7 var6 var5 var4 var3 var2 var1 var0)) (inv_main43 var8 var7 var6 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Int) (var5 Int) (var6 node) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Int) (var11 Int) (var12 Int) (var13 Int) (var14 Heap)) (or (not (and (inv_main8 var14 var13 var12 var11 var10 var9) (and (and (= nullAddr var8) (and (and (and (and (and (and (and (= var7 (newHeap (alloc var14 (O_node var6)))) (= var5 var13)) (= var4 var12)) (= var3 var9)) (= var2 3)) (= var1 var12)) (= var0 var12)) (= var8 (newAddr (alloc var14 (O_node var6)))))) (not (<= 0 (+ var11 (- 1))))))) (inv_main43 var7 var5 var4 var3 var2 var1 var0 var8 1))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Int) (var4 Addr) (var5 Int) (var6 Int) (var7 Heap)) (or (not (and (inv_main46 var7 var6 var5 var4 var3 var2 var1 var0) (is-O_node (read var7 var0)))) (inv_main47 (write var7 var0 (O_node (node (data (getnode (read var7 var0))) (next (getnode (read var7 var0))) nullAddr))) var6 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Int) (var5 Int) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Int) (var10 Addr) (var11 Addr) (var12 Int) (var13 Int) (var14 Heap) (var15 Addr) (var16 Addr) (var17 Int) (var18 Addr) (var19 Addr) (var20 Int) (var21 Int) (var22 Heap)) (or (not (and (inv_main73 var22 var21 var20 var19 var18 var17 var16) (and (not (= var15 nullAddr)) (and (and (is-O_node (read var22 var16)) (and (and (and (and (and (and (and (= var14 var22) (= var13 var21)) (= var12 var20)) (= var11 var19)) (= var10 var18)) (= var9 var17)) (= var8 var16)) (= var7 (next (getnode (read var22 var16)))))) (and (and (and (and (and (and (and (= var6 (write var14 var8 defObj)) (= var5 var13)) (= var4 var12)) (= var3 var11)) (= var2 var10)) (= var1 var9)) (= var0 var8)) (= var15 var7)))))) (inv_main73 var6 var5 var4 var3 var2 var1 var15))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Heap)) (or (not (and (inv_main58 var5 var4 var3 var2 var1 var0) (and (not (= var2 nullAddr)) (and (= var0 (+ 1 var4)) (= var1 nullAddr))))) (inv_main73 var5 var4 var3 var2 var1 var0 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Int) (var10 Int) (var11 Int) (var12 Int) (var13 Heap)) (or (not (and (inv_main28 var13 var12 var11 var10 var9 var8 var7) (and (is-O_node (read var13 var8)) (and (and (and (and (and (and (= var6 (write var13 var8 (O_node (node (data (getnode (read var13 var8))) (next (getnode (read var13 var8))) var7)))) (= var5 var12)) (= var4 var11)) (= var3 var10)) (= var2 var9)) (= var1 var8)) (= var0 var7))))) (inv_main8 var6 var5 var4 (+ var3 (- 1)) var2 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Int) (var4 Int) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Int) (var10 Int) (var11 Int) (var12 Int) (var13 Heap)) (or (not (and (inv_main25 var13 var12 var11 var10 var9 var8 var7) (and (and (= var6 nullAddr) (is-O_node (read var13 var7))) (and (and (and (and (and (and (= var5 (write var13 var7 (O_node (node (data (getnode (read var13 var7))) var8 (prev (getnode (read var13 var7))))))) (= var4 var12)) (= var3 var11)) (= var2 var10)) (= var1 var9)) (= var6 var8)) (= var0 var7))))) (inv_main8 var5 var4 var3 (+ var2 (- 1)) var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Heap)) (or (not (inv_main4 var2 var1 var0)) (inv_main8 var2 var1 var0 var1 var0 nullAddr))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Heap)) (not (and (inv_main15 var7 var6 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var7 var0)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Heap)) (not (and (inv_main21 var7 var6 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var7 var0)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Heap)) (not (and (inv_main22 var7 var6 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var7 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Heap)) (not (and (inv_main24 var6 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var6 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Heap)) (not (and (inv_main25 var6 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var6 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Heap)) (not (and (inv_main28 var6 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var6 var1)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Int) (var4 Addr) (var5 Int) (var6 Int) (var7 Heap)) (not (and (inv_main40 var7 var6 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var7 var0)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Int) (var4 Addr) (var5 Int) (var6 Int) (var7 Heap)) (not (and (inv_main46 var7 var6 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var7 var0)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Int) (var4 Addr) (var5 Int) (var6 Int) (var7 Heap)) (not (and (inv_main47 var7 var6 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var7 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Addr) (var5 Int) (var6 Int) (var7 Heap)) (not (and (inv_main52 var7 var6 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var7 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Addr) (var5 Int) (var6 Int) (var7 Heap)) (not (and (inv_main54 var7 var6 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var7 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Addr) (var5 Int) (var6 Int) (var7 Heap)) (not (and (inv_main53 var7 var6 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var7 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Addr) (var5 Int) (var6 Int) (var7 Heap)) (not (and (inv_main56 var7 var6 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var7 var1)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Heap)) (not (and (inv_main60 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var5 var1)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Heap)) (not (and (inv_main61 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var5 var1)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Int) (var5 Int) (var6 Heap)) (not (and (inv_main73 var6 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var6 var0)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Heap)) (not (inv_main76 var5 var4 var3 var2 var1 var0))))
(check-sat)
