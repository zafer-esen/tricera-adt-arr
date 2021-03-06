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
                   (((O_Int (getInt Int)) (O_UInt (getUInt Int)) (O_Addr (getAddr Addr)) (O_node (getnode node)) (defObj))
                   ((node (data_0 Int) (next Addr) (data_1 Int) (prev Addr) (data_2 Int)))))
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
(declare-fun inv_main11 (Heap Int Int Addr Addr) Bool)
(declare-fun inv_main14 (Heap Int Int Addr Addr Int) Bool)
(declare-fun inv_main17 (Heap Int Int Addr Addr) Bool)
(declare-fun inv_main19 (Heap Int Int Addr Addr) Bool)
(declare-fun inv_main21 (Heap Int Int Addr Addr Int) Bool)
(declare-fun inv_main22 (Heap Int Int Addr Addr) Bool)
(declare-fun inv_main25 (Heap Int Int Addr Addr) Bool)
(declare-fun inv_main28 (Heap Int Addr) Bool)
(declare-fun inv_main3 (Heap Int) Bool)
(declare-fun inv_main30 (Heap Int Addr) Bool)
(declare-fun inv_main32 (Heap Int Addr Int Int Int) Bool)
(declare-fun inv_main37 (Heap Int Addr) Bool)
(declare-fun inv_main38 (Heap Int Addr Addr) Bool)
(declare-fun inv_main44 (Heap Int Addr) Bool)
(declare-fun inv_main7 (Heap Int Int Addr) Bool)
(assert (forall ((var0 Heap)) (or (not (= var0 emptyHeap)) (inv_main3 var0 5))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Heap)) (or (not (and (inv_main37 var2 var1 var0) (is-O_node (read var2 var0)))) (inv_main38 var2 var1 var0 (prev (getnode (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Heap)) (or (not (and (inv_main28 var2 var1 var0) (and (is-O_node (read var2 var0)) (not (= (next (getnode (read var2 var0))) nullAddr))))) (inv_main30 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Heap)) (or (not (and (inv_main19 var4 var3 var2 var1 var0) (and (is-O_node (read var4 var0)) (is-O_node (read var4 var0))))) (inv_main22 (write var4 var0 (O_node (node (data_0 (getnode (read var4 var0))) var1 (data_1 (getnode (read var4 var0))) (prev (getnode (read var4 var0))) (data_2 (getnode (read var4 var0)))))) var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Int) (var4 Addr) (var5 Int) (var6 Heap) (var7 Int) (var8 Int) (var9 Int) (var10 Addr) (var11 Int) (var12 Heap)) (or (not (and (inv_main32 var12 var11 var10 var9 var8 var7) (and (is-O_node (read var12 var10)) (and (and (and (and (and (and (= var6 var12) (= var5 var11)) (= var4 var10)) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var0 (next (getnode (read var12 var10)))))))) (inv_main28 var6 var5 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Heap)) (or (not (and (inv_main7 var3 var2 var1 var0) (not (<= 0 (+ var1 (- 1)))))) (inv_main28 var3 var2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Heap)) (or (not (and (inv_main11 var4 var3 var2 var1 var0) (and (is-O_node (read var4 var0)) (is-O_node (read var4 var0))))) (inv_main17 (write var4 var0 (O_node (node 0 (next (getnode (read var4 var0))) (data_1 (getnode (read var4 var0))) (prev (getnode (read var4 var0))) (data_2 (getnode (read var4 var0)))))) var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 node) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Int) (var8 Int) (var9 Heap)) (or (not (and (inv_main7 var9 var8 var7 var6) (and (and (not (= nullAddr var5)) (and (and (and (and (= var4 (newHeap (alloc var9 (O_node var3)))) (= var2 var8)) (= var1 var7)) (= var0 var6)) (= var5 (newAddr (alloc var9 (O_node var3)))))) (<= 0 (+ var7 (- 1)))))) (inv_main11 var4 var2 var1 var0 var5))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap) (var4 Int) (var5 Int) (var6 Addr) (var7 Addr) (var8 Int) (var9 Int) (var10 Heap)) (or (not (and (inv_main17 var10 var9 var8 var7 var6) (and (= var5 var4) (and (and (is-O_node (read var10 var6)) (is-O_node (read var10 var6))) (and (and (and (and (= var3 (write var10 var6 (O_node (node (data_0 (getnode (read var10 var6))) (next (getnode (read var10 var6))) 0 (prev (getnode (read var10 var6))) (data_2 (getnode (read var10 var6))))))) (= var2 var9)) (= var4 var8)) (= var1 var7)) (= var0 var6)))))) (inv_main21 var3 var2 var4 var1 var0 1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap) (var4 Int) (var5 Int) (var6 Addr) (var7 Addr) (var8 Int) (var9 Int) (var10 Heap)) (or (not (and (inv_main17 var10 var9 var8 var7 var6) (and (not (= var5 var4)) (and (and (is-O_node (read var10 var6)) (is-O_node (read var10 var6))) (and (and (and (and (= var3 (write var10 var6 (O_node (node (data_0 (getnode (read var10 var6))) (next (getnode (read var10 var6))) 0 (prev (getnode (read var10 var6))) (data_2 (getnode (read var10 var6))))))) (= var2 var9)) (= var4 var8)) (= var1 var7)) (= var0 var6)))))) (inv_main21 var3 var2 var4 var1 var0 0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Int) (var8 Int) (var9 Heap)) (or (not (and (inv_main25 var9 var8 var7 var6 var5) (and (and (is-O_node (read var9 var6)) (is-O_node (read var9 var6))) (and (and (and (and (= var4 (write var9 var6 (O_node (node (data_0 (getnode (read var9 var6))) (next (getnode (read var9 var6))) (data_1 (getnode (read var9 var6))) var5 (data_2 (getnode (read var9 var6))))))) (= var3 var8)) (= var2 var7)) (= var1 var6)) (= var0 var5))))) (inv_main7 var4 var3 (+ var2 (- 1)) var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Int) (var8 Int) (var9 Heap)) (or (not (and (inv_main22 var9 var8 var7 var6 var5) (and (and (= var4 nullAddr) (and (is-O_node (read var9 var5)) (is-O_node (read var9 var5)))) (and (and (and (and (= var3 (write var9 var5 (O_node (node (data_0 (getnode (read var9 var5))) (next (getnode (read var9 var5))) (data_1 (getnode (read var9 var5))) nullAddr (data_2 (getnode (read var9 var5))))))) (= var2 var8)) (= var1 var7)) (= var4 var6)) (= var0 var5))))) (inv_main7 var3 var2 (+ var1 (- 1)) var0))))
(assert (forall ((var0 Int) (var1 Heap)) (or (not (inv_main3 var1 var0)) (inv_main7 var1 var0 var0 nullAddr))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Int) (var8 Int) (var9 Heap)) (or (not (and (inv_main22 var9 var8 var7 var6 var5) (and (and (not (= var4 nullAddr)) (and (is-O_node (read var9 var5)) (is-O_node (read var9 var5)))) (and (and (and (and (= var3 (write var9 var5 (O_node (node (data_0 (getnode (read var9 var5))) (next (getnode (read var9 var5))) (data_1 (getnode (read var9 var5))) nullAddr (data_2 (getnode (read var9 var5))))))) (= var2 var8)) (= var1 var7)) (= var4 var6)) (= var0 var5))))) (inv_main25 var3 var2 var1 var4 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Heap)) (or (not (and (inv_main28 var2 var1 var0) (and (not (= var0 nullAddr)) (and (is-O_node (read var2 var0)) (= (next (getnode (read var2 var0))) nullAddr))))) (inv_main37 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Int) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Int) (var9 Heap) (var10 Int) (var11 Int) (var12 Int) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Int) (var17 Heap)) (or (not (and (inv_main38 var17 var16 var15 var14) (and (not (= var13 nullAddr)) (and (and (and (and (and (= 0 var12) (= 0 var11)) (= 0 var10)) (and (and (is-O_node (read var17 var15)) (is-O_node (read var17 var15))) (is-O_node (read var17 var15)))) (and (and (and (and (and (and (= var9 var17) (= var8 var16)) (= var7 var15)) (= var6 var14)) (= var12 (data_0 (getnode (read var17 var15))))) (= var11 (data_1 (getnode (read var17 var15))))) (= var10 (data_2 (getnode (read var17 var15)))))) (and (and (and (and (and (and (= var5 (write var9 var7 defObj)) (= var4 var8)) (= var3 var7)) (= var13 var6)) (= var2 var12)) (= var1 var11)) (= var0 var10)))))) (inv_main37 var5 var4 var13))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap) (var4 Int) (var5 Int) (var6 Int) (var7 Addr) (var8 Addr) (var9 Int) (var10 Heap)) (or (not (and (inv_main38 var10 var9 var8 var7) (and (and (or (or (not (= 0 var6)) (not (= 0 var5))) (not (= 0 var4))) (and (and (is-O_node (read var10 var8)) (is-O_node (read var10 var8))) (is-O_node (read var10 var8)))) (and (and (and (and (and (and (= var3 var10) (= var2 var9)) (= var1 var8)) (= var0 var7)) (= var6 (data_0 (getnode (read var10 var8))))) (= var5 (data_1 (getnode (read var10 var8))))) (= var4 (data_2 (getnode (read var10 var8)))))))) (inv_main44 var3 var2 var1))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Heap) (var3 Int) (var4 Int) (var5 Int) (var6 Addr) (var7 Int) (var8 Heap)) (or (not (and (inv_main30 var8 var7 var6) (and (and (or (or (not (= 0 var5)) (not (= 0 var4))) (not (= 0 var3))) (and (and (is-O_node (read var8 var6)) (is-O_node (read var8 var6))) (is-O_node (read var8 var6)))) (and (and (and (and (and (= var2 var8) (= var1 var7)) (= var0 var6)) (= var5 (data_0 (getnode (read var8 var6))))) (= var4 (data_1 (getnode (read var8 var6))))) (= var3 (data_2 (getnode (read var8 var6)))))))) (inv_main44 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Heap) (var3 Int) (var4 Int) (var5 Int) (var6 Addr) (var7 Int) (var8 Heap)) (or (not (and (inv_main30 var8 var7 var6) (and (and (and (and (= 0 var5) (= 0 var4)) (= 0 var3)) (and (and (is-O_node (read var8 var6)) (is-O_node (read var8 var6))) (is-O_node (read var8 var6)))) (and (and (and (and (and (= var2 var8) (= var1 var7)) (= var0 var6)) (= var5 (data_0 (getnode (read var8 var6))))) (= var4 (data_1 (getnode (read var8 var6))))) (= var3 (data_2 (getnode (read var8 var6)))))))) (inv_main32 var2 var1 var0 var5 var4 var3))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Heap)) (or (not (and (inv_main21 var5 var4 var3 var2 var1 var0) (and (is-O_node (read var5 var1)) (is-O_node (read var5 var1))))) (inv_main19 (write var5 var1 (O_node (node (data_0 (getnode (read var5 var1))) (next (getnode (read var5 var1))) (data_1 (getnode (read var5 var1))) (prev (getnode (read var5 var1))) var0))) var4 var3 var2 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Heap)) (or (not (inv_main14 var5 var4 var3 var2 var1 var0)) (inv_main14 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 node) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Int) (var8 Int) (var9 Heap)) (or (not (and (inv_main7 var9 var8 var7 var6) (and (and (= nullAddr var5) (and (and (and (and (= var4 (newHeap (alloc var9 (O_node var3)))) (= var2 var8)) (= var1 var7)) (= var0 var6)) (= var5 (newAddr (alloc var9 (O_node var3)))))) (<= 0 (+ var7 (- 1)))))) (inv_main14 var4 var2 var1 var0 var5 1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Heap)) (not (and (inv_main11 var4 var3 var2 var1 var0) (not (is-O_node (read var4 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Heap)) (not (and (inv_main11 var4 var3 var2 var1 var0) (and (is-O_node (read var4 var0)) (not (is-O_node (read var4 var0))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Heap)) (not (and (inv_main17 var4 var3 var2 var1 var0) (not (is-O_node (read var4 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Heap)) (not (and (inv_main17 var4 var3 var2 var1 var0) (and (is-O_node (read var4 var0)) (not (is-O_node (read var4 var0))))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Heap)) (not (and (inv_main21 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var5 var1)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Heap)) (not (and (inv_main21 var5 var4 var3 var2 var1 var0) (and (is-O_node (read var5 var1)) (not (is-O_node (read var5 var1))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Heap)) (not (and (inv_main19 var4 var3 var2 var1 var0) (not (is-O_node (read var4 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Heap)) (not (and (inv_main19 var4 var3 var2 var1 var0) (and (is-O_node (read var4 var0)) (not (is-O_node (read var4 var0))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Heap)) (not (and (inv_main22 var4 var3 var2 var1 var0) (not (is-O_node (read var4 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Heap)) (not (and (inv_main22 var4 var3 var2 var1 var0) (and (is-O_node (read var4 var0)) (not (is-O_node (read var4 var0))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Heap)) (not (and (inv_main25 var4 var3 var2 var1 var0) (not (is-O_node (read var4 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Heap)) (not (and (inv_main25 var4 var3 var2 var1 var0) (and (is-O_node (read var4 var1)) (not (is-O_node (read var4 var1))))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Heap)) (not (and (inv_main28 var2 var1 var0) (not (is-O_node (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Heap)) (not (and (inv_main30 var2 var1 var0) (not (is-O_node (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Heap)) (not (and (inv_main30 var2 var1 var0) (and (is-O_node (read var2 var0)) (not (is-O_node (read var2 var0))))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Heap)) (not (and (inv_main30 var2 var1 var0) (and (and (is-O_node (read var2 var0)) (is-O_node (read var2 var0))) (not (is-O_node (read var2 var0))))))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Int) (var5 Heap)) (not (and (inv_main32 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var5 var3)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Heap)) (not (and (inv_main37 var2 var1 var0) (not (is-O_node (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap)) (not (and (inv_main38 var3 var2 var1 var0) (not (is-O_node (read var3 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap)) (not (and (inv_main38 var3 var2 var1 var0) (and (is-O_node (read var3 var1)) (not (is-O_node (read var3 var1))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap)) (not (and (inv_main38 var3 var2 var1 var0) (and (and (is-O_node (read var3 var1)) (is-O_node (read var3 var1))) (not (is-O_node (read var3 var1))))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Heap)) (not (inv_main44 var2 var1 var0))))
(check-sat)
