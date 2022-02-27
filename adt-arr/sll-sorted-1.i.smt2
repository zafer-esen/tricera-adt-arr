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
(declare-datatypes ((HeapObject 0) (TSLL 0))
                   (((O_Int (getInt Int)) (O_Addr (getAddr Addr)) (O_TSLL (getTSLL TSLL)) (defObj))
                   ((TSLL (next Addr) (data Int)))))
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
(declare-fun inv_main11 (Heap Addr Addr Int) Bool)
(declare-fun inv_main12 (Heap Addr Addr Int Addr) Bool)
(declare-fun inv_main13 (Heap Addr Addr Int) Bool)
(declare-fun inv_main2 (Heap) Bool)
(declare-fun inv_main20 (Heap Addr Addr Int) Bool)
(declare-fun inv_main21 (Heap Addr Addr Int) Bool)
(declare-fun inv_main25 (Heap Addr Addr Int) Bool)
(declare-fun inv_main28 (Heap Addr Addr Int) Bool)
(declare-fun inv_main29 (Heap Addr Addr Int) Bool)
(declare-fun inv_main3 (Heap Addr) Bool)
(declare-fun inv_main30 (Heap Addr Addr Int) Bool)
(declare-fun inv_main31 (Heap Addr Addr Int Addr) Bool)
(declare-fun inv_main36 (Heap Addr Addr Int) Bool)
(declare-fun inv_main4 (Heap Addr) Bool)
(declare-fun inv_main40 (Heap Addr Addr Int) Bool)
(declare-fun inv_main43 (Heap Addr Addr Int) Bool)
(declare-fun inv_main47 (Heap Addr Addr Int Addr) Bool)
(declare-fun inv_main48 (Heap Addr Addr Int Addr) Bool)
(declare-fun inv_main49 (Heap Addr Addr Int Addr) Bool)
(declare-fun inv_main51 (Heap Addr Addr Int Addr) Bool)
(declare-fun inv_main52 (Heap Addr Addr Int Addr) Bool)
(declare-fun inv_main54 (Heap Addr Addr Int Addr) Bool)
(declare-fun inv_main55 (Heap Addr Addr Int Addr Addr) Bool)
(declare-fun inv_main57 (Heap Addr Addr Int Addr) Bool)
(declare-fun inv_main58 (Heap Addr Addr Int Addr) Bool)
(declare-fun inv_main59 (Heap Addr Addr Int Addr) Bool)
(declare-fun inv_main62 (Heap Addr Addr Int Addr) Bool)
(declare-fun inv_main66 (Heap Addr Addr Int Addr) Bool)
(declare-fun inv_main7 (Heap Addr Addr Int) Bool)
(declare-fun inv_main70 (Heap Addr Addr Int Addr) Bool)
(declare-fun inv_main72 (Heap Addr Addr Int Addr) Bool)
(declare-fun inv_main77 (Heap Addr Addr Int Addr) Bool)
(declare-fun inv_main78 (Heap Addr Addr Int Addr) Bool)
(declare-fun inv_main82 (Heap Addr Addr Int Addr) Bool)
(declare-fun inv_main86 (Heap Addr Addr Int Addr) Bool)
(declare-fun inv_main88 (Heap Addr Addr Int Addr) Bool)
(declare-fun inv_main95 (Heap Addr Addr Int Addr) Bool)
(assert (inv_main2 emptyHeap))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Int) (var9 Addr) (var10 Heap)) (or (not (and (inv_main49 var10 var2 var1 var8 var6) (and (not (= var7 nullAddr)) (and (and (and (and (and (= var5 var10) (= var9 var2)) (= var0 var1)) (= var3 var8)) (= var4 var6)) (= var7 (next (getTSLL (read var10 var1)))))))) (inv_main52 var5 var9 var0 var3 var4))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap) (var4 Addr)) (or (not (and (inv_main31 var3 var1 var0 var2 var4) (= var4 nullAddr))) (inv_main29 var3 var1 var0 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Addr) (var6 Int) (var7 Heap) (var8 Int) (var9 Heap) (var10 Addr) (var11 Heap) (var12 Addr) (var13 Int) (var14 Addr)) (or (not (and (inv_main31 var9 var5 var1 var13 var10) (and (and (= var6 0) (and (not (= var10 nullAddr)) (and (and (and (and (= var11 var9) (= var0 var5)) (= var12 var1)) (= var8 var13)) (= var4 (data (getTSLL (read var9 (next (getTSLL (read var9 var1)))))))))) (and (and (and (and (= var7 var11) (= var2 var0)) (= var14 var12)) (= var3 var8)) (or (and (= var4 0) (= var6 1)) (and (not (= var4 0)) (= var6 0))))))) (inv_main29 var7 var2 var14 var3))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Heap) (var4 Int) (var5 Int) (var6 Heap) (var7 Addr) (var8 Addr)) (or (not (and (inv_main40 var6 var2 var0 var5) (and (= var1 1) (and (and (and (and (= var3 var6) (= var8 var2)) (= var7 var0)) (= var4 var5)) (= var1 (data (getTSLL (read var6 var0)))))))) (inv_main29 var3 var8 var7 var4))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap)) (or (not (inv_main52 var4 var1 var0 var3 var2)) (inv_main55 var4 var1 var0 var3 var2 (next (getTSLL (read var4 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap)) (or (not (inv_main3 var1 var0)) (inv_main4 (write var1 var0 (O_TSLL (TSLL nullAddr (data (getTSLL (read var1 var0)))))) var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap)) (or (not (inv_main47 var4 var1 var0 var3 var2)) (inv_main48 (write var4 var2 (O_TSLL (TSLL (next (getTSLL (read var4 var2))) 1))) var1 var0 var3 var2))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Int) (var6 Int) (var7 Addr) (var8 Heap) (var9 Addr) (var10 Addr)) (or (not (and (inv_main86 var8 var2 var0 var6 var4) (and (and (and (and (and (= var1 var8) (= var3 var2)) (= var10 var0)) (= var5 var6)) (= var7 var4)) (= var9 (next (getTSLL (read var8 var0))))))) (inv_main58 var1 var3 var9 var5 var7))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap)) (or (not (and (inv_main57 var4 var1 var0 var3 var2) (= var0 nullAddr))) (inv_main58 var4 var1 var0 var3 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Int) (var9 Int) (var10 Int) (var11 Heap) (var12 Heap) (var13 Int) (var14 Addr) (var15 Addr) (var16 Int)) (or (not (and (inv_main57 var12 var3 var1 var16 var6) (and (and (= var10 0) (and (not (= var1 nullAddr)) (and (and (and (and (and (= var2 var12) (= var15 var3)) (= var4 var1)) (= var8 var16)) (= var5 var6)) (= var13 (data (getTSLL (read var12 var1))))))) (and (and (and (and (and (= var11 var2) (= var7 var15)) (= var0 var4)) (= var9 var8)) (= var14 var5)) (or (and (not (= var13 1)) (= var10 1)) (and (= var13 1) (= var10 0))))))) (inv_main58 var11 var7 var0 var9 var14))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Int) (var4 Addr) (var5 Addr) (var6 Int) (var7 Int) (var8 Heap)) (or (not (and (inv_main40 var8 var2 var0 var7) (and (not (= var6 1)) (and (and (and (and (= var1 var8) (= var5 var2)) (= var4 var0)) (= var3 var7)) (= var6 (data (getTSLL (read var8 var0)))))))) (inv_main43 var1 var5 var4 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Int) (var7 Heap) (var8 Int)) (or (not (and (inv_main30 var7 var4 var1 var6) (and (and (and (and (= var3 var7) (= var5 var4)) (= var0 var1)) (= var8 var6)) (= var2 (next (getTSLL (read var7 var1))))))) (inv_main28 var3 var5 var2 var8))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Heap)) (or (not (and (inv_main7 var4 var1 var0 var3) (and (not (= nullAddr var1)) (and (= var2 0) (not (= var3 0)))))) (inv_main28 var4 var1 var1 0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Int) (var7 Int) (var8 Heap) (var9 Addr) (var10 Int)) (or (not (and (inv_main78 var8 var1 var0 var6 var4) (and (= var7 1) (and (and (and (and (and (= var3 var8) (= var2 var1)) (= var5 var0)) (= var10 var6)) (= var9 var4)) (= var7 (data (getTSLL (read var8 var0)))))))) (inv_main82 var3 var2 var5 var10 var9))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap)) (or (not (inv_main28 var3 var1 var0 var2)) (inv_main31 var3 var1 var0 var2 (next (getTSLL (read var3 var0)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Int) (var8 Heap) (var9 Addr) (var10 Heap)) (or (not (and (inv_main78 var8 var2 var1 var7 var5) (and (not (= var3 1)) (and (not (= var0 1)) (and (and (and (and (and (= var10 var8) (= var4 var2)) (= var9 var1)) (= var3 var7)) (= var6 var5)) (= var0 (data (getTSLL (read var8 var1))))))))) (inv_main88 var10 var4 var9 var3 var6))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap)) (or (not (and (inv_main58 var4 var1 var0 var3 var2) (not (= var0 nullAddr)))) (inv_main77 var4 var1 var0 var3 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Int) (var6 Heap) (var7 Heap) (var8 Addr)) (or (not (and (inv_main36 var7 var2 var1 var4) (and (and (and (and (= var6 var7) (= var3 var2)) (= var0 var1)) (= var5 var4)) (= var8 (next (getTSLL (read var7 var1))))))) (inv_main40 var6 var3 var8 var5))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap)) (or (not (inv_main48 var4 var1 var0 var3 var2)) (inv_main49 (write var4 var2 (O_TSLL (TSLL nullAddr (data (getTSLL (read var4 var2)))))) var1 var0 var3 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Heap)) (or (not (and (inv_main7 var4 var1 var0 var3) (and (= nullAddr var1) (and (= var2 0) (not (= var3 0)))))) (inv_main25 var4 var1 var1 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap)) (or (not (and (inv_main58 var4 var1 var0 var3 var2) (and (not (= var1 nullAddr)) (= var0 nullAddr)))) (inv_main95 var4 var1 var1 var3 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Heap) (var12 Int) (var13 Int) (var14 Addr) (var15 Addr)) (or (not (and (inv_main95 var7 var1 var0 var12 var4) (and (and (not (= var9 nullAddr)) (and (and (and (and (and (= var5 var7) (= var3 var1)) (= var8 var0)) (= var2 var12)) (= var6 var4)) (= var15 (next (getTSLL (read var7 var0)))))) (and (and (and (and (= var11 (write var5 var3 defObj)) (= var10 var3)) (= var9 var15)) (= var13 var2)) (= var14 var6))))) (inv_main95 var11 var9 var9 var13 var14))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap)) (or (not (inv_main55 var5 var1 var0 var4 var3 var2)) (inv_main54 (write var5 var3 (O_TSLL (TSLL var2 (data (getTSLL (read var5 var3)))))) var1 var0 var4 var3))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Int) (var8 Heap) (var9 Addr) (var10 Heap)) (or (not (and (inv_main78 var8 var2 var1 var7 var5) (and (= var3 1) (and (not (= var0 1)) (and (and (and (and (and (= var10 var8) (= var4 var2)) (= var9 var1)) (= var3 var7)) (= var6 var5)) (= var0 (data (getTSLL (read var8 var1))))))))) (inv_main86 var10 var4 var9 var3 var6))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Int) (var9 Int) (var10 Heap)) (or (not (and (inv_main62 var10 var2 var1 var9 var6) (and (not (= var0 0)) (and (= var8 0) (and (and (and (and (and (= var7 var10) (= var3 var2)) (= var5 var1)) (= var0 var9)) (= var4 var6)) (= var8 (data (getTSLL (read var10 var1))))))))) (inv_main72 var7 var3 var5 var0 var4))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Int) (var6 Int) (var7 Int) (var8 Heap) (var9 Addr) (var10 Addr)) (or (not (and (inv_main62 var8 var2 var0 var6 var4) (and (not (= var7 0)) (and (and (and (and (and (= var3 var8) (= var1 var2)) (= var9 var0)) (= var5 var6)) (= var10 var4)) (= var7 (data (getTSLL (read var8 var0)))))))) (inv_main66 var3 var1 var9 var5 var10))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Int) (var5 Addr) (var6 Int) (var7 Int) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main59 var10 var3 var0 var7 var5) (and (and (and (and (and (= var1 var10) (= var9 var3)) (= var2 var0)) (= var6 var7)) (= var8 var5)) (= var4 (data (getTSLL (read var10 var0))))))) (inv_main62 var1 var9 var2 var4 var8))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Int) (var6 Int) (var7 Heap) (var8 Addr) (var9 Heap) (var10 Int) (var11 Addr) (var12 Int) (var13 Heap) (var14 Addr)) (or (not (and (inv_main31 var7 var3 var1 var12 var8) (and (and (not (= var5 0)) (and (not (= var8 nullAddr)) (and (and (and (and (= var9 var7) (= var0 var3)) (= var11 var1)) (= var6 var12)) (= var2 (data (getTSLL (read var7 (next (getTSLL (read var7 var1)))))))))) (and (and (and (and (= var13 var9) (= var4 var0)) (= var14 var11)) (= var10 var6)) (or (and (= var2 0) (= var5 1)) (and (not (= var2 0)) (= var5 0))))))) (inv_main30 var13 var4 var14 var10))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Int) (var6 Addr) (var7 Addr) (var8 Int) (var9 Heap) (var10 Heap)) (or (not (and (inv_main49 var10 var2 var0 var8 var4) (and (= var3 nullAddr) (and (and (and (and (and (= var9 var10) (= var1 var2)) (= var7 var0)) (= var5 var8)) (= var6 var4)) (= var3 (next (getTSLL (read var10 var0)))))))) (inv_main51 var9 var1 var7 var5 var6))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Heap) (var5 Addr) (var6 Int) (var7 Heap) (var8 Addr)) (or (not (and (inv_main13 var7 var1 var0 var3) (and (= var6 0) (and (= var2 0) (and (and (and (= var4 (write var7 var0 (O_TSLL (TSLL nullAddr (data (getTSLL (read var7 var0))))))) (= var8 var1)) (= var5 var0)) (= var6 var3)))))) (inv_main21 var4 var8 var5 var6))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Int) (var7 Addr) (var8 Int) (var9 Heap) (var10 Heap)) (or (not (and (inv_main70 var10 var1 var0 var8 var5) (and (and (and (and (and (= var9 var10) (= var7 var1)) (= var2 var0)) (= var6 var8)) (= var3 var5)) (= var4 (next (getTSLL (read var10 var0))))))) (inv_main57 var9 var7 var4 var6 var3))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Int) (var6 Addr) (var7 Heap) (var8 Heap) (var9 Addr)) (or (not (and (inv_main51 var8 var2 var0 var5 var4) (and (and (and (and (= var7 (write var8 var0 (O_TSLL (TSLL var4 (data (getTSLL (read var8 var0))))))) (= var3 var2)) (= var9 var0)) (= var1 var5)) (= var6 var4)))) (inv_main57 var7 var3 var3 0 var6))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Int) (var5 Addr) (var6 Addr) (var7 Int) (var8 Heap) (var9 Addr)) (or (not (and (inv_main54 var8 var2 var0 var7 var5) (and (and (and (and (= var1 (write var8 var0 (O_TSLL (TSLL var5 (data (getTSLL (read var8 var0))))))) (= var9 var2)) (= var3 var0)) (= var4 var7)) (= var6 var5)))) (inv_main57 var1 var9 var9 0 var6))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Int) (var8 Heap) (var9 Int) (var10 Addr)) (or (not (and (inv_main77 var8 var2 var1 var7 var3) (and (and (and (and (and (= var5 var8) (= var10 var2)) (= var6 var1)) (= var0 var7)) (= var4 var3)) (= var9 (data (getTSLL (read var8 var1))))))) (inv_main78 var5 var10 var6 var9 var4))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 TSLL) (var5 Int) (var6 Int) (var7 Addr) (var8 Heap) (var9 Addr)) (or (not (and (inv_main29 var8 var1 var0 var5) (and (= var9 nullAddr) (and (and (and (and (= var3 var8) (= var2 var1)) (= var7 var0)) (= var6 var5)) (= var9 (next (getTSLL (read var8 var0)))))))) (inv_main47 (newHeap (alloc var3 (O_TSLL var4))) var2 var7 var6 (newAddr (alloc var3 (O_TSLL var4)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Int) (var4 Addr) (var5 Addr) (var6 Int) (var7 Addr) (var8 Int) (var9 TSLL) (var10 Heap)) (or (not (and (inv_main29 var10 var2 var1 var8) (and (= var6 0) (and (not (= var7 nullAddr)) (and (and (and (and (= var0 var10) (= var5 var2)) (= var4 var1)) (= var3 var8)) (= var7 (next (getTSLL (read var10 var1))))))))) (inv_main47 (newHeap (alloc var0 (O_TSLL var9))) var5 var4 var3 (newAddr (alloc var0 (O_TSLL var9)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Int) (var9 Heap) (var10 Int) (var11 Heap) (var12 Addr) (var13 Int) (var14 Int) (var15 Addr) (var16 Int)) (or (not (and (inv_main57 var9 var4 var1 var14 var7) (and (and (not (= var16 0)) (and (not (= var1 nullAddr)) (and (and (and (and (and (= var3 var9) (= var12 var4)) (= var5 var1)) (= var8 var14)) (= var6 var7)) (= var10 (data (getTSLL (read var9 var1))))))) (and (and (and (and (and (= var11 var3) (= var2 var12)) (= var15 var5)) (= var13 var8)) (= var0 var6)) (or (and (not (= var10 1)) (= var16 1)) (and (= var10 1) (= var16 0))))))) (inv_main59 var11 var2 var15 var13 var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Int) (var9 Heap)) (or (not (and (inv_main29 var9 var2 var1 var8) (and (not (= var3 0)) (and (not (= var7 nullAddr)) (and (and (and (and (= var0 var9) (= var6 var2)) (= var5 var1)) (= var4 var8)) (= var7 (next (getTSLL (read var9 var1))))))))) (inv_main36 var0 var6 var5 var4))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap) (var5 Addr) (var6 Int) (var7 Heap) (var8 Addr)) (or (not (and (inv_main13 var7 var2 var1 var3) (and (not (= var0 0)) (and (and (and (= var4 (write var7 var1 (O_TSLL (TSLL nullAddr (data (getTSLL (read var7 var1))))))) (= var8 var2)) (= var5 var1)) (= var6 var3))))) (inv_main20 var4 var8 var5 1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Heap) (var5 Addr) (var6 Int) (var7 Heap) (var8 Addr)) (or (not (and (inv_main13 var7 var1 var0 var3) (and (not (= var6 0)) (and (= var2 0) (and (and (and (= var4 (write var7 var0 (O_TSLL (TSLL nullAddr (data (getTSLL (read var7 var0))))))) (= var8 var1)) (= var5 var0)) (= var6 var3)))))) (inv_main20 var4 var8 var5 var6))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap)) (or (not (inv_main12 var4 var2 var0 var3 var1)) (inv_main11 (write var4 var0 (O_TSLL (TSLL var1 (data (getTSLL (read var4 var0)))))) var2 var0 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap)) (or (not (inv_main20 var3 var1 var0 var2)) (inv_main7 (write var3 var0 (O_TSLL (TSLL (next (getTSLL (read var3 var0))) 1))) var1 var0 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap)) (or (not (inv_main21 var3 var1 var0 var2)) (inv_main7 (write var3 var0 (O_TSLL (TSLL (next (getTSLL (read var3 var0))) 0))) var1 var0 var2))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Heap)) (or (not (and (inv_main4 var3 var2) (and (= var1 (write var3 var2 (O_TSLL (TSLL (next (getTSLL (read var3 var2))) 0)))) (= var0 var2)))) (inv_main7 var1 var0 var0 0))))
(assert (forall ((var0 TSLL) (var1 Heap)) (or (not (inv_main2 var1)) (inv_main3 (newHeap (alloc var1 (O_TSLL var0))) (newAddr (alloc var1 (O_TSLL var0)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Int) (var4 Addr) (var5 Addr) (var6 Int) (var7 Addr) (var8 Heap)) (or (not (and (inv_main11 var8 var2 var0 var6) (and (and (and (and (= var1 var8) (= var4 var2)) (= var5 var0)) (= var3 var6)) (= var7 (next (getTSLL (read var8 var0))))))) (inv_main13 var1 var4 var7 var3))))
(assert (forall ((var0 Addr) (var1 TSLL) (var2 Addr) (var3 Int) (var4 Heap) (var5 Int)) (or (not (and (inv_main7 var4 var2 var0 var3) (or (not (= var5 0)) (= var3 0)))) (inv_main12 (newHeap (alloc var4 (O_TSLL var1))) var2 var0 var3 (newAddr (alloc var4 (O_TSLL var1)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Int) (var9 Int) (var10 Heap)) (or (not (and (inv_main62 var10 var2 var1 var9 var6) (and (= var0 0) (and (= var8 0) (and (and (and (and (and (= var7 var10) (= var3 var2)) (= var5 var1)) (= var0 var9)) (= var4 var6)) (= var8 (data (getTSLL (read var10 var1))))))))) (inv_main70 var7 var3 var5 var0 var4))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main3 var1 var0) (not (is-O_TSLL (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main4 var1 var0) (not (is-O_TSLL (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap)) (not (and (inv_main12 var4 var2 var0 var3 var1) (not (is-O_TSLL (read var4 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap)) (not (and (inv_main11 var3 var1 var0 var2) (not (is-O_TSLL (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap)) (not (and (inv_main13 var3 var1 var0 var2) (not (is-O_TSLL (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap)) (not (and (inv_main20 var3 var1 var0 var2) (not (is-O_TSLL (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap)) (not (and (inv_main21 var3 var1 var0 var2) (not (is-O_TSLL (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap)) (not (inv_main25 var3 var1 var0 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap)) (not (and (inv_main28 var3 var1 var0 var2) (not (is-O_TSLL (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap) (var4 Addr)) (not (and (inv_main31 var3 var1 var0 var2 var4) (and (not (= var4 nullAddr)) (not (is-O_TSLL (read var3 var0))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap) (var4 Addr)) (not (and (inv_main31 var3 var1 var0 var2 var4) (and (not (= var4 nullAddr)) (not (is-O_TSLL (read var3 (next (getTSLL (read var3 var0)))))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap)) (not (and (inv_main30 var3 var1 var0 var2) (not (is-O_TSLL (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap)) (not (and (inv_main29 var3 var1 var0 var2) (not (is-O_TSLL (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap)) (not (and (inv_main36 var3 var1 var0 var2) (not (is-O_TSLL (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap)) (not (and (inv_main40 var3 var1 var0 var2) (not (is-O_TSLL (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap)) (not (inv_main43 var3 var1 var0 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap)) (not (and (inv_main47 var4 var1 var0 var3 var2) (not (is-O_TSLL (read var4 var2)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap)) (not (and (inv_main48 var4 var1 var0 var3 var2) (not (is-O_TSLL (read var4 var2)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap)) (not (and (inv_main49 var4 var1 var0 var3 var2) (not (is-O_TSLL (read var4 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap)) (not (and (inv_main51 var4 var1 var0 var3 var2) (not (is-O_TSLL (read var4 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap)) (not (and (inv_main52 var4 var1 var0 var3 var2) (not (is-O_TSLL (read var4 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap)) (not (and (inv_main55 var5 var1 var0 var4 var3 var2) (not (is-O_TSLL (read var5 var3)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap)) (not (and (inv_main54 var4 var1 var0 var3 var2) (not (is-O_TSLL (read var4 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap)) (not (and (inv_main57 var4 var1 var0 var3 var2) (and (not (= var0 nullAddr)) (not (is-O_TSLL (read var4 var0))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap)) (not (and (inv_main59 var4 var1 var0 var3 var2) (not (is-O_TSLL (read var4 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap)) (not (and (inv_main62 var4 var1 var0 var3 var2) (not (is-O_TSLL (read var4 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap)) (not (inv_main66 var4 var1 var0 var3 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap)) (not (inv_main72 var4 var1 var0 var3 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap)) (not (and (inv_main70 var4 var1 var0 var3 var2) (not (is-O_TSLL (read var4 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap)) (not (and (inv_main77 var4 var1 var0 var3 var2) (not (is-O_TSLL (read var4 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap)) (not (and (inv_main78 var4 var1 var0 var3 var2) (not (is-O_TSLL (read var4 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap)) (not (inv_main82 var4 var1 var0 var3 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap)) (not (inv_main88 var4 var1 var0 var3 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap)) (not (and (inv_main86 var4 var1 var0 var3 var2) (not (is-O_TSLL (read var4 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap)) (not (and (inv_main95 var4 var1 var0 var3 var2) (not (is-O_TSLL (read var4 var0)))))))
(check-sat)
