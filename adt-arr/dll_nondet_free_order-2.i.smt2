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
                   ((node (next Addr) (prev Addr)))))
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
(declare-fun inv_main0 (Heap Int) Bool)
(declare-fun inv_main11 (Heap Int Int Addr Int) Bool)
(declare-fun inv_main14 (Heap Int Int Addr) Bool)
(declare-fun inv_main16 (Heap Int Int Addr Addr) Bool)
(declare-fun inv_main17 (Heap Int Int Addr Addr) Bool)
(declare-fun inv_main20 (Heap Int Int Addr Addr Addr) Bool)
(declare-fun inv_main23 (Heap Int Int Addr Addr Addr Int) Bool)
(declare-fun inv_main26 (Heap Int Int Addr Addr Addr) Bool)
(declare-fun inv_main29 (Heap Int Int Addr Addr) Bool)
(declare-fun inv_main3 (Heap Int) Bool)
(declare-fun inv_main33 (Heap Int Addr Addr) Bool)
(declare-fun inv_main36 (Heap Int Addr Addr Addr) Bool)
(declare-fun inv_main8 (Heap Int Int Addr) Bool)
(assert (forall ((var0 Heap)) (or (not (= var0 emptyHeap)) (inv_main3 var0 3))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap) (var5 Heap) (var6 node) (var7 Addr) (var8 Int) (var9 Addr) (var10 Addr) (var11 Int)) (or (not (and (inv_main16 var4 var8 var3 var1 var2) (and (and (not (= nullAddr var7)) (and (and (and (and (and (= var5 (newHeap (alloc var4 (O_node var6)))) (= var0 var8)) (= var11 var3)) (= var9 var1)) (= var10 var2)) (= var7 (newAddr (alloc var4 (O_node var6)))))) (<= 0 (+ (+ var3 (- 1)) (- 1)))))) (inv_main20 var5 var0 var11 var9 var10 var7))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Int) (var3 Addr)) (or (not (inv_main33 var0 var2 var1 var3)) (inv_main36 var0 var2 var1 var3 (prev (getnode (read var0 var3)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap) (var4 Int)) (or (not (inv_main17 var3 var4 var2 var0 var1)) (inv_main29 (write var3 var0 (O_node (node var1 (prev (getnode (read var3 var0)))))) var4 var2 var0 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Int) (var4 Addr) (var5 Int) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Int) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Heap) (var17 Int) (var18 Heap) (var19 Addr) (var20 Heap) (var21 Int) (var22 Heap) (var23 Addr) (var24 Addr) (var25 Addr) (var26 Int) (var27 Addr) (var28 Addr) (var29 Addr) (var30 Int) (var31 Addr)) (or (not (and (inv_main36 var16 var3 var19 var4 var13) (and (and (and (and (not (= var5 0)) (and (and (not (= var17 0)) (and (and (and (and (and (= var2 var16) (= var0 var3)) (= var9 var19)) (= var14 var4)) (= var23 var13)) (= var1 (next (getnode (read var16 var4)))))) (and (and (and (and (and (= var22 (write var2 var14 defObj)) (= var26 var0)) (= var25 var9)) (= var12 var14)) (= var10 var23)) (= var27 var1)))) (and (and (and (and (and (= var20 (write var22 var27 defObj)) (= var21 var26)) (= var31 var25)) (= var15 var12)) (= var24 var10)) (= var6 var27))) (and (and (and (= var18 (write var20 var24 defObj)) (= var11 var21)) (= var8 var31)) (= var28 var15))) (and (and (= var7 var18) (= var30 var11)) (= var29 nullAddr))))) (inv_main0 var7 0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Heap) (var5 Heap) (var6 Heap) (var7 Int) (var8 Addr) (var9 Addr) (var10 Int) (var11 Addr) (var12 Heap) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Heap) (var20 Int) (var21 Int) (var22 Addr) (var23 Addr) (var24 Addr) (var25 Heap) (var26 Addr) (var27 Addr) (var28 Int) (var29 Addr) (var30 Addr) (var31 Addr)) (or (not (and (inv_main36 var19 var7 var22 var9 var16) (and (and (and (and (= var10 0) (and (and (not (= var21 0)) (and (and (and (and (and (= var5 var19) (= var2 var7)) (= var13 var22)) (= var17 var9)) (= var26 var16)) (= var3 (next (getnode (read var19 var9)))))) (and (and (and (and (and (= var25 (write var5 var17 defObj)) (= var28 var2)) (= var27 var13)) (= var15 var17)) (= var14 var26)) (= var29 var3)))) (and (and (and (and (and (= var4 (write var25 var14 defObj)) (= var20 var28)) (= var24 var27)) (= var18 var15)) (= var8 var14)) (= var23 var29))) (and (and (and (= var12 (write var4 var23 defObj)) (= var0 var20)) (= var30 var24)) (= var11 var18))) (and (and (= var6 var12) (= var1 var0)) (= var31 nullAddr))))) (inv_main0 var6 0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Int) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Int) (var8 Int) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Int) (var15 Heap) (var16 Addr) (var17 Heap) (var18 Addr) (var19 Addr) (var20 Int) (var21 Heap) (var22 Heap) (var23 Heap) (var24 Addr) (var25 Addr) (var26 Addr) (var27 Addr) (var28 Addr) (var29 Int) (var30 Addr) (var31 Addr) (var32 Int)) (or (not (and (inv_main36 var23 var8 var24 var9 var18) (and (and (and (and (not (= var20 0)) (and (and (not (= var2 0)) (and (= var7 0) (and (and (and (and (and (= var6 var23) (= var3 var8)) (= var13 var24)) (= var19 var9)) (= var25 var18)) (= var4 (next (getnode (read var23 var9))))))) (and (and (and (and (and (= var17 (write var6 var4 defObj)) (= var14 var3)) (= var28 var13)) (= var11 var19)) (= var31 var25)) (= var30 var4)))) (and (and (and (and (and (= var15 (write var17 var11 defObj)) (= var29 var14)) (= var0 var28)) (= var5 var11)) (= var27 var31)) (= var16 var30))) (and (and (and (= var21 (write var15 var27 defObj)) (= var1 var29)) (= var26 var0)) (= var10 var5))) (and (and (= var22 var21) (= var32 var1)) (= var12 nullAddr))))) (inv_main0 var22 0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Addr) (var5 Heap) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Int) (var10 Int) (var11 Int) (var12 Heap) (var13 Addr) (var14 Int) (var15 Int) (var16 Heap) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Int) (var21 Heap) (var22 Addr) (var23 Addr) (var24 Addr) (var25 Heap) (var26 Addr) (var27 Addr) (var28 Addr) (var29 Addr) (var30 Addr) (var31 Addr) (var32 Addr)) (or (not (and (inv_main36 var25 var11 var27 var13 var22) (and (and (and (and (= var14 0) (and (and (not (= var2 0)) (and (= var10 0) (and (and (and (and (and (= var6 var25) (= var3 var11)) (= var19 var27)) (= var23 var13)) (= var28 var22)) (= var4 (next (getnode (read var25 var13))))))) (and (and (and (and (and (= var21 (write var6 var4 defObj)) (= var20 var3)) (= var29 var19)) (= var17 var23)) (= var32 var28)) (= var31 var4)))) (and (and (and (and (and (= var12 (write var21 var32 defObj)) (= var9 var20)) (= var30 var29)) (= var8 var17)) (= var26 var32)) (= var18 var31))) (and (and (and (= var16 (write var12 var8 defObj)) (= var0 var9)) (= var24 var30)) (= var7 var8))) (and (and (= var5 var16) (= var15 var0)) (= var1 nullAddr))))) (inv_main0 var5 0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Heap) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Int) (var9 Addr) (var10 Int) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Int) (var16 Int) (var17 Addr) (var18 Int) (var19 Heap) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Addr) (var25 Heap) (var26 Int)) (or (not (and (inv_main36 var3 var10 var9 var11 var23) (and (and (and (= var15 0) (and (and (= var18 0) (and (= var8 0) (and (and (and (and (and (= var4 var3) (= var1 var10)) (= var17 var9)) (= var24 var11)) (= var14 var23)) (= var2 (next (getnode (read var3 var11))))))) (and (and (and (and (and (= var7 (write var4 var14 defObj)) (= var26 var1)) (= var22 var17)) (= var13 var24)) (= var6 var14)) (= var12 var2)))) (and (and (and (= var19 (write var7 var13 defObj)) (= var16 var26)) (= var21 var22)) (= var20 var13))) (and (and (= var25 var19) (= var0 var16)) (= var5 nullAddr))))) (inv_main0 var25 0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Int) (var5 Heap) (var6 Int) (var7 Addr) (var8 Addr) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Int) (var14 Addr) (var15 Int) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Int) (var21 Int) (var22 Heap) (var23 Int) (var24 Addr) (var25 Heap) (var26 Int) (var27 Addr) (var28 Addr) (var29 Addr) (var30 Addr) (var31 Heap) (var32 Addr)) (or (not (and (inv_main36 var22 var6 var24 var8 var17) (and (and (and (and (not (= var23 0)) (and (and (= var15 0) (and (= var4 0) (and (and (and (and (and (= var2 var22) (= var0 var6)) (= var14 var24)) (= var18 var8)) (= var29 var17)) (= var1 (next (getnode (read var22 var8))))))) (and (and (and (and (and (= var5 (write var2 var29 defObj)) (= var21 var0)) (= var16 var14)) (= var11 var18)) (= var3 var29)) (= var12 var1)))) (and (and (and (and (and (= var25 (write var5 var11 defObj)) (= var20 var21)) (= var19 var16)) (= var27 var11)) (= var30 var3)) (= var28 var12))) (and (and (and (= var31 (write var25 var28 defObj)) (= var26 var20)) (= var7 var19)) (= var10 var27))) (and (and (= var9 var31) (= var13 var26)) (= var32 nullAddr))))) (inv_main0 var9 0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap) (var4 Int) (var5 Int) (var6 Addr)) (or (not (inv_main23 var3 var4 var2 var0 var1 var6 var5)) (inv_main23 var3 var4 var2 var0 var1 var6 var5))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Int) (var6 Heap) (var7 Heap) (var8 Int) (var9 Int) (var10 Addr) (var11 node)) (or (not (and (inv_main16 var7 var9 var5 var1 var2) (and (and (= nullAddr var4) (and (and (and (and (and (= var6 (newHeap (alloc var7 (O_node var11)))) (= var8 var9)) (= var0 var5)) (= var10 var1)) (= var3 var2)) (= var4 (newAddr (alloc var7 (O_node var11)))))) (<= 0 (+ (+ var5 (- 1)) (- 1)))))) (inv_main23 var6 var8 var0 var10 var3 var4 1))))
(assert (forall ((var0 Heap) (var1 Heap) (var2 Int) (var3 node) (var4 Int) (var5 Int) (var6 Addr)) (or (not (and (inv_main3 var1 var5) (and (not (= nullAddr var6)) (and (and (and (= var0 (newHeap (alloc var1 (O_node var3)))) (= var4 var5)) (= var2 var5)) (= var6 (newAddr (alloc var1 (O_node var3)))))))) (inv_main8 var0 var4 var2 var6))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap) (var4 Int) (var5 Addr)) (or (not (inv_main20 var3 var4 var2 var0 var1 var5)) (inv_main26 (write var3 var5 (O_node (node var1 (prev (getnode (read var3 var5)))))) var4 var2 var0 var1 var5))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap) (var4 Int)) (or (not (and (inv_main16 var3 var4 var2 var0 var1) (not (<= 0 (+ (+ var2 (- 1)) (- 1)))))) (inv_main17 var3 var4 var2 var0 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Heap) (var7 Heap) (var8 Int) (var9 Addr)) (or (not (and (inv_main29 var6 var8 var5 var1 var2) (and (and (and (and (= var7 (write var6 var2 (O_node (node (next (getnode (read var6 var2))) var1)))) (= var4 var8)) (= var3 var5)) (= var0 var1)) (= var9 var2)))) (inv_main33 var7 var4 var9 var9))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Heap) (var3 Int) (var4 Int)) (or (not (inv_main11 var2 var3 var1 var0 var4)) (inv_main11 var2 var3 var1 var0 var4))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Int) (var4 Heap) (var5 Int) (var6 node)) (or (not (and (inv_main3 var1 var3) (and (= nullAddr var0) (and (and (and (= var4 (newHeap (alloc var1 (O_node var6)))) (= var5 var3)) (= var2 var3)) (= var0 (newAddr (alloc var1 (O_node var6)))))))) (inv_main11 var4 var5 var2 var0 1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap) (var4 Heap) (var5 Int) (var6 Addr) (var7 Int) (var8 Addr) (var9 Int) (var10 Addr) (var11 Addr)) (or (not (and (inv_main26 var3 var7 var2 var0 var1 var11) (and (and (and (and (and (= var4 (write var3 var1 (O_node (node (next (getnode (read var3 var1))) var11)))) (= var5 var7)) (= var9 var2)) (= var8 var0)) (= var6 var1)) (= var10 var11)))) (inv_main16 var4 var5 (+ var9 (- 1)) var8 var10))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Heap) (var5 Int) (var6 Int) (var7 Heap)) (or (not (and (inv_main14 var4 var5 var2 var0) (and (and (and (= var7 (write var4 var0 (O_node (node (next (getnode (read var4 var0))) var0)))) (= var3 var5)) (= var6 var2)) (= var1 var0)))) (inv_main16 var7 var3 var6 var1 var1))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Heap) (var3 Int)) (or (not (inv_main8 var2 var3 var1 var0)) (inv_main14 (write var2 var0 (O_node (node var0 (prev (getnode (read var2 var0)))))) var3 var1 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Heap) (var3 Int)) (not (and (inv_main8 var2 var3 var1 var0) (not (is-O_node (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Heap) (var3 Int)) (not (and (inv_main14 var2 var3 var1 var0) (not (is-O_node (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap) (var4 Int) (var5 Addr)) (not (and (inv_main20 var3 var4 var2 var0 var1 var5) (not (is-O_node (read var3 var5)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap) (var4 Int) (var5 Addr)) (not (and (inv_main26 var3 var4 var2 var0 var1 var5) (not (is-O_node (read var3 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap) (var4 Int)) (not (and (inv_main17 var3 var4 var2 var0 var1) (not (is-O_node (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap) (var4 Int)) (not (and (inv_main29 var3 var4 var2 var0 var1) (not (is-O_node (read var3 var1)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Int) (var3 Addr)) (not (and (inv_main33 var0 var2 var1 var3) (not (is-O_node (read var0 var3)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr)) (not (and (inv_main36 var0 var2 var1 var4 var3) (not (is-O_node (read var0 var4)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Int)) (not (and (inv_main0 var0 var2) (not (= (read var0 var1) defObj))))))
(check-sat)
