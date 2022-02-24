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
                   ((node (h Int) (n Addr)))))
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
(declare-fun inv_main16 (Heap Int Addr Addr Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main17 (Heap Int Addr Addr Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main21 (Heap Int Addr Addr Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main22 (Heap Int Addr Addr Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main27 (Heap Int Addr Addr Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main3 (Heap Int) Bool)
(declare-fun inv_main30 (Heap Int Addr Addr Addr Addr Addr Addr Addr Int) Bool)
(declare-fun inv_main33 (Heap Int Addr Addr Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main35 (Heap Int Addr Addr Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main43 (Heap Int Addr Addr Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main47 (Heap Int Addr Addr Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main50 (Heap Int Addr Addr Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main51 (Heap Int Addr Addr Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main58 (Heap Int Addr Addr Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main59 (Heap Int Addr Addr Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main64 (Heap Int Addr Addr Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main66 (Heap Int Addr Addr Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main67 (Heap Int Addr Addr Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main72 (Heap Int Addr Addr Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main8 (Heap Int Addr Int) Bool)
(assert (forall ((var0 Heap)) (or (not (= var0 emptyHeap)) (inv_main3 var0 1))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Int) (var7 Addr) (var8 Addr)) (or (not (and (inv_main64 var0 var6 var2 var1 var4 var8 var7 var3 var5) (not (= var5 nullAddr)))) (inv_main66 var0 var6 var2 var1 var4 var8 var7 var3 var5))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Addr) (var6 Addr) (var7 Int) (var8 Addr) (var9 Addr)) (or (not (and (inv_main16 var0 var7 var2 var1 var5 var9 var8 var3 var6) (and (= var7 0) (not (= var4 0))))) (inv_main22 var0 var7 var2 var1 var5 var9 var8 var3 var6))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Addr) (var6 Addr) (var7 Int) (var8 Addr) (var9 Addr)) (or (not (and (inv_main16 var0 var7 var2 var1 var5 var9 var8 var3 var6) (and (not (= var7 0)) (not (= var4 0))))) (inv_main21 var0 var7 var2 var1 var5 var9 var8 var3 var6))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Int) (var7 Addr) (var8 Heap) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Int) (var17 Addr) (var18 Addr)) (or (not (and (inv_main43 var8 var6 var10 var1 var3 var17 var7 var11 var5) (and (not (= var2 3)) (and (and (and (and (and (and (and (and (and (= var9 var8) (= var16 var6)) (= var14 var10)) (= var18 var1)) (= var4 var3)) (= var15 var17)) (= var12 var7)) (= var13 var11)) (= var0 var5)) (= var2 (h (getnode (read var8 var5)))))))) (inv_main47 var9 var16 var14 var0 var4 var15 var12 var13 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Int) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap) (var11 Addr) (var12 Heap) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr)) (or (not (and (inv_main47 var12 var6 var13 var0 var4 var18 var8 var15 var5) (and (not (= var2 0)) (and (and (and (and (and (and (and (and (and (= var10 var12) (= var2 var6)) (= var11 var13)) (= var1 var0)) (= var14 var4)) (= var3 var18)) (= var9 var8)) (= var17 var15)) (= var7 var5)) (= var16 (n (getnode (read var12 var5)))))))) (inv_main50 var10 var2 var11 var1 var14 var3 var9 var17 var16))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Int) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Int) (var25 Heap) (var26 Int) (var27 Addr) (var28 Addr) (var29 Addr) (var30 Heap) (var31 Addr) (var32 Int) (var33 Addr) (var34 Int) (var35 Addr) (var36 Addr)) (or (not (and (inv_main35 var30 var26 var12 var20 var7 var19 var28 var31 var10) (and (and (and (not (= var32 3)) (and (and (and (and (and (and (and (and (and (= var25 var30) (= var24 var26)) (= var29 var12)) (= var21 var20)) (= var8 var7)) (= var3 var19)) (= var15 var28)) (= var17 var31)) (= var16 var10)) (= var32 (h (getnode (read var30 var12)))))) (and (and (and (and (and (and (and (and (= var2 var25) (= var34 1)) (= var23 var29)) (= var36 var21)) (= var13 nullAddr)) (= var18 var3)) (= var5 var15)) (= var11 var17)) (= var1 var16))) (and (and (and (and (and (and (and (and (= var4 var2) (= var6 var34)) (= var9 var23)) (= var14 var36)) (= var33 var13)) (= var27 nullAddr)) (= var22 var5)) (= var0 var11)) (= var35 var1))))) (inv_main43 var4 var6 var9 var14 var33 var27 var22 var0 var9))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Int) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Heap) (var15 Addr) (var16 Addr) (var17 Addr)) (or (not (and (inv_main50 var7 var5 var9 var1 var3 var17 var6 var10 var4) (and (and (and (and (and (and (and (and (= var14 (write var7 var1 (O_node (node (h (getnode (read var7 var1))) var3)))) (= var2 var5)) (= var12 var9)) (= var13 var1)) (= var0 var3)) (= var8 var17)) (= var15 var6)) (= var16 var10)) (= var11 var4)))) (inv_main43 var14 0 var12 var13 var13 var8 var15 var16 var11))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Int) (var10 Int) (var11 Addr) (var12 Heap) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr)) (or (not (and (inv_main51 var12 var9 var13 var1 var7 var16 var11 var14 var8) (and (and (and (and (and (and (and (and (= var5 (write var12 var1 (O_node (node (h (getnode (read var12 var1))) var16)))) (= var10 var9)) (= var0 var13)) (= var6 var1)) (= var17 var7)) (= var3 var16)) (= var4 var11)) (= var2 var14)) (= var15 var8)))) (inv_main43 var5 1 var0 var6 var17 var6 var4 var2 var15))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 node) (var15 Addr) (var16 Heap) (var17 Addr) (var18 Int) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Heap) (var24 Addr) (var25 Addr) (var26 Heap) (var27 Addr) (var28 Addr)) (or (not (and (inv_main21 var23 var18 var11 var15 var6 var13 var20 var24 var9) (and (and (not (= var12 nullAddr)) (and (and (and (and (and (and (and (and (and (= var16 (newHeap (alloc var26 (O_node var14)))) (= var3 0)) (= var17 var19)) (= var4 var7)) (= var5 var10)) (= var8 var28)) (= var1 var25)) (= var21 var22)) (= var2 var27)) (= var12 (newAddr (alloc var26 (O_node var14)))))) (and (and (and (and (and (and (and (and (= var26 (write var23 var9 (O_node (node 1 (n (getnode (read var23 var9))))))) (= var0 var18)) (= var19 var11)) (= var7 var15)) (= var10 var6)) (= var28 var13)) (= var25 var20)) (= var22 var24)) (= var27 var9))))) (inv_main27 var16 var3 var17 var12 var5 var8 var1 var21 var2))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Int) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Heap) (var15 Addr) (var16 Addr) (var17 Int) (var18 Addr) (var19 Heap) (var20 Addr) (var21 Heap) (var22 Addr) (var23 Addr) (var24 node) (var25 Addr) (var26 Addr) (var27 Addr) (var28 Addr)) (or (not (and (inv_main22 var21 var17 var7 var13 var4 var12 var20 var23 var6) (and (and (not (= var5 nullAddr)) (and (and (and (and (and (and (and (and (and (= var19 (newHeap (alloc var14 (O_node var24)))) (= var1 1)) (= var16 var9)) (= var11 var2)) (= var22 var0)) (= var15 var10)) (= var25 var8)) (= var18 var28)) (= var26 var27)) (= var5 (newAddr (alloc var14 (O_node var24)))))) (and (and (and (and (and (and (and (and (= var14 (write var21 var6 (O_node (node 2 (n (getnode (read var21 var6))))))) (= var3 var17)) (= var9 var7)) (= var2 var13)) (= var0 var4)) (= var10 var12)) (= var8 var20)) (= var28 var23)) (= var27 var6))))) (inv_main27 var19 var1 var16 var5 var22 var15 var25 var18 var26))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Int) (var6 Addr) (var7 Int) (var8 Addr) (var9 Addr)) (or (not (inv_main30 var0 var7 var2 var1 var4 var9 var8 var3 var6 var5)) (inv_main30 var0 var7 var2 var1 var4 var9 var8 var3 var6 var5))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Heap) (var12 Addr) (var13 Addr) (var14 Addr) (var15 node) (var16 Int) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Heap) (var22 Addr) (var23 Addr) (var24 Heap) (var25 Addr) (var26 Addr) (var27 Addr) (var28 Addr)) (or (not (and (inv_main21 var21 var16 var9 var13 var2 var12 var18 var22 var6) (and (and (= var19 nullAddr) (and (and (and (and (and (and (and (and (and (= var11 (newHeap (alloc var24 (O_node var15)))) (= var4 0)) (= var28 var17)) (= var25 var3)) (= var5 var7)) (= var8 var27)) (= var14 var23)) (= var1 var20)) (= var10 var26)) (= var19 (newAddr (alloc var24 (O_node var15)))))) (and (and (and (and (and (and (and (and (= var24 (write var21 var6 (O_node (node 1 (n (getnode (read var21 var6))))))) (= var0 var16)) (= var17 var9)) (= var3 var13)) (= var7 var2)) (= var27 var12)) (= var23 var18)) (= var20 var22)) (= var26 var6))))) (inv_main30 var11 var4 var28 var19 var5 var8 var14 var1 var10 1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Heap) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Heap) (var19 Addr) (var20 Int) (var21 Int) (var22 Addr) (var23 Heap) (var24 Addr) (var25 Addr) (var26 Addr) (var27 node) (var28 Addr)) (or (not (and (inv_main22 var23 var20 var7 var16 var3 var15 var22 var24 var4) (and (and (= var14 nullAddr) (and (and (and (and (and (and (and (and (and (= var12 (newHeap (alloc var18 (O_node var27)))) (= var21 1)) (= var19 var9)) (= var5 var1)) (= var11 var0)) (= var13 var10)) (= var25 var8)) (= var17 var28)) (= var6 var26)) (= var14 (newAddr (alloc var18 (O_node var27)))))) (and (and (and (and (and (and (and (and (= var18 (write var23 var4 (O_node (node 2 (n (getnode (read var23 var4))))))) (= var2 var20)) (= var9 var7)) (= var1 var16)) (= var0 var3)) (= var10 var15)) (= var8 var22)) (= var28 var24)) (= var26 var4))))) (inv_main30 var12 var21 var19 var14 var11 var13 var25 var17 var6 1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Int) (var8 Int) (var9 Addr) (var10 Heap) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr)) (or (not (and (inv_main66 var10 var7 var12 var1 var4 var18 var9 var13 var6) (and (= var8 2) (and (and (and (and (and (and (and (and (and (= var5 var10) (= var2 var7)) (= var3 var12)) (= var17 var1)) (= var14 var4)) (= var16 var18)) (= var11 var9)) (= var0 var13)) (= var15 var6)) (= var8 (h (getnode (read var10 var6)))))))) (inv_main67 var5 var2 var3 var17 var14 var16 var11 var0 var15))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Int) (var9 Addr) (var10 Int) (var11 Addr) (var12 Heap) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Heap) (var17 Addr) (var18 Addr)) (or (not (and (inv_main35 var12 var8 var13 var0 var4 var17 var9 var15 var7) (and (= var2 3) (and (and (and (and (and (and (and (and (and (= var16 var12) (= var10 var8)) (= var6 var13)) (= var3 var0)) (= var11 var4)) (= var5 var17)) (= var18 var9)) (= var1 var15)) (= var14 var7)) (= var2 (h (getnode (read var12 var13)))))))) (inv_main0 var16 0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Int) (var7 Addr) (var8 Addr)) (or (not (and (inv_main64 var0 var6 var2 var1 var4 var8 var7 var3 var5) (= var5 nullAddr))) (inv_main0 var0 0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Int) (var7 Addr) (var8 Addr)) (or (not (inv_main27 var0 var6 var2 var1 var4 var8 var7 var3 var5)) (inv_main33 (write var0 var5 (O_node (node (h (getnode (read var0 var5))) var1))) var6 var2 var1 var4 var8 var7 var3 var5))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Int) (var6 Int) (var7 Addr) (var8 Addr) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Heap) (var14 Addr) (var15 Addr) (var16 Int) (var17 Addr) (var18 Addr)) (or (not (and (inv_main58 var9 var5 var10 var0 var3 var17 var7 var12 var4) (and (not (= var16 1)) (and (and (and (and (and (and (and (and (and (= var13 var9) (= var6 var5)) (= var11 var10)) (= var14 var0)) (= var8 var3)) (= var1 var17)) (= var2 var7)) (= var18 var12)) (= var15 var4)) (= var16 (h (getnode (read var9 var4)))))))) (inv_main72 var13 var6 var11 var14 var8 var1 var2 var18 var15))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Int) (var10 Addr) (var11 Heap) (var12 Addr) (var13 Int) (var14 Addr) (var15 Addr) (var16 Int) (var17 Addr) (var18 Addr)) (or (not (and (inv_main66 var11 var9 var12 var2 var5 var18 var10 var14 var8) (and (not (= var13 2)) (and (and (and (and (and (and (and (and (and (= var3 var11) (= var16 var9)) (= var15 var12)) (= var0 var2)) (= var17 var5)) (= var7 var18)) (= var4 var10)) (= var1 var14)) (= var6 var8)) (= var13 (h (getnode (read var11 var8)))))))) (inv_main72 var3 var16 var15 var0 var17 var7 var4 var1 var6))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Int) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap) (var11 Addr) (var12 Heap) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr)) (or (not (and (inv_main47 var12 var6 var13 var0 var4 var18 var8 var15 var5) (and (= var2 0) (and (and (and (and (and (and (and (and (and (= var10 var12) (= var2 var6)) (= var11 var13)) (= var1 var0)) (= var14 var4)) (= var3 var18)) (= var9 var8)) (= var17 var15)) (= var7 var5)) (= var16 (n (getnode (read var12 var5)))))))) (inv_main51 var10 var2 var11 var1 var14 var3 var9 var17 var16))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Int) (var7 Addr) (var8 Addr)) (or (not (inv_main17 var0 var6 var2 var1 var4 var8 var7 var3 var5)) (inv_main35 (write var0 var5 (O_node (node 3 (n (getnode (read var0 var5)))))) var6 var2 var1 var4 var8 var7 var3 var5))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Int) (var6 Addr) (var7 Int) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Heap) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr)) (or (not (and (inv_main59 var11 var7 var13 var0 var4 var18 var8 var14 var6) (and (not (= var12 nullAddr)) (and (and (and (and (and (and (and (and (and (= var2 var11) (= var5 var7)) (= var10 var13)) (= var16 var0)) (= var3 var4)) (= var15 var18)) (= var1 var8)) (= var17 var14)) (= var9 var6)) (= var12 (n (getnode (read var11 var6)))))))) (inv_main58 var2 var5 var10 var16 var3 var15 var1 var17 var12))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Int) (var7 Addr) (var8 Int) (var9 Addr) (var10 Heap) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Heap) (var16 Int) (var17 Addr) (var18 Addr)) (or (not (and (inv_main43 var10 var8 var11 var0 var5 var17 var9 var12 var7) (and (not (= var14 nullAddr)) (and (= var16 3) (and (and (and (and (and (and (and (and (and (= var15 var10) (= var6 var8)) (= var3 var11)) (= var2 var0)) (= var14 var5)) (= var1 var17)) (= var13 var9)) (= var4 var12)) (= var18 var7)) (= var16 (h (getnode (read var10 var7))))))))) (inv_main58 var15 var6 var3 var2 var14 var1 var13 var4 var14))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Int) (var7 Addr) (var8 Addr) (var9 Int) (var10 Heap) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Heap) (var18 Addr)) (or (not (and (inv_main33 var10 var6 var12 var0 var4 var18 var7 var14 var5) (and (and (and (and (and (and (and (and (and (= var17 var10) (= var9 var6)) (= var1 var12)) (= var2 var0)) (= var3 var4)) (= var8 var18)) (= var13 var7)) (= var11 var14)) (= var15 var5)) (= var16 (n (getnode (read var10 var5))))))) (inv_main16 var17 var9 var1 var2 var3 var8 var13 var11 var16))))
(assert (forall ((var0 Heap) (var1 Heap) (var2 Int) (var3 node) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Int) (var10 Addr)) (or (not (and (inv_main3 var0 var9) (and (not (= var5 nullAddr)) (and (and (= var1 (newHeap (alloc var0 (O_node var3)))) (= var2 var9)) (= var5 (newAddr (alloc var0 (O_node var3)))))))) (inv_main16 var1 var2 var5 var8 var6 var4 var10 var7 var5))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Addr) (var6 Addr) (var7 Int) (var8 Addr) (var9 Addr)) (or (not (and (inv_main16 var0 var7 var2 var1 var5 var9 var8 var3 var6) (= var4 0))) (inv_main17 var0 var7 var2 var1 var5 var9 var8 var3 var6))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Int) (var3 Int)) (or (not (inv_main8 var0 var3 var1 var2)) (inv_main8 var0 var3 var1 var2))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Heap) (var3 node) (var4 Int) (var5 Int)) (or (not (and (inv_main3 var0 var5) (and (= var1 nullAddr) (and (and (= var2 (newHeap (alloc var0 (O_node var3)))) (= var4 var5)) (= var1 (newAddr (alloc var0 (O_node var3)))))))) (inv_main8 var2 var4 var1 1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Int) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Heap) (var12 Addr) (var13 Int) (var14 Heap) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr)) (or (not (and (inv_main58 var14 var7 var15 var0 var5 var18 var10 var16 var6) (and (= var13 1) (and (and (and (and (and (and (and (and (and (= var11 var14) (= var3 var7)) (= var2 var15)) (= var17 var0)) (= var1 var5)) (= var4 var18)) (= var9 var10)) (= var8 var16)) (= var12 var6)) (= var13 (h (getnode (read var14 var6)))))))) (inv_main59 var11 var3 var2 var17 var1 var4 var9 var8 var12))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Int) (var9 Addr) (var10 Addr) (var11 Heap) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr)) (or (not (and (inv_main67 var11 var8 var13 var2 var6 var18 var9 var15 var7) (and (and (and (and (and (and (and (and (and (= var4 var11) (= var3 var8)) (= var14 var13)) (= var12 var2)) (= var10 var6)) (= var0 var18)) (= var1 var9)) (= var5 var15)) (= var16 var7)) (= var17 (n (getnode (read var11 var7))))))) (inv_main64 var4 var3 var14 var12 var10 var0 var1 var5 var17))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Int) (var6 Addr) (var7 Int) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Heap) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr)) (or (not (and (inv_main59 var11 var7 var13 var0 var4 var18 var8 var14 var6) (and (= var12 nullAddr) (and (and (and (and (and (and (and (and (and (= var2 var11) (= var5 var7)) (= var10 var13)) (= var16 var0)) (= var3 var4)) (= var15 var18)) (= var1 var8)) (= var17 var14)) (= var9 var6)) (= var12 (n (getnode (read var11 var6)))))))) (inv_main64 var2 var5 var10 var16 var3 var15 var1 var17 var15))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Int) (var7 Addr) (var8 Int) (var9 Addr) (var10 Heap) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Heap) (var16 Int) (var17 Addr) (var18 Addr)) (or (not (and (inv_main43 var10 var8 var11 var0 var5 var17 var9 var12 var7) (and (= var14 nullAddr) (and (= var16 3) (and (and (and (and (and (and (and (and (and (= var15 var10) (= var6 var8)) (= var3 var11)) (= var2 var0)) (= var14 var5)) (= var1 var17)) (= var13 var9)) (= var4 var12)) (= var18 var7)) (= var16 (h (getnode (read var10 var7))))))))) (inv_main64 var15 var6 var3 var2 var14 var1 var13 var4 var1))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Int) (var7 Addr) (var8 Addr)) (not (and (inv_main21 var0 var6 var2 var1 var4 var8 var7 var3 var5) (not (is-O_node (read var0 var5)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Int) (var7 Addr) (var8 Addr)) (not (and (inv_main22 var0 var6 var2 var1 var4 var8 var7 var3 var5) (not (is-O_node (read var0 var5)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Int) (var7 Addr) (var8 Addr)) (not (and (inv_main27 var0 var6 var2 var1 var4 var8 var7 var3 var5) (not (is-O_node (read var0 var5)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Int) (var7 Addr) (var8 Addr)) (not (and (inv_main33 var0 var6 var2 var1 var4 var8 var7 var3 var5) (not (is-O_node (read var0 var5)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Int) (var7 Addr) (var8 Addr)) (not (and (inv_main17 var0 var6 var2 var1 var4 var8 var7 var3 var5) (not (is-O_node (read var0 var5)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Int) (var7 Addr) (var8 Addr)) (not (and (inv_main35 var0 var6 var2 var1 var4 var8 var7 var3 var5) (not (is-O_node (read var0 var2)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Int) (var7 Addr) (var8 Addr)) (not (and (inv_main43 var0 var6 var2 var1 var4 var8 var7 var3 var5) (not (is-O_node (read var0 var5)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Int) (var7 Addr) (var8 Addr)) (not (and (inv_main47 var0 var6 var2 var1 var4 var8 var7 var3 var5) (not (is-O_node (read var0 var5)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Int) (var7 Addr) (var8 Addr)) (not (and (inv_main50 var0 var6 var2 var1 var4 var8 var7 var3 var5) (not (is-O_node (read var0 var1)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Int) (var7 Addr) (var8 Addr)) (not (and (inv_main51 var0 var6 var2 var1 var4 var8 var7 var3 var5) (not (is-O_node (read var0 var1)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Int) (var7 Addr) (var8 Addr)) (not (and (inv_main58 var0 var6 var2 var1 var4 var8 var7 var3 var5) (not (is-O_node (read var0 var5)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Int) (var7 Addr) (var8 Addr)) (not (and (inv_main59 var0 var6 var2 var1 var4 var8 var7 var3 var5) (not (is-O_node (read var0 var5)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Int) (var7 Addr) (var8 Addr)) (not (and (inv_main66 var0 var6 var2 var1 var4 var8 var7 var3 var5) (not (is-O_node (read var0 var5)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Int) (var7 Addr) (var8 Addr)) (not (and (inv_main67 var0 var6 var2 var1 var4 var8 var7 var3 var5) (not (is-O_node (read var0 var5)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Int) (var7 Addr) (var8 Addr)) (not (inv_main72 var0 var6 var2 var1 var4 var8 var7 var3 var5))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Addr)) (not (and (inv_main0 var0 var1) (not (= (read var0 var2) defObj))))))
(check-sat)
