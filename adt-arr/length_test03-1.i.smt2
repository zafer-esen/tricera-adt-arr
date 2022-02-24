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
(declare-datatypes ((HeapObject 0) (node_t 0) (list_t 0))
                   (((O_Int (getInt Int)) (O_Addr (getAddr Addr)) (O_node_t (getnode_t node_t)) (O_list_t (getlist_t list_t)) (defObj))
                   ((node_t (data Int) (prev Addr) (next Addr)))
                   ((list_t (first Addr) (last Addr)))))
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
(declare-fun inv_main17 (Heap Addr Addr Int Int Addr Int Addr) Bool)
(declare-fun inv_main18 (Heap Addr Addr Int Int Addr Int Addr) Bool)
(declare-fun inv_main19 (Heap Addr Addr Int Int Addr Int Addr) Bool)
(declare-fun inv_main2 (Heap) Bool)
(declare-fun inv_main20 (Heap Addr Addr Int Int Addr Int Addr) Bool)
(declare-fun inv_main22 (Heap Addr Addr Int Int Addr Int Addr Addr) Bool)
(declare-fun inv_main25 (Heap Addr Addr Int Int Addr Int Addr) Bool)
(declare-fun inv_main26 (Heap Addr Addr Int Int Addr Int Addr) Bool)
(declare-fun inv_main27 (Heap Addr Addr Int Int Addr Int Addr) Bool)
(declare-fun inv_main29 (Heap Addr Addr Int Int Addr Int Addr) Bool)
(declare-fun inv_main3 (Heap Addr) Bool)
(declare-fun inv_main30 (Heap Addr Addr Int Int Addr Int Addr Addr) Bool)
(declare-fun inv_main31 (Heap Addr Addr Int Int Addr Int Addr) Bool)
(declare-fun inv_main32 (Heap Addr Addr Int Int Addr Int Addr) Bool)
(declare-fun inv_main36 (Heap Addr Addr Int Int Int) Bool)
(declare-fun inv_main37 (Heap Addr Addr Int Int Int) Bool)
(declare-fun inv_main4 (Heap Addr) Bool)
(declare-fun inv_main45 (Heap Addr Addr Int Int Int Int Addr Int Addr) Bool)
(declare-fun inv_main46 (Heap Addr Addr Int Int Int Int Addr Int Addr) Bool)
(declare-fun inv_main47 (Heap Addr Addr Int Int Int Int Addr Int Addr) Bool)
(declare-fun inv_main48 (Heap Addr Addr Int Int Int Int Addr Int Addr) Bool)
(declare-fun inv_main50 (Heap Addr Addr Int Int Int Int Addr Int Addr Addr) Bool)
(declare-fun inv_main53 (Heap Addr Addr Int Int Int Int Addr Int Addr) Bool)
(declare-fun inv_main54 (Heap Addr Addr Int Int Int Int Addr Int Addr) Bool)
(declare-fun inv_main55 (Heap Addr Addr Int Int Int Int Addr Int Addr) Bool)
(declare-fun inv_main57 (Heap Addr Addr Int Int Int Int Addr Int Addr) Bool)
(declare-fun inv_main58 (Heap Addr Addr Int Int Int Int Addr Int Addr Addr) Bool)
(declare-fun inv_main59 (Heap Addr Addr Int Int Int Int Addr Int Addr) Bool)
(declare-fun inv_main6 (Heap Addr Addr) Bool)
(declare-fun inv_main60 (Heap Addr Addr Int Int Int Int Addr Int Addr) Bool)
(declare-fun inv_main61 (Heap Addr Addr Int Int Int Addr) Bool)
(declare-fun inv_main63 (Heap Addr Addr Int Int Int Addr Addr) Bool)
(declare-fun inv_main64 (Heap Addr Addr Int Int Int Addr Addr) Bool)
(declare-fun inv_main68 (Heap Addr Addr Int Int Int Addr Addr) Bool)
(declare-fun inv_main7 (Heap Addr Addr) Bool)
(declare-fun inv_main73 (Heap Addr Addr Int Int Int Addr Addr Addr) Bool)
(assert (inv_main2 emptyHeap))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Int) (var7 Int)) (or (not (inv_main18 var5 var0 var1 var2 var6 var4 var7 var3)) (inv_main22 var5 var0 var1 var2 var6 var4 var7 var3 (first (getlist_t (read var5 var4)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap) (var4 Addr) (var5 Int) (var6 Int) (var7 Int) (var8 Addr) (var9 Int)) (or (not (inv_main57 var3 var0 var1 var2 var7 var5 var6 var4 var9 var8)) (inv_main59 (write var3 var8 (O_node_t (node_t (data (getnode_t (read var3 var8))) (prev (getnode_t (read var3 var8))) nullAddr))) var0 var1 var2 var7 var5 var6 var4 var9 var8))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 node_t) (var3 Int) (var4 Heap) (var5 Int) (var6 Int) (var7 Int)) (or (not (and (inv_main37 var4 var0 var1 var3 var7 var6) (<= 0 (+ (+ 5 (* (- 1) var6)) (- 1))))) (inv_main45 (newHeap (alloc var4 (O_node_t var2))) var0 var1 var3 var7 var6 var5 var1 var5 (newAddr (alloc var4 (O_node_t var2)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Int) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Int) (var9 Heap) (var10 Int) (var11 Int) (var12 Int) (var13 Addr) (var14 Addr)) (or (not (and (inv_main61 var9 var6 var7 var0 var12 var3 var4) (and (= var1 nullAddr) (and (and (and (and (and (and (and (= var2 var9) (= var14 var6)) (= var13 var7)) (= var11 var0)) (= var10 var12)) (= var8 var3)) (= var1 var4)) (= var5 (next (getnode_t (read var9 var4)))))))) (inv_main63 var2 var14 var13 var11 var10 var8 var1 var5))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Addr) (var5 Int) (var6 Int) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Heap) (var13 Int) (var14 Addr) (var15 Addr) (var16 Heap) (var17 Heap) (var18 Int) (var19 Int) (var20 Addr) (var21 Addr) (var22 Int) (var23 Addr) (var24 Int)) (or (not (and (inv_main64 var16 var9 var10 var2 var22 var3 var8 var15) (and (= var1 nullAddr) (and (and (and (and (and (and (and (and (and (= var17 var16) (= var14 var9)) (= var20 var10)) (= var19 var2)) (= var13 var22)) (= var6 var3)) (= var4 var8)) (= var21 var15)) (= var7 (next (getnode_t (read var16 var8))))) (and (and (and (and (and (and (and (= var12 (write var17 var4 defObj)) (= var11 var14)) (= var23 var20)) (= var18 var19)) (= var5 var13)) (= var24 var6)) (= var0 var4)) (= var1 var7)))))) (inv_main63 var12 var11 var23 var18 var5 var24 var1 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap) (var4 Addr) (var5 Int) (var6 Int) (var7 Int) (var8 Addr) (var9 Int)) (or (not (inv_main59 var3 var0 var1 var2 var7 var5 var6 var4 var9 var8)) (inv_main60 (write var3 (last (getlist_t (read var3 var4))) (O_node_t (node_t (data (getnode_t (read var3 (last (getlist_t (read var3 var4)))))) (prev (getnode_t (read var3 (last (getlist_t (read var3 var4)))))) var8))) var0 var1 var2 var7 var5 var6 var4 var9 var8))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap) (var4 Addr) (var5 Int) (var6 Int) (var7 Int) (var8 Addr) (var9 Int)) (or (not (inv_main53 var3 var0 var1 var2 var7 var5 var6 var4 var9 var8)) (inv_main54 (write var3 var4 (O_list_t (list_t (first (getlist_t (read var3 var4))) var8))) var0 var1 var2 var7 var5 var6 var4 var9 var8))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap) (var4 Addr) (var5 Int) (var6 Int) (var7 Int) (var8 Addr) (var9 Int)) (or (not (inv_main47 var3 var0 var1 var2 var7 var5 var6 var4 var9 var8)) (inv_main58 var3 var0 var1 var2 var7 var5 var6 var4 var9 var8 (last (getlist_t (read var3 var4)))))))
(assert (forall ((var0 Addr) (var1 Heap)) (or (not (inv_main3 var1 var0)) (inv_main4 (write var1 var0 (O_list_t (list_t nullAddr (last (getlist_t (read var1 var0)))))) var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Int) (var7 Int)) (or (not (inv_main31 var5 var0 var1 var2 var6 var4 var7 var3)) (inv_main32 (write var5 (last (getlist_t (read var5 var4))) (O_node_t (node_t (data (getnode_t (read var5 (last (getlist_t (read var5 var4)))))) (prev (getnode_t (read var5 (last (getlist_t (read var5 var4)))))) var3))) var0 var1 var2 var6 var4 var7 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap) (var4 Addr) (var5 Int) (var6 Int) (var7 Addr) (var8 Int) (var9 Addr) (var10 Int)) (or (not (and (inv_main50 var3 var0 var1 var2 var8 var5 var6 var4 var10 var9 var7) (not (= var7 nullAddr)))) (inv_main47 var3 var0 var1 var2 var8 var5 var6 var4 var10 var9))))
(assert (forall ((var0 Int) (var1 Int) (var2 Heap) (var3 Addr) (var4 Int) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Int) (var9 Int) (var10 Heap) (var11 Addr) (var12 Addr) (var13 Int) (var14 Addr) (var15 Int) (var16 Int) (var17 Addr) (var18 Addr) (var19 Int) (var20 Addr) (var21 Addr) (var22 Int) (var23 Addr) (var24 Int) (var25 Addr) (var26 Int) (var27 Int) (var28 Int) (var29 Addr) (var30 Int) (var31 Addr) (var32 Int)) (or (not (and (inv_main50 var7 var21 var6 var1 var30 var13 var15 var29 var32 var31 var3) (and (and (= var28 0) (and (= var3 nullAddr) (and (and (and (and (and (and (and (and (and (and (= var2 var7) (= var18 var21)) (= var23 var6)) (= var22 var1)) (= var9 var30)) (= var8 var13)) (= var26 var15)) (= var5 var29)) (= var4 var32)) (= var14 var31)) (= var20 (last (getlist_t (read var7 var29))))))) (and (and (and (and (and (and (and (and (and (and (= var10 var2) (= var17 var18)) (= var25 var23)) (= var16 var22)) (= var24 var9)) (= var27 var8)) (= var19 var26)) (= var12 var5)) (= var0 var4)) (= var11 var14)) (or (and (= var20 nullAddr) (= var28 1)) (and (not (= var20 nullAddr)) (= var28 0))))))) (inv_main47 var10 var17 var25 var16 var24 var27 var19 var12 var0 var11))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Int) (var4 Addr) (var5 Int) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap) (var11 Addr) (var12 Heap) (var13 Int) (var14 Addr) (var15 Addr) (var16 Int)) (or (not (and (inv_main63 var12 var8 var9 var3 var16 var5 var6 var11) (and (and (and (and (and (and (and (and (= var10 var12) (= var7 var8)) (= var15 var9)) (= var0 var3)) (= var1 var16)) (= var13 var5)) (= var14 var6)) (= var4 var11)) (= var2 (last (getlist_t (read var12 var9))))))) (inv_main68 var10 var7 var15 var0 var1 var13 var2 var4))))
(assert (forall ((var0 Int) (var1 Heap) (var2 Int) (var3 Int) (var4 Int) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap) (var11 Int) (var12 Addr) (var13 Addr) (var14 Int)) (or (not (and (inv_main61 var10 var6 var7 var3 var14 var4 var5) (and (not (= var13 nullAddr)) (and (and (and (and (and (and (and (= var1 var10) (= var9 var6)) (= var12 var7)) (= var0 var3)) (= var2 var14)) (= var11 var4)) (= var13 var5)) (= var8 (next (getnode_t (read var10 var5)))))))) (inv_main64 var1 var9 var12 var0 var2 var11 var13 var8))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Addr) (var5 Int) (var6 Int) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Heap) (var13 Int) (var14 Addr) (var15 Addr) (var16 Heap) (var17 Heap) (var18 Int) (var19 Int) (var20 Addr) (var21 Addr) (var22 Int) (var23 Addr) (var24 Int)) (or (not (and (inv_main64 var16 var9 var10 var2 var22 var3 var8 var15) (and (not (= var1 nullAddr)) (and (and (and (and (and (and (and (and (and (= var17 var16) (= var14 var9)) (= var20 var10)) (= var19 var2)) (= var13 var22)) (= var6 var3)) (= var4 var8)) (= var21 var15)) (= var7 (next (getnode_t (read var16 var8))))) (and (and (and (and (and (and (and (= var12 (write var17 var4 defObj)) (= var11 var14)) (= var23 var20)) (= var18 var19)) (= var5 var13)) (= var24 var6)) (= var0 var4)) (= var1 var7)))))) (inv_main64 var12 var11 var23 var18 var5 var24 var1 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (inv_main6 var2 var0 var1)) (inv_main7 (write var2 var1 (O_list_t (list_t nullAddr (last (getlist_t (read var2 var1)))))) var0 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap) (var4 Addr) (var5 Int) (var6 Int) (var7 Int) (var8 Addr) (var9 Int)) (or (not (inv_main46 var3 var0 var1 var2 var7 var5 var6 var4 var9 var8)) (inv_main50 var3 var0 var1 var2 var7 var5 var6 var4 var9 var8 (first (getlist_t (read var3 var4)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Int) (var6 Addr) (var7 Addr) (var8 Int) (var9 Int) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Int) (var14 Int) (var15 Int) (var16 Heap) (var17 Addr) (var18 Addr) (var19 Heap) (var20 Heap) (var21 Int) (var22 Addr) (var23 Int) (var24 Addr) (var25 Addr) (var26 Addr)) (or (not (and (inv_main22 var19 var17 var18 var5 var23 var7 var14 var6 var22) (and (and (not (= var8 0)) (and (= var22 nullAddr) (and (and (and (and (and (and (and (and (= var16 var19) (= var3 var17)) (= var24 var18)) (= var21 var5)) (= var0 var23)) (= var25 var7)) (= var13 var14)) (= var10 var6)) (= var2 (last (getlist_t (read var19 var7))))))) (and (and (and (and (and (and (and (and (= var20 var16) (= var12 var3)) (= var1 var24)) (= var9 var21)) (= var15 var0)) (= var26 var25)) (= var4 var13)) (= var11 var10)) (or (and (= var2 nullAddr) (= var8 1)) (and (not (= var2 nullAddr)) (= var8 0))))))) (inv_main20 var20 var12 var1 var9 var15 var26 var4 var11))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Int) (var7 Int)) (or (not (inv_main17 var5 var0 var1 var2 var6 var4 var7 var3)) (inv_main18 (write var5 var3 (O_node_t (node_t var7 (prev (getnode_t (read var5 var3))) (next (getnode_t (read var5 var3)))))) var0 var1 var2 var6 var4 var7 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap) (var4 Addr) (var5 Int) (var6 Addr) (var7 Int) (var8 Int) (var9 Addr) (var10 Int)) (or (not (inv_main58 var3 var0 var1 var2 var8 var5 var7 var4 var10 var9 var6)) (inv_main57 (write var3 var9 (O_node_t (node_t (data (getnode_t (read var3 var9))) var6 (next (getnode_t (read var3 var9)))))) var0 var1 var2 var8 var5 var7 var4 var10 var9))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap) (var4 Addr) (var5 Int) (var6 Int) (var7 Int) (var8 Addr) (var9 Int)) (or (not (inv_main48 var3 var0 var1 var2 var7 var5 var6 var4 var9 var8)) (inv_main53 (write var3 var4 (O_list_t (list_t var8 (last (getlist_t (read var3 var4)))))) var0 var1 var2 var7 var5 var6 var4 var9 var8))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 node_t) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Int) (var9 Int) (var10 Int) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Int) (var15 Addr) (var16 Heap) (var17 Int) (var18 Int)) (or (not (and (inv_main27 var16 var12 var13 var2 var17 var5 var9 var4) (and (not (= var1 0)) (and (and (and (and (and (and (and (= var7 (write var16 var4 (O_node_t (node_t (data (getnode_t (read var16 var4))) (prev (getnode_t (read var16 var4))) nullAddr)))) (= var6 var12)) (= var15 var13)) (= var8 var2)) (= var10 var17)) (= var0 var5)) (= var14 var9)) (= var11 var4))))) (inv_main17 (newHeap (alloc var7 (O_node_t var3))) var6 var15 var8 var18 var6 var18 (newAddr (alloc var7 (O_node_t var3)))))))
(assert (forall ((var0 node_t) (var1 Int) (var2 Int) (var3 Int) (var4 Addr) (var5 Addr) (var6 Int) (var7 Int) (var8 Int) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Heap) (var14 Int) (var15 Int) (var16 Addr) (var17 Heap)) (or (not (and (inv_main32 var13 var11 var12 var2 var15 var5 var7 var4) (and (not (= var8 0)) (and (and (and (and (and (and (= var17 (write var13 var5 (O_list_t (list_t (first (getlist_t (read var13 var5))) var4)))) (= var16 var11)) (= var9 var12)) (= var1 var2)) (= var14 var15)) (= var10 var5)) (= var6 var7))))) (inv_main17 (newHeap (alloc var17 (O_node_t var0))) var16 var9 var1 var3 var16 var3 (newAddr (alloc var17 (O_node_t var0)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 node_t) (var6 Addr) (var7 Int) (var8 Heap)) (or (not (and (inv_main7 var4 var1 var2) (and (and (= var8 (write var4 var2 (O_list_t (list_t (first (getlist_t (read var4 var2))) nullAddr)))) (= var6 var1)) (= var3 var2)))) (inv_main17 (newHeap (alloc var8 (O_node_t var5))) var6 var3 var0 var7 var6 var7 (newAddr (alloc var8 (O_node_t var5)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Int) (var9 Heap) (var10 Addr) (var11 Heap) (var12 Addr) (var13 Int) (var14 Addr) (var15 Addr) (var16 Addr)) (or (not (and (inv_main68 var11 var6 var7 var2 var13 var4 var5 var10) (and (and (and (and (and (and (and (and (= var9 var11) (= var15 var6)) (= var14 var7)) (= var3 var2)) (= var0 var13)) (= var8 var4)) (= var12 var5)) (= var1 var10)) (= var16 (prev (getnode_t (read var11 var5))))))) (inv_main73 var9 var15 var14 var3 var0 0 var12 var1 var16))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Heap) (var4 Int) (var5 Int) (var6 Addr) (var7 Addr) (var8 Int) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Heap) (var13 Int) (var14 Addr) (var15 Int) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Int) (var20 Addr) (var21 Addr) (var22 Heap) (var23 Addr) (var24 Addr) (var25 Addr) (var26 Addr) (var27 Int)) (or (not (and (inv_main73 var12 var23 var9 var2 var27 var19 var21 var11 var18) (and (<= 0 (+ (+ 5 (* (- 1) (+ var4 1))) (- 1))) (and (and (and (and (and (and (and (and (and (and (= var22 var12) (= var17 var23)) (= var20 var9)) (= var8 var2)) (= var13 var27)) (= var5 var19)) (= var25 var21)) (= var16 var11)) (= var24 var18)) (= var14 (prev (getnode_t (read var12 var21))))) (and (and (and (and (and (and (and (and (= var3 (write var22 var25 defObj)) (= var7 var17)) (= var0 var20)) (= var15 var8)) (= var1 var13)) (= var4 var5)) (= var26 var25)) (= var10 var16)) (= var6 var14)))))) (inv_main73 var3 var7 var0 var15 var1 (+ var4 1) var6 var10 var6))))
(assert (forall ((var0 Heap) (var1 list_t)) (or (not (inv_main2 var0)) (inv_main3 (newHeap (alloc var0 (O_list_t var1))) (newAddr (alloc var0 (O_list_t var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Int) (var8 Int)) (or (not (inv_main30 var6 var0 var1 var3 var7 var5 var8 var4 var2)) (inv_main29 (write var6 var4 (O_node_t (node_t (data (getnode_t (read var6 var4))) var2 (next (getnode_t (read var6 var4)))))) var0 var1 var3 var7 var5 var8 var4))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Int) (var7 Int)) (or (not (inv_main29 var5 var0 var1 var2 var6 var4 var7 var3)) (inv_main31 (write var5 var3 (O_node_t (node_t (data (getnode_t (read var5 var3))) (prev (getnode_t (read var5 var3))) nullAddr))) var0 var1 var2 var6 var4 var7 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Int) (var7 Int)) (or (not (inv_main19 var5 var0 var1 var2 var6 var4 var7 var3)) (inv_main30 var5 var0 var1 var2 var6 var4 var7 var3 (last (getlist_t (read var5 var4)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Int) (var7 Int)) (or (not (inv_main25 var5 var0 var1 var2 var6 var4 var7 var3)) (inv_main26 (write var5 var4 (O_list_t (list_t (first (getlist_t (read var5 var4))) var3))) var0 var1 var2 var6 var4 var7 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap) (var4 Int) (var5 Int)) (or (not (and (inv_main37 var3 var0 var1 var2 var5 var4) (not (<= 0 (+ (+ 5 (* (- 1) var4)) (- 1)))))) (inv_main36 var3 var0 var1 var2 var5 var4))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Int) (var5 Int) (var6 Int) (var7 Int) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Heap) (var14 Addr) (var15 Int) (var16 Heap) (var17 Int) (var18 Addr) (var19 Int)) (or (not (and (inv_main55 var13 var11 var12 var1 var17 var5 var6 var14 var19 var18) (and (and (and (and (and (and (and (and (and (= var16 (write var13 var18 (O_node_t (node_t (data (getnode_t (read var13 var18))) (prev (getnode_t (read var13 var18))) nullAddr)))) (= var9 var11)) (= var3 var12)) (= var2 var1)) (= var15 var17)) (= var0 var5)) (= var4 var6)) (= var8 var14)) (= var7 var19)) (= var10 var18)))) (inv_main37 var16 var9 var3 var2 var15 (+ var0 1)))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Int) (var6 Int) (var7 Int) (var8 Heap) (var9 Int) (var10 Int) (var11 Addr) (var12 Addr) (var13 Int) (var14 Heap) (var15 Addr) (var16 Int) (var17 Addr) (var18 Int)) (or (not (and (inv_main60 var14 var11 var12 var4 var16 var6 var7 var15 var18 var17) (and (and (and (and (and (and (and (and (= var8 (write var14 var15 (O_list_t (list_t (first (getlist_t (read var14 var15))) var17)))) (= var3 var11)) (= var2 var12)) (= var13 var4)) (= var10 var16)) (= var9 var6)) (= var0 var7)) (= var1 var15)) (= var5 var18)))) (inv_main37 var8 var3 var2 var13 var10 (+ var9 1)))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Int) (var8 Int) (var9 Int) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Int) (var14 Addr) (var15 Heap) (var16 Int)) (or (not (and (inv_main27 var15 var11 var12 var2 var16 var4 var8 var3) (and (= var1 0) (and (and (and (and (and (and (and (= var6 (write var15 var3 (O_node_t (node_t (data (getnode_t (read var15 var3))) (prev (getnode_t (read var15 var3))) nullAddr)))) (= var5 var11)) (= var14 var12)) (= var7 var2)) (= var9 var16)) (= var0 var4)) (= var13 var8)) (= var10 var3))))) (inv_main37 var6 var5 var14 var7 5 0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Int) (var5 Int) (var6 Int) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Heap) (var12 Int) (var13 Int) (var14 Addr) (var15 Heap)) (or (not (and (inv_main32 var11 var9 var10 var1 var13 var3 var6 var2) (and (= var4 0) (and (and (and (and (and (and (= var15 (write var11 var3 (O_list_t (list_t (first (getlist_t (read var11 var3))) var2)))) (= var14 var9)) (= var7 var10)) (= var0 var1)) (= var12 var13)) (= var8 var3)) (= var5 var6))))) (inv_main37 var15 var14 var7 var0 5 0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap) (var4 Addr) (var5 Int) (var6 Int) (var7 Int) (var8 Addr) (var9 Int)) (or (not (inv_main54 var3 var0 var1 var2 var7 var5 var6 var4 var9 var8)) (inv_main55 (write var3 var8 (O_node_t (node_t (data (getnode_t (read var3 var8))) nullAddr (next (getnode_t (read var3 var8)))))) var0 var1 var2 var7 var5 var6 var4 var9 var8))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Int) (var7 Int)) (or (not (inv_main26 var5 var0 var1 var2 var6 var4 var7 var3)) (inv_main27 (write var5 var3 (O_node_t (node_t (data (getnode_t (read var5 var3))) nullAddr (next (getnode_t (read var5 var3)))))) var0 var1 var2 var6 var4 var7 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Int) (var8 Int)) (or (not (and (inv_main22 var5 var0 var1 var2 var7 var4 var8 var3 var6) (not (= var6 nullAddr)))) (inv_main19 var5 var0 var1 var2 var7 var4 var8 var3))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Addr) (var4 Int) (var5 Int) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Int) (var10 Int) (var11 Int) (var12 Addr) (var13 Heap) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Heap) (var18 Int) (var19 Addr) (var20 Addr) (var21 Int) (var22 Int) (var23 Addr) (var24 Addr) (var25 Addr) (var26 Heap)) (or (not (and (inv_main22 var17 var15 var16 var4 var21 var7 var11 var6 var20) (and (and (= var10 0) (and (= var20 nullAddr) (and (and (and (and (and (and (and (and (= var13 var17) (= var3 var15)) (= var23 var16)) (= var18 var4)) (= var0 var21)) (= var25 var7)) (= var9 var11)) (= var8 var6)) (= var1 (last (getlist_t (read var17 var7))))))) (and (and (and (and (and (and (and (and (= var26 var13) (= var12 var3)) (= var24 var23)) (= var5 var18)) (= var22 var0)) (= var19 var25)) (= var2 var9)) (= var14 var8)) (or (and (= var1 nullAddr) (= var10 1)) (and (not (= var1 nullAddr)) (= var10 0))))))) (inv_main19 var26 var12 var24 var5 var22 var19 var2 var14))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Int) (var7 Int)) (or (not (inv_main20 var5 var0 var1 var2 var6 var4 var7 var3)) (inv_main25 (write var5 var4 (O_list_t (list_t var3 (last (getlist_t (read var5 var4)))))) var0 var1 var2 var6 var4 var7 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap) (var4 Addr) (var5 Int) (var6 Int) (var7 Int) (var8 Addr) (var9 Int)) (or (not (inv_main45 var3 var0 var1 var2 var7 var5 var6 var4 var9 var8)) (inv_main46 (write var3 var8 (O_node_t (node_t var9 (prev (getnode_t (read var3 var8))) (next (getnode_t (read var3 var8)))))) var0 var1 var2 var7 var5 var6 var4 var9 var8))))
(assert (forall ((var0 Addr) (var1 list_t) (var2 Heap) (var3 Heap) (var4 Addr)) (or (not (and (inv_main4 var2 var0) (and (= var3 (write var2 var0 (O_list_t (list_t (first (getlist_t (read var2 var0))) nullAddr)))) (= var4 var0)))) (inv_main6 (newHeap (alloc var3 (O_list_t var1))) var4 (newAddr (alloc var3 (O_list_t var1)))))))
(assert (forall ((var0 Int) (var1 Int) (var2 Heap) (var3 Heap) (var4 Addr) (var5 Int) (var6 Addr) (var7 Int) (var8 Int) (var9 Addr) (var10 Addr) (var11 Heap) (var12 Int) (var13 Addr) (var14 Int) (var15 Int) (var16 Addr) (var17 Int) (var18 Int) (var19 Int) (var20 Addr) (var21 Int) (var22 Addr) (var23 Addr) (var24 Addr) (var25 Addr) (var26 Int) (var27 Addr) (var28 Int) (var29 Addr) (var30 Int) (var31 Addr) (var32 Int)) (or (not (and (inv_main50 var11 var25 var9 var0 var30 var19 var21 var29 var32 var31 var4) (and (and (not (= var15 0)) (and (= var4 nullAddr) (and (and (and (and (and (and (and (and (and (and (= var2 var11) (= var23 var25)) (= var27 var9)) (= var26 var0)) (= var14 var30)) (= var12 var19)) (= var28 var21)) (= var6 var29)) (= var5 var32)) (= var20 var31)) (= var24 (last (getlist_t (read var11 var29))))))) (and (and (and (and (and (and (and (and (and (and (= var3 var2) (= var16 var23)) (= var13 var27)) (= var7 var26)) (= var1 var14)) (= var8 var12)) (= var17 var28)) (= var10 var6)) (= var18 var5)) (= var22 var20)) (or (and (= var24 nullAddr) (= var15 1)) (and (not (= var24 nullAddr)) (= var15 0))))))) (inv_main48 var3 var16 var13 var7 var1 var8 var17 var10 var18 var22))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap) (var4 Int) (var5 Int)) (or (not (inv_main36 var3 var0 var1 var2 var5 var4)) (inv_main61 var3 var0 var1 var2 var5 var4 (first (getlist_t (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main3 var1 var0) (not (is-O_list_t (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main4 var1 var0) (not (is-O_list_t (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main6 var2 var0 var1) (not (is-O_list_t (read var2 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main7 var2 var0 var1) (not (is-O_list_t (read var2 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Int) (var7 Int)) (not (and (inv_main17 var5 var0 var1 var2 var6 var4 var7 var3) (not (is-O_node_t (read var5 var3)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Int) (var7 Int)) (not (and (inv_main18 var5 var0 var1 var2 var6 var4 var7 var3) (not (is-O_list_t (read var5 var4)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Int) (var8 Int)) (not (and (inv_main22 var5 var0 var1 var2 var7 var4 var8 var3 var6) (and (= var6 nullAddr) (not (is-O_list_t (read var5 var4))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Int) (var7 Int)) (not (and (inv_main20 var5 var0 var1 var2 var6 var4 var7 var3) (not (is-O_list_t (read var5 var4)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Int) (var7 Int)) (not (and (inv_main25 var5 var0 var1 var2 var6 var4 var7 var3) (not (is-O_list_t (read var5 var4)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Int) (var7 Int)) (not (and (inv_main26 var5 var0 var1 var2 var6 var4 var7 var3) (not (is-O_node_t (read var5 var3)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Int) (var7 Int)) (not (and (inv_main27 var5 var0 var1 var2 var6 var4 var7 var3) (not (is-O_node_t (read var5 var3)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Int) (var7 Int)) (not (and (inv_main19 var5 var0 var1 var2 var6 var4 var7 var3) (not (is-O_list_t (read var5 var4)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Int) (var8 Int)) (not (and (inv_main30 var6 var0 var1 var3 var7 var5 var8 var4 var2) (not (is-O_node_t (read var6 var4)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Int) (var7 Int)) (not (and (inv_main29 var5 var0 var1 var2 var6 var4 var7 var3) (not (is-O_node_t (read var5 var3)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Int) (var7 Int)) (not (and (inv_main31 var5 var0 var1 var2 var6 var4 var7 var3) (not (is-O_list_t (read var5 var4)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Int) (var7 Int)) (not (and (inv_main31 var5 var0 var1 var2 var6 var4 var7 var3) (not (is-O_node_t (read var5 (last (getlist_t (read var5 var4))))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Int) (var7 Int)) (not (and (inv_main32 var5 var0 var1 var2 var6 var4 var7 var3) (not (is-O_list_t (read var5 var4)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap) (var4 Addr) (var5 Int) (var6 Int) (var7 Int) (var8 Addr) (var9 Int)) (not (and (inv_main45 var3 var0 var1 var2 var7 var5 var6 var4 var9 var8) (not (is-O_node_t (read var3 var8)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap) (var4 Addr) (var5 Int) (var6 Int) (var7 Int) (var8 Addr) (var9 Int)) (not (and (inv_main46 var3 var0 var1 var2 var7 var5 var6 var4 var9 var8) (not (is-O_list_t (read var3 var4)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap) (var4 Addr) (var5 Int) (var6 Int) (var7 Addr) (var8 Int) (var9 Addr) (var10 Int)) (not (and (inv_main50 var3 var0 var1 var2 var8 var5 var6 var4 var10 var9 var7) (and (= var7 nullAddr) (not (is-O_list_t (read var3 var4))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap) (var4 Addr) (var5 Int) (var6 Int) (var7 Int) (var8 Addr) (var9 Int)) (not (and (inv_main48 var3 var0 var1 var2 var7 var5 var6 var4 var9 var8) (not (is-O_list_t (read var3 var4)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap) (var4 Addr) (var5 Int) (var6 Int) (var7 Int) (var8 Addr) (var9 Int)) (not (and (inv_main53 var3 var0 var1 var2 var7 var5 var6 var4 var9 var8) (not (is-O_list_t (read var3 var4)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap) (var4 Addr) (var5 Int) (var6 Int) (var7 Int) (var8 Addr) (var9 Int)) (not (and (inv_main54 var3 var0 var1 var2 var7 var5 var6 var4 var9 var8) (not (is-O_node_t (read var3 var8)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap) (var4 Addr) (var5 Int) (var6 Int) (var7 Int) (var8 Addr) (var9 Int)) (not (and (inv_main55 var3 var0 var1 var2 var7 var5 var6 var4 var9 var8) (not (is-O_node_t (read var3 var8)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap) (var4 Addr) (var5 Int) (var6 Int) (var7 Int) (var8 Addr) (var9 Int)) (not (and (inv_main47 var3 var0 var1 var2 var7 var5 var6 var4 var9 var8) (not (is-O_list_t (read var3 var4)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap) (var4 Addr) (var5 Int) (var6 Addr) (var7 Int) (var8 Int) (var9 Addr) (var10 Int)) (not (and (inv_main58 var3 var0 var1 var2 var8 var5 var7 var4 var10 var9 var6) (not (is-O_node_t (read var3 var9)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap) (var4 Addr) (var5 Int) (var6 Int) (var7 Int) (var8 Addr) (var9 Int)) (not (and (inv_main57 var3 var0 var1 var2 var7 var5 var6 var4 var9 var8) (not (is-O_node_t (read var3 var8)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap) (var4 Addr) (var5 Int) (var6 Int) (var7 Int) (var8 Addr) (var9 Int)) (not (and (inv_main59 var3 var0 var1 var2 var7 var5 var6 var4 var9 var8) (not (is-O_list_t (read var3 var4)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap) (var4 Addr) (var5 Int) (var6 Int) (var7 Int) (var8 Addr) (var9 Int)) (not (and (inv_main59 var3 var0 var1 var2 var7 var5 var6 var4 var9 var8) (not (is-O_node_t (read var3 (last (getlist_t (read var3 var4))))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap) (var4 Addr) (var5 Int) (var6 Int) (var7 Int) (var8 Addr) (var9 Int)) (not (and (inv_main60 var3 var0 var1 var2 var7 var5 var6 var4 var9 var8) (not (is-O_list_t (read var3 var4)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap) (var4 Int) (var5 Int)) (not (and (inv_main36 var3 var0 var1 var2 var5 var4) (not (is-O_list_t (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap) (var5 Int) (var6 Int)) (not (and (inv_main61 var4 var1 var2 var3 var6 var5 var0) (not (is-O_node_t (read var4 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Addr) (var5 Heap) (var6 Int) (var7 Int)) (not (and (inv_main64 var5 var1 var2 var3 var7 var6 var0 var4) (not (is-O_node_t (read var5 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Addr) (var5 Heap) (var6 Int) (var7 Int)) (not (and (inv_main63 var5 var1 var2 var3 var7 var6 var0 var4) (not (is-O_list_t (read var5 var2)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Addr) (var5 Heap) (var6 Int) (var7 Int)) (not (and (inv_main68 var5 var1 var2 var3 var7 var6 var0 var4) (not (is-O_node_t (read var5 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Int) (var8 Int)) (not (and (inv_main73 var5 var1 var2 var3 var8 var7 var0 var4 var6) (not (is-O_node_t (read var5 var0)))))))
(check-sat)
