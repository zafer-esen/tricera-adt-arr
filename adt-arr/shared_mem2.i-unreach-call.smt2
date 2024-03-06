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
(declare-datatypes ((AddrRange 0))
                   (((AddrRange (AddrRangeStart Addr) (AddrRangeSize Int)))))

(declare-datatypes ((HeapObject 0) (mem 0) (list_node 0))
                   (((O_Int (getInt Int)) (O_UInt (getUInt Int)) (O_Addr (getAddr Addr)) (O_AddrRange (getAddrRange AddrRange)) (O_mem (getmem mem)) (O_list_node (getlist_node list_node)) (defObj))
                   ((mem (|mem::val| Int)))
                   ((list_node (|list_node::x| Int) (|list_node::mem| Addr) (|list_node::next| Addr)))))
(declare-datatypes ((BatchAllocResHeap 0) (AllocResHeap 0) (Heap 0))
                   (((BatchAllocResHeap   (newBatchHeap Heap) (newAddrRange AddrRange)))
                   ((AllocResHeap   (newHeap Heap) (newAddr Addr)))
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
(declare-fun inv_main577_5 (Heap) Bool)
(declare-fun inv_main583_5 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main600_9 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main_11 (Heap Addr Addr Addr) Bool)
(assert (forall ((var0 Heap)) (or (not (= var0 emptyHeap)) (inv_main577_5 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Heap) (var9 Int) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Heap)) (or (not (and (inv_main_11 var13 var12 var11 var10) (and (and (not (= var9 100)) (and (and (and (and (= var8 var7) (= var6 var5)) (= var4 var3)) (= var2 var1)) (= var9 (|mem::val| (getmem (read var7 var5)))))) (and (not (<= 0 (+ (+ 100 (* (- 1) var0)) (- 1)))) (and (and (and (and (= var7 var13) (= var5 var12)) (= var3 var11)) (= var1 var10)) (= var0 (|mem::val| (getmem (read var13 var12))))))))) (inv_main600_9 var8 var6 var4 var2))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main583_5 var4 var3 var2 var1) (= var0 0))) (inv_main_11 var4 var3 var2 var2))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap) (var9 Heap) (var10 Int) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Heap) (var15 Int) (var16 Int) (var17 Int) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Heap) (var25 Heap) (var26 Addr) (var27 Addr) (var28 Addr) (var29 Addr) (var30 Addr) (var31 Addr) (var32 Addr) (var33 Heap) (var34 Heap) (var35 Addr) (var36 Addr) (var37 Addr) (var38 Heap)) (or (not (and (inv_main_11 var38 var37 var36 var35) (and (and (and (and (and (and (= var34 var33) (= var32 var31)) (= var30 var29)) (= var28 var27)) (= var26 (|list_node::next| (getlist_node (read var33 var27))))) (and (and (and (and (and (and (and (= var25 var24) (= var23 var22)) (= var21 var20)) (= var19 var18)) (= var17 var16)) (= var15 (|list_node::x| (getlist_node (read var24 var18))))) (and (and (and (and (= var24 var14) (= var22 var13)) (= var20 var12)) (= var18 var11)) (= var16 (|mem::val| (getmem (read var14 (|list_node::mem| (getlist_node (read var14 var11))))))))) (and (and (and (<= 0 (+ 100 (* (- 1) var10))) (and (and (and (and (= var9 var8) (= var7 var6)) (= var5 var4)) (= var3 var2)) (= var1 (|mem::val| (getmem (read var8 (|list_node::mem| (getlist_node (read var8 var2))))))))) (and (and (and (and (= var14 var9) (= var13 var7)) (= var12 var5)) (= var11 var3)) (= var10 (+ var1 (|list_node::x| (getlist_node (read var9 var3))))))) (and (<= 0 (+ (+ 100 (* (- 1) var0)) (- 1))) (and (and (and (and (= var8 var38) (= var6 var37)) (= var4 var36)) (= var2 var35)) (= var0 (|mem::val| (getmem (read var38 var37))))))))) (and (and (and (= var33 (write var25 (|list_node::mem| (getlist_node (read var25 var19))) (O_mem (mem (+ var17 var15))))) (= var31 var23)) (= var29 var21)) (= var27 var19))))) (inv_main_11 var34 var32 var30 var26))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap) (var9 Heap) (var10 Int) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Heap) (var19 Heap) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Heap)) (or (not (and (inv_main_11 var23 var22 var21 var20) (and (and (and (and (and (= var19 var18) (= var17 var16)) (= var15 var14)) (= var13 var12)) (= var11 (|list_node::next| (getlist_node (read var18 var12))))) (and (and (and (not (<= 0 (+ 100 (* (- 1) var10)))) (and (and (and (and (= var9 var8) (= var7 var6)) (= var5 var4)) (= var3 var2)) (= var1 (|mem::val| (getmem (read var8 (|list_node::mem| (getlist_node (read var8 var2))))))))) (and (and (and (and (= var18 var9) (= var16 var7)) (= var14 var5)) (= var12 var3)) (= var10 (+ var1 (|list_node::x| (getlist_node (read var9 var3))))))) (and (<= 0 (+ (+ 100 (* (- 1) var0)) (- 1))) (and (and (and (and (= var8 var23) (= var6 var22)) (= var4 var21)) (= var2 var20)) (= var0 (|mem::val| (getmem (read var23 var22)))))))))) (inv_main_11 var19 var17 var15 var11))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Addr) (var3 Int) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Int) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Heap) (var14 Addr) (var15 Int) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Heap) (var20 Addr) (var21 Int) (var22 Int) (var23 Addr) (var24 Addr) (var25 Addr) (var26 list_node) (var27 Heap) (var28 Addr) (var29 Addr) (var30 Addr) (var31 Heap)) (or (not (and (inv_main583_5 var31 var30 var29 var28) (and (and (and (and (and (and (and (and (and (and (and (= var27 (newHeap (alloc var31 (O_list_node var26)))) (= var25 var30)) (= var24 var29)) (= var23 var28)) (= var22 var21)) (= var20 (newAddr (alloc var31 (O_list_node var26))))) (and (and (and (and (and (= var19 (write var27 var20 (O_list_node (list_node var22 (|list_node::mem| (getlist_node (read var27 var20))) (|list_node::next| (getlist_node (read var27 var20))))))) (= var18 var25)) (= var17 var24)) (= var16 var23)) (= var15 var22)) (= var14 var20))) (and (and (and (and (and (= var13 (write var19 var14 (O_list_node (list_node (|list_node::x| (getlist_node (read var19 var14))) var18 (|list_node::next| (getlist_node (read var19 var14))))))) (= var12 var18)) (= var11 var17)) (= var10 var16)) (= var9 var15)) (= var8 var14))) (and (and (and (and (and (= var7 (write var13 var8 (O_list_node (list_node (|list_node::x| (getlist_node (read var13 var8))) (|list_node::mem| (getlist_node (read var13 var8))) var11)))) (= var6 var12)) (= var5 var11)) (= var4 var10)) (= var3 var9)) (= var2 var8))) (and (<= 0 (+ var21 (- 1))) (<= 0 (+ (+ 10 (* (- 1) var21)) (- 1))))) (not (= var1 0))) (= var0 (write var7 var4 (O_list_node (list_node (|list_node::x| (getlist_node (read var7 var4))) (|list_node::mem| (getlist_node (read var7 var4))) var2))))))) (inv_main583_5 var0 var6 var5 var4))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main583_5 var5 var4 var3 var2) (and (or (not (<= 0 (+ var1 (- 1)))) (not (<= 0 (+ (+ 10 (* (- 1) var1)) (- 1))))) (not (= var0 0))))) (inv_main583_5 var5 var4 var3 var2))))
(assert (forall ((var0 Addr) (var1 mem) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Heap) (var12 Addr) (var13 Addr) (var14 Addr) (var15 list_node) (var16 Heap) (var17 Heap) (var18 Heap)) (or (not (and (inv_main577_5 var18) (and (and (and (and (and (and (and (= var17 (newHeap (alloc var16 (O_list_node var15)))) (= var14 var13)) (= var12 (newAddr (alloc var16 (O_list_node var15))))) (and (and (= var11 (write var17 var12 (O_list_node (list_node 1 (|list_node::mem| (getlist_node (read var17 var12))) (|list_node::next| (getlist_node (read var17 var12))))))) (= var10 var14)) (= var9 var12))) (and (and (= var8 (write var11 var9 (O_list_node (list_node (|list_node::x| (getlist_node (read var11 var9))) var10 (|list_node::next| (getlist_node (read var11 var9))))))) (= var7 var10)) (= var6 var9))) (and (and (= var5 (write var8 var6 (O_list_node (list_node (|list_node::x| (getlist_node (read var8 var6))) (|list_node::mem| (getlist_node (read var8 var6))) var6)))) (= var4 var7)) (= var3 var6))) (and (= var2 (newHeap (alloc var18 (O_mem var1)))) (= var0 (newAddr (alloc var18 (O_mem var1)))))) (and (= var16 (write var2 var0 (O_mem (mem 0)))) (= var13 var0))))) (inv_main583_5 var5 var4 var3 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (inv_main600_9 var3 var2 var1 var0))))
(check-sat)
