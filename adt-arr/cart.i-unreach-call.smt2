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

(declare-datatypes ((HeapObject 0) (node 0))
                   (((O_Int (getInt Int)) (O_UInt (getUInt Int)) (O_Addr (getAddr Addr)) (O_AddrRange (getAddrRange AddrRange)) (O_node (getnode node)) (defObj))
                   ((node (|node::next| Addr) (|node::stock| Int) (|node::order| Int)))))
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
(declare-fun inv_main574_5 (Heap) Bool)
(declare-fun inv_main574_5_1 (Heap Addr) Bool)
(declare-fun inv_main584_5 (Heap Addr Addr) Bool)
(declare-fun inv_main595_13_18 (Heap Addr Addr) Bool)
(declare-fun inv_main_15 (Heap Addr Addr) Bool)
(assert (forall ((var0 Heap)) (or (not (= var0 emptyHeap)) (inv_main574_5 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Int) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main_15 var6 var5 var4) (and (and (<= 0 (+ (+ var3 (* (- 1) (|node::stock| (getnode (read var2 var1))))) (- 1))) (and (and (and (= var2 var6) (= var0 var5)) (= var1 var4)) (= var3 (|node::order| (getnode (read var6 var4)))))) (not (= var4 nullAddr))))) (inv_main595_13_18 var2 var0 var1))))
(assert (forall ((var0 Addr) (var1 Heap)) (or (not (and (inv_main574_5 var1) (= var0 nullAddr))) (inv_main574_5_1 var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Heap)) (or (not (and (inv_main574_5_1 var3 var2) (and (<= 0 (+ (* (- 1) var1) (- 1))) (not (= var0 0))))) (inv_main574_5_1 var3 var2))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Int) (var7 Addr) (var8 Heap) (var9 Addr) (var10 Int) (var11 Addr) (var12 Heap) (var13 Addr) (var14 Int) (var15 Int) (var16 Addr) (var17 node) (var18 Heap) (var19 Addr) (var20 Heap)) (or (not (and (inv_main574_5_1 var20 var19) (and (and (and (and (and (and (and (and (= var18 (newHeap (alloc var20 (O_node var17)))) (= var16 var19)) (= var15 var14)) (= var13 (newAddr (alloc var20 (O_node var17))))) (and (and (and (= var12 (write var18 var13 (O_node (node (|node::next| (getnode (read var18 var13))) var15 (|node::order| (getnode (read var18 var13))))))) (= var11 var16)) (= var10 var15)) (= var9 var13))) (and (and (and (= var8 (write var12 var9 (O_node (node (|node::next| (getnode (read var12 var9))) (|node::stock| (getnode (read var12 var9))) 0)))) (= var7 var11)) (= var6 var10)) (= var5 var9))) (and (and (and (= var4 (write var8 var5 (O_node (node var7 (|node::stock| (getnode (read var8 var5))) (|node::order| (getnode (read var8 var5))))))) (= var3 var7)) (= var2 var6)) (= var1 var5))) (not (<= 0 (+ (* (- 1) var14) (- 1))))) (not (= var0 0))))) (inv_main574_5_1 var4 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main584_5 var3 var2 var1) (and (<= 0 (+ (* (- 1) var0) (- 1))) (not (= var1 nullAddr))))) (inv_main584_5 var3 var2 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Int) (var6 Addr) (var7 Addr) (var8 Heap) (var9 Int) (var10 Int) (var11 Addr) (var12 Addr) (var13 Heap)) (or (not (and (inv_main584_5 var13 var12 var11) (and (and (and (not (= var10 0)) (and (not (<= 0 (+ (* (- 1) var9) (- 1)))) (and (and (and (and (= var8 var13) (= var7 var12)) (= var6 var11)) (= var5 var9)) (= var4 (|node::stock| (getnode (read var13 var11))))))) (and (and (and (and (= var3 var8) (= var2 var7)) (= var1 var6)) (= var0 var5)) (or (and (<= 0 (+ (+ var5 (* (- 1) var4)) (- 1))) (= var10 1)) (and (not (<= 0 (+ (+ var5 (* (- 1) var4)) (- 1)))) (= var10 0))))) (not (= var11 nullAddr))))) (inv_main584_5 var3 var2 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Int) (var6 Addr) (var7 Addr) (var8 Heap) (var9 Int) (var10 Int) (var11 Int) (var12 Int) (var13 Int) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Heap) (var19 Heap) (var20 Addr) (var21 Int) (var22 Int) (var23 Addr) (var24 Addr) (var25 Addr) (var26 Addr) (var27 Heap) (var28 Heap) (var29 Addr) (var30 Addr) (var31 Heap)) (or (not (and (inv_main584_5 var31 var30 var29) (and (and (and (and (and (and (and (= var28 var27) (= var26 var25)) (= var24 var23)) (= var22 var21)) (= var20 (|node::next| (getnode (read var27 var23))))) (and (and (and (and (and (and (= var19 var18) (= var17 var16)) (= var15 var14)) (= var13 var12)) (= var11 (|node::stock| (getnode (read var18 var14))))) (and (and (= var10 0) (and (not (<= 0 (+ (* (- 1) var9) (- 1)))) (and (and (and (and (= var8 var31) (= var7 var30)) (= var6 var29)) (= var5 var9)) (= var4 (|node::stock| (getnode (read var31 var29))))))) (and (and (and (and (= var3 var8) (= var2 var7)) (= var1 var6)) (= var0 var5)) (or (and (<= 0 (+ (+ var5 (* (- 1) var4)) (- 1))) (= var10 1)) (and (not (<= 0 (+ (+ var5 (* (- 1) var4)) (- 1)))) (= var10 0)))))) (and (and (and (= var18 (write var3 var1 (O_node (node (|node::next| (getnode (read var3 var1))) (|node::stock| (getnode (read var3 var1))) var0)))) (= var16 var2)) (= var14 var1)) (= var12 var0)))) (and (and (and (= var27 (write var19 var15 (O_node (node (|node::next| (getnode (read var19 var15))) var11 (|node::order| (getnode (read var19 var15))))))) (= var25 var17)) (= var23 var15)) (= var21 var13))) (not (= var29 nullAddr))))) (inv_main584_5 var28 var26 var20))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap)) (or (not (and (inv_main574_5_1 var2 var1) (= var0 0))) (inv_main584_5 var2 var1 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (and (inv_main584_5 var2 var1 var0) (= var0 nullAddr))) (inv_main_15 var2 var1 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main595_13_18 var6 var5 var4) (and (and (and (= var3 var6) (= var2 var5)) (= var1 var4)) (= var0 (|node::next| (getnode (read var6 var4))))))) (inv_main_15 var3 var2 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main_15 var10 var9 var8) (and (and (and (and (= var7 var6) (= var5 var4)) (= var3 var2)) (= var1 (|node::next| (getnode (read var6 var2))))) (and (and (not (<= 0 (+ (+ var0 (* (- 1) (|node::stock| (getnode (read var6 var2))))) (- 1)))) (and (and (and (= var6 var10) (= var4 var9)) (= var2 var8)) (= var0 (|node::order| (getnode (read var10 var8)))))) (not (= var8 nullAddr)))))) (inv_main_15 var7 var5 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (inv_main595_13_18 var2 var1 var0))))
(check-sat)
