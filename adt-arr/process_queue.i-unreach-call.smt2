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

(declare-datatypes ((HeapObject 0) (process_node 0))
                   (((O_Int (getInt Int)) (O_UInt (getUInt Int)) (O_Addr (getAddr Addr)) (O_AddrRange (getAddrRange AddrRange)) (O_process_node (getprocess_node process_node)) (defObj))
                   ((process_node (|process_node::process_id| Int) (|process_node::time_to_wait| Int) (|process_node::next| Addr)))))
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
(declare-fun inv_main581_5 (Heap Addr Int Int Addr Addr Addr) Bool)
(declare-fun inv_main598_73 (Heap Addr Int Addr Addr) Bool)
(declare-fun inv_main599_13 (Heap Addr Int Addr Addr) Bool)
(declare-fun inv_main603_5 (Heap) Bool)
(declare-fun inv_main604_5 (Heap Addr Int) Bool)
(assert (forall ((var0 Heap)) (or (not (= var0 emptyHeap)) (inv_main603_5 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Heap) (var5 Int) (var6 Addr) (var7 Addr) (var8 Int) (var9 Addr) (var10 Heap)) (or (not (and (inv_main598_73 var10 var9 var8 var7 var6) (and (and (not (<= 0 (+ var5 (- 1)))) (and (and (and (and (and (= var4 var10) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var0 var6)) (= var5 (|process_node::time_to_wait| (getprocess_node (read var10 var6)))))) (not (= var6 nullAddr))))) (inv_main599_13 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Int) (var9 Addr) (var10 Heap)) (or (not (and (inv_main599_13 var10 var9 var8 var7 var6) (and (and (and (and (and (= var5 var10) (= var4 var9)) (= var3 var8)) (= var2 var7)) (= var1 var6)) (= var0 (|process_node::next| (getprocess_node (read var10 var6))))))) (inv_main598_73 var5 var4 var3 var2 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Int) (var7 Int) (var8 Addr) (var9 Addr) (var10 Heap) (var11 Heap) (var12 Addr) (var13 Addr) (var14 Int) (var15 Addr) (var16 Heap)) (or (not (and (inv_main598_73 var16 var15 var14 var13 var12) (and (and (and (and (and (and (= var11 var10) (= var9 var8)) (= var7 var6)) (= var5 var4)) (= var3 var2)) (= var1 (|process_node::next| (getprocess_node (read var10 var2))))) (and (and (<= 0 (+ var0 (- 1))) (and (and (and (and (and (= var10 var16) (= var8 var15)) (= var6 var14)) (= var4 var13)) (= var2 var12)) (= var0 (|process_node::time_to_wait| (getprocess_node (read var16 var12)))))) (not (= var12 nullAddr)))))) (inv_main598_73 var11 var9 var7 var5 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Int) (var9 Int) (var10 Addr) (var11 Heap)) (or (not (and (inv_main581_5 var11 var10 var9 var8 var7 var6 var5) (and (and (and (and (and (= var4 var11) (= var3 var10)) (= var2 (+ var9 (- 1)))) (= var1 var5)) (= var0 (|process_node::process_id| (getprocess_node (read var11 var5))))) (= var7 nullAddr)))) (inv_main598_73 var4 var3 var2 var3 var3))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Int) (var4 Int) (var5 Addr) (var6 Int) (var7 Heap) (var8 Addr) (var9 Int) (var10 Int) (var11 Int) (var12 Addr) (var13 process_node) (var14 Heap) (var15 Int) (var16 Addr) (var17 Addr) (var18 Int) (var19 Int) (var20 Int) (var21 Int) (var22 Addr) (var23 Addr) (var24 Addr) (var25 Heap) (var26 Heap) (var27 Int) (var28 Addr) (var29 Heap)) (or (not (and (inv_main604_5 var29 var28 var27) (and (and (and (and (and (and (and (and (and (= var26 (write var25 var24 (O_process_node (process_node (|process_node::process_id| (getprocess_node (read var25 var24))) (|process_node::time_to_wait| (getprocess_node (read var25 var24))) var23)))) (= var22 var23)) (= var21 var20)) (= var19 var18)) (= var17 var24)) (= var16 var24)) (= var15 1)) (and (and (and (and (and (= var14 (newHeap (alloc var29 (O_process_node var13)))) (= var12 var28)) (= var11 var27)) (= var10 var9)) (= var8 (newAddr (alloc var29 (O_process_node var13))))) (and (and (and (and (= var7 (write var14 var8 (O_process_node (process_node var6 (|process_node::time_to_wait| (getprocess_node (read var14 var8))) (|process_node::next| (getprocess_node (read var14 var8))))))) (= var5 var12)) (= var4 var11)) (= var3 var10)) (= var2 var8)))) (and (and (and (and (= var25 (write var7 var2 (O_process_node (process_node (|process_node::process_id| (getprocess_node (read var7 var2))) var4 (|process_node::next| (getprocess_node (read var7 var2))))))) (= var23 var5)) (= var20 (+ var4 1))) (= var18 var3)) (= var24 var2))) (and (not (= var1 0)) (and (<= 0 (+ (+ 1000 (* (- 1) var27)) (- 1))) (not (= var0 0))))))) (inv_main598_73 var26 var16 var21 var16 var16))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Heap)) (or (not (and (inv_main604_5 var3 var2 var1) (and (not (<= 0 (+ (+ var1 (- 1)) (- 1)))) (and (not (<= 0 (+ (+ 1000 (* (- 1) var1)) (- 1)))) (not (= var0 0)))))) (inv_main598_73 var3 var2 var1 var2 var2))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Heap)) (or (not (and (inv_main604_5 var4 var3 var2) (and (not (<= 0 (+ (+ var2 (- 1)) (- 1)))) (and (= var1 0) (and (<= 0 (+ (+ 1000 (* (- 1) var2)) (- 1))) (not (= var0 0))))))) (inv_main598_73 var4 var3 var2 var3 var3))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Int) (var10 Int) (var11 Int) (var12 Int) (var13 Addr) (var14 Addr) (var15 Heap) (var16 Heap) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Int) (var24 Int) (var25 Int) (var26 Int) (var27 Addr) (var28 Addr) (var29 Heap) (var30 Heap) (var31 Addr) (var32 Addr) (var33 Addr) (var34 Int) (var35 Int) (var36 Addr) (var37 Heap)) (or (not (and (inv_main581_5 var37 var36 var35 var34 var33 var32 var31) (and (and (and (and (and (and (and (and (and (= var30 var29) (= var28 var27)) (= var26 var25)) (= var24 var23)) (= var22 var21)) (= var20 var21)) (= var19 var18)) (= var17 (|process_node::next| (getprocess_node (read var29 var21))))) (and (and (and (and (and (and (and (and (= var16 var15) (= var14 var13)) (= var12 var11)) (= var10 var9)) (= var8 var7)) (= var6 var5)) (= var4 var3)) (= var2 (|process_node::time_to_wait| (getprocess_node (read var15 var7))))) (and (and (not (= var1 1)) (and (and (and (and (and (and (and (= var15 var37) (= var13 var36)) (= var11 var35)) (= var9 var34)) (= var7 var33)) (= var5 var32)) (= var3 var31)) (= var1 (|process_node::time_to_wait| (getprocess_node (read var37 var33)))))) (not (= var33 nullAddr))))) (and (and (and (and (and (and (= var29 (write var16 var8 (O_process_node (process_node (|process_node::process_id| (getprocess_node (read var16 var8))) (+ var2 (- 1)) (|process_node::next| (getprocess_node (read var16 var8))))))) (= var27 var14)) (= var25 var12)) (= var23 var10)) (= var21 var8)) (= var0 var6)) (= var18 var4))))) (inv_main581_5 var30 var28 var26 var24 var17 var20 var19))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Int) (var6 Int) (var7 Addr) (var8 Addr) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Int) (var17 Int) (var18 Int) (var19 Int) (var20 Addr) (var21 Addr) (var22 Heap) (var23 Heap) (var24 Addr) (var25 Addr) (var26 Addr) (var27 Int) (var28 Int) (var29 Addr) (var30 Heap)) (or (not (and (inv_main581_5 var30 var29 var28 var27 var26 var25 var24) (and (and (and (and (and (and (and (and (= var23 var22) (= var21 var20)) (= var19 var18)) (= var17 var16)) (= var15 var14)) (= var13 var14)) (= var12 var11)) (= var10 (|process_node::next| (getprocess_node (read var22 var14))))) (and (and (and (and (and (and (and (and (= var22 var9) (= var8 var7)) (= var18 var6)) (= var16 var5)) (= var14 var4)) (= var3 var2)) (= var11 var4)) (= var20 (|process_node::next| (getprocess_node (read var9 var4))))) (and (= var2 nullAddr) (and (and (= var1 1) (and (and (and (and (and (and (and (= var9 var30) (= var7 var29)) (= var6 var28)) (= var5 var27)) (= var4 var26)) (= var2 var25)) (= var0 var24)) (= var1 (|process_node::time_to_wait| (getprocess_node (read var30 var26)))))) (not (= var26 nullAddr)))))))) (inv_main581_5 var23 var21 var19 var17 var10 var13 var12))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Int) (var10 Int) (var11 Int) (var12 Int) (var13 Addr) (var14 Addr) (var15 Heap) (var16 Heap) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Int) (var24 Int) (var25 Int) (var26 Int) (var27 Addr) (var28 Addr) (var29 Heap) (var30 Heap) (var31 Addr) (var32 Addr) (var33 Addr) (var34 Int) (var35 Int) (var36 Addr) (var37 Heap)) (or (not (and (inv_main581_5 var37 var36 var35 var34 var33 var32 var31) (and (and (and (and (and (and (and (and (and (= var30 var29) (= var28 var27)) (= var26 var25)) (= var24 var23)) (= var22 var21)) (= var20 var21)) (= var19 var18)) (= var17 (|process_node::next| (getprocess_node (read var29 var21))))) (and (and (and (and (and (and (and (and (= var16 var15) (= var14 var13)) (= var12 var11)) (= var10 var9)) (= var8 var7)) (= var6 var5)) (= var4 var7)) (= var3 (|process_node::next| (getprocess_node (read var15 var7))))) (and (not (= var5 nullAddr)) (and (and (= var2 1) (and (and (and (and (and (and (and (= var15 var37) (= var13 var36)) (= var11 var35)) (= var9 var34)) (= var7 var33)) (= var5 var32)) (= var1 var31)) (= var2 (|process_node::time_to_wait| (getprocess_node (read var37 var33)))))) (not (= var33 nullAddr)))))) (and (and (and (and (and (and (= var29 (write var16 var6 (O_process_node (process_node (|process_node::process_id| (getprocess_node (read var16 var6))) (|process_node::time_to_wait| (getprocess_node (read var16 var6))) var3)))) (= var27 var14)) (= var25 var12)) (= var23 var10)) (= var21 var8)) (= var0 var6)) (= var18 var4))))) (inv_main581_5 var30 var28 var26 var24 var17 var20 var19))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Int) (var5 Int) (var6 Addr) (var7 Heap) (var8 Int) (var9 Addr) (var10 Heap)) (or (not (and (inv_main604_5 var10 var9 var8) (and (and (and (and (and (and (and (= var7 var10) (= var6 var9)) (= var5 var8)) (= var4 1)) (= var3 var9)) (= var2 nullAddr)) (and (<= 0 (+ (+ var8 (- 1)) (- 1))) (and (not (<= 0 (+ (+ 1000 (* (- 1) var8)) (- 1)))) (not (= var1 0))))) (= var0 nullAddr)))) (inv_main581_5 var7 var6 var5 var4 var3 var2 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Addr) (var4 Addr) (var5 Int) (var6 Int) (var7 Addr) (var8 Heap) (var9 Int) (var10 Addr) (var11 Heap)) (or (not (and (inv_main604_5 var11 var10 var9) (and (and (and (and (and (and (and (= var8 var11) (= var7 var10)) (= var6 var9)) (= var5 1)) (= var4 var10)) (= var3 nullAddr)) (and (<= 0 (+ (+ var9 (- 1)) (- 1))) (and (= var2 0) (and (<= 0 (+ (+ 1000 (* (- 1) var9)) (- 1))) (not (= var1 0)))))) (= var0 nullAddr)))) (inv_main581_5 var8 var7 var6 var5 var4 var3 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Heap)) (or (not (and (inv_main598_73 var4 var3 var2 var1 var0) (= var0 nullAddr))) (inv_main604_5 var4 var3 var2))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Heap)) (or (not (and (inv_main603_5 var3) (and (and (= var2 var3) (= var1 nullAddr)) (= var0 1)))) (inv_main604_5 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Heap)) (not (inv_main599_13 var4 var3 var2 var1 var0))))
(check-sat)
