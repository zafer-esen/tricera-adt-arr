(set-logic HORN)
(set-info :source |
    Benchmark: 
    Output by Princess (http://www.philipp.ruemmer.org/princess.shtml)
|)
;===============================================================================
; Encoding of Heap sorts and operations
;-------------------------------------------------------------------------------
(define-sort Addr() Int)
(declare-datatypes ((AddrRange 0))
                   (((AddrRange (AddrRangeStart Addr) (AddrRangeSize Int)))))

(declare-datatypes ((HeapObject 0) (TData 0))
                   (((O_Int (getInt Int)) (O_UInt (getUInt Int)) (O_Addr (getAddr Addr)) (O_AddrRange (getAddrRange AddrRange)) (O_TData (getTData TData)) (defObj))
                   ((TData (|TData::lo| Addr) (|TData::hi| Addr)))))
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
(declare-fun Inv_Heap (Addr HeapObject) Bool)
(declare-fun _Glue6_exp (Addr HeapObject Addr Heap) Bool)
(declare-fun _Glue7 (Heap Addr HeapObject) Bool)
(declare-fun _Glue13_exp (Heap Int HeapObject Addr) Bool)
(assert (forall ((var0 AllocResHeap) (var1 Heap) (var2 HeapObject) (var3 Int)) (or (not (and (and (= (O_Int var3) var2) (= (alloc var1 var2) var0)) (= emptyHeap var1))) (Inv_Heap (newAddr var0) var2))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 Int) (var3 AllocResHeap) (var4 Addr) (var5 AllocResHeap) (var6 Heap) (var7 HeapObject) (var8 Int)) (or (not (and (and (and (and (and (= (O_Int var8) var7) (= (alloc var6 var7) var5)) (= (AllocResHeap var6 var4) var3)) (= (O_Int var2) var1)) (= (alloc var0 var1) var3)) (= emptyHeap var0))) (Inv_Heap (newAddr var5) var7))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 Int) (var3 AllocResHeap) (var4 Heap) (var5 HeapObject) (var6 Int) (var7 AllocResHeap) (var8 Addr) (var9 Heap) (var10 Addr) (var11 Addr) (var12 HeapObject)) (or (not (and (and (and (and (and (and (and (and (and (and (= (O_Int 4) var12) (not (= var11 var10))) (valid var9 var8)) (= (AllocResHeap var9 var11) var7)) (= (O_Int var6) var5)) (= (alloc var4 var5) var7)) (= (AllocResHeap var4 var8) var3)) (= (O_Int var2) var1)) (= (alloc var0 var1) var3)) (= nullAddr var10)) (= emptyHeap var0))) (Inv_Heap var8 var12))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 Int) (var3 AllocResHeap) (var4 Heap) (var5 HeapObject) (var6 Int) (var7 AllocResHeap) (var8 Addr) (var9 Addr) (var10 Heap) (var11 HeapObject) (var12 Addr) (var13 Heap) (var14 HeapObject)) (or (not (and (and (and (and (and (and (and (and (and (and (and (and (= (O_Int 8) var14) (valid var13 var12)) (= (O_Int 4) var11)) (= (write var10 var9 var11) var13)) (not (= var12 var8))) (= (AllocResHeap var10 var12) var7)) (= (O_Int var6) var5)) (= (alloc var4 var5) var7)) (= (AllocResHeap var4 var9) var3)) (= (O_Int var2) var1)) (= (alloc var0 var1) var3)) (= nullAddr var8)) (= emptyHeap var0))) (Inv_Heap var12 var14))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 Int) (var3 AllocResHeap) (var4 Heap) (var5 HeapObject) (var6 Int) (var7 AllocResHeap) (var8 Addr) (var9 Heap) (var10 HeapObject) (var11 Addr) (var12 Heap) (var13 HeapObject) (var14 Addr) (var15 Heap) (var16 HeapObject)) (or (not (and (and (and (and (and (and (and (and (and (and (and (and (and (and (= defObj var16) (valid var15 var14)) (= (O_Int 8) var13)) (= (write var12 var11 var13) var15)) (= (O_Int 4) var10)) (= (write var9 var14 var10) var12)) (not (= var11 var8))) (= (AllocResHeap var9 var11) var7)) (= (O_Int var6) var5)) (= (alloc var4 var5) var7)) (= (AllocResHeap var4 var14) var3)) (= (O_Int var2) var1)) (= (alloc var0 var1) var3)) (= nullAddr var8)) (= emptyHeap var0))) (Inv_Heap var14 var16))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Heap) (var3 HeapObject) (var4 Int) (var5 AllocResHeap) (var6 Heap) (var7 HeapObject) (var8 Int) (var9 AllocResHeap) (var10 Heap) (var11 HeapObject) (var12 Heap) (var13 HeapObject) (var14 Addr) (var15 Heap) (var16 Heap) (var17 HeapObject) (var18 Addr)) (or (not (and (Inv_Heap var18 var17) (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (= defObj var17) (= (read var16 var18) var17)) (= (write var15 var14 var17) var16)) (= (O_Int 8) var13)) (= (write var12 var18 var13) var15)) (= (O_Int 4) var11)) (= (write var10 var14 var11) var12)) (= (AllocResHeap var10 var18) var9)) (= (O_Int var8) var7)) (= (alloc var6 var7) var9)) (= (AllocResHeap var6 var14) var5)) (= (O_Int var4) var3)) (= (alloc var2 var3) var5)) (= nullAddr var1)) (= emptyHeap var2)) (valid var16 var18)) (not (= var18 var1))))) (_Glue6_exp var18 var0 var14 var15))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Heap) (var3 HeapObject) (var4 Int) (var5 AllocResHeap) (var6 Heap) (var7 HeapObject) (var8 Int) (var9 AllocResHeap) (var10 Heap) (var11 HeapObject) (var12 Heap) (var13 HeapObject) (var14 Addr) (var15 Heap) (var16 Addr) (var17 Heap) (var18 HeapObject)) (or (not (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (= defObj var18) (= (read var17 var16) var18)) (= (write var15 var14 var18) var17)) (= (O_Int 8) var13)) (= (write var12 var16 var13) var15)) (= (O_Int 4) var11)) (= (write var10 var14 var11) var12)) (= (AllocResHeap var10 var16) var9)) (= (O_Int var8) var7)) (= (alloc var6 var7) var9)) (= (AllocResHeap var6 var14) var5)) (= (O_Int var4) var3)) (= (alloc var2 var3) var5)) (= nullAddr var1)) (= emptyHeap var2)) (not (valid var17 var16))) (not (= var16 var1)))) (_Glue6_exp var16 var0 var14 var15))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 Addr) (var3 HeapObject) (var4 Addr)) (or (not (and (and (Inv_Heap var4 var3) (_Glue6_exp var2 var1 var4 var0)) (and (and (= (read var0 var4) var3) (valid var0 var4)) (= defObj var1)))) (_Glue7 var0 var2 var3))))
(assert (forall ((var0 HeapObject) (var1 Heap) (var2 Addr) (var3 HeapObject) (var4 Addr)) (or (not (and (_Glue6_exp var4 var3 var2 var1) (and (and (= (read var1 var2) var0) (not (valid var1 var2))) (= defObj var3)))) (_Glue7 var1 var4 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 HeapObject) (var3 Heap) (var4 HeapObject) (var5 Addr)) (not (and (and (Inv_Heap var5 var4) (_Glue7 var3 var5 var2)) (and (and (and (and (= (getInt var2) var1) (= (read var3 var5) var4)) (= (getInt var4) var0)) (not (<= 0 (+ (+ var1 (* (- 1) var0)) (- 1))))) (valid var3 var5))))))
(assert (forall ((var0 Int) (var1 HeapObject) (var2 Int) (var3 HeapObject) (var4 Addr) (var5 Heap)) (not (and (_Glue7 var5 var4 var3) (and (and (and (and (= (getInt var3) var2) (= (read var5 var4) var1)) (= (getInt var1) var0)) (not (<= 0 (+ (+ var2 (* (- 1) var0)) (- 1))))) (not (valid var5 var4)))))))
(assert (forall ((var0 AllocResHeap) (var1 Heap) (var2 HeapObject) (var3 Int)) (or (not (and (and (= (O_Int var3) var2) (= (alloc var1 var2) var0)) (= emptyHeap var1))) (Inv_Heap (newAddr var0) var2))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 Int) (var3 AllocResHeap) (var4 AllocResHeap) (var5 Heap) (var6 Addr) (var7 Addr) (var8 HeapObject) (var9 Int)) (or (not (and (and (and (and (and (and (and (= (O_Int var9) var8) (not (= var7 var6))) (= (alloc var5 var8) var4)) (= (AllocResHeap var5 var7) var3)) (= (O_Int var2) var1)) (= (alloc var0 var1) var3)) (= nullAddr var6)) (= emptyHeap var0))) (Inv_Heap (newAddr var4) var8))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 Int) (var3 AllocResHeap) (var4 Addr) (var5 Heap) (var6 HeapObject) (var7 Int) (var8 AllocResHeap) (var9 Addr) (var10 Addr) (var11 Heap) (var12 HeapObject)) (or (not (and (and (and (and (and (and (and (and (and (and (= (O_Int 4) var12) (valid var11 var10)) (= (AllocResHeap var11 var9) var8)) (= (O_Int var7) var6)) (= (alloc var5 var6) var8)) (not (= var10 var4))) (= (AllocResHeap var5 var10) var3)) (= (O_Int var2) var1)) (= (alloc var0 var1) var3)) (= nullAddr var4)) (= emptyHeap var0))) (Inv_Heap var10 var12))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 Int) (var3 AllocResHeap) (var4 Addr) (var5 Heap) (var6 HeapObject) (var7 Int) (var8 AllocResHeap) (var9 Addr) (var10 Heap) (var11 HeapObject) (var12 Addr) (var13 Heap) (var14 HeapObject)) (or (not (and (and (and (and (and (and (and (and (and (and (and (and (= (O_Int 8) var14) (valid var13 var12)) (= (O_Int 4) var11)) (= (write var10 var9 var11) var13)) (= (AllocResHeap var10 var12) var8)) (= (O_Int var7) var6)) (= (alloc var5 var6) var8)) (not (= var9 var4))) (= (AllocResHeap var5 var9) var3)) (= (O_Int var2) var1)) (= (alloc var0 var1) var3)) (= nullAddr var4)) (= emptyHeap var0))) (Inv_Heap var12 var14))))
(assert (forall ((var0 HeapObject) (var1 Int) (var2 Addr) (var3 Heap) (var4 HeapObject) (var5 Int) (var6 AllocResHeap) (var7 Heap) (var8 HeapObject) (var9 Int) (var10 AllocResHeap) (var11 Heap) (var12 HeapObject) (var13 Addr) (var14 Heap) (var15 HeapObject) (var16 Heap) (var17 HeapObject) (var18 Addr)) (or (not (and (Inv_Heap var18 var17) (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (= defObj var17) (= (read var16 var18) var17)) (= (O_Int 8) var15)) (= (write var14 var13 var15) var16)) (= (O_Int 4) var12)) (= (write var11 var18 var12) var14)) (= (AllocResHeap var11 var13) var10)) (= (O_Int var9) var8)) (= (alloc var7 var8) var10)) (= (AllocResHeap var7 var18) var6)) (= (O_Int var5) var4)) (= (alloc var3 var4) var6)) (= nullAddr var2)) (= (getInt var17) var1)) (= emptyHeap var3)) (valid var16 var18)) (not (= var18 var2))))) (_Glue13_exp var16 var1 var0 var13))))
(assert (forall ((var0 HeapObject) (var1 Int) (var2 Addr) (var3 Heap) (var4 HeapObject) (var5 Int) (var6 AllocResHeap) (var7 Heap) (var8 HeapObject) (var9 Int) (var10 AllocResHeap) (var11 Heap) (var12 HeapObject) (var13 Addr) (var14 Heap) (var15 HeapObject) (var16 Addr) (var17 Heap) (var18 HeapObject)) (or (not (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (= defObj var18) (= (read var17 var16) var18)) (= (O_Int 8) var15)) (= (write var14 var13 var15) var17)) (= (O_Int 4) var12)) (= (write var11 var16 var12) var14)) (= (AllocResHeap var11 var13) var10)) (= (O_Int var9) var8)) (= (alloc var7 var8) var10)) (= (AllocResHeap var7 var16) var6)) (= (O_Int var5) var4)) (= (alloc var3 var4) var6)) (= nullAddr var2)) (= (getInt var18) var1)) (= emptyHeap var3)) (not (valid var17 var16))) (not (= var16 var2)))) (_Glue13_exp var17 var1 var0 var13))))
(assert (forall ((var0 Int) (var1 HeapObject) (var2 Int) (var3 Heap) (var4 HeapObject) (var5 Addr)) (not (and (and (Inv_Heap var5 var4) (_Glue13_exp var3 var2 var1 var5)) (and (and (and (and (= (read var3 var5) var4) (= (getInt var4) var0)) (not (<= 0 (+ (+ var2 (* (- 1) var0)) (- 1))))) (valid var3 var5)) (= defObj var1))))))
(assert (forall ((var0 Int) (var1 HeapObject) (var2 Addr) (var3 HeapObject) (var4 Int) (var5 Heap)) (not (and (_Glue13_exp var5 var4 var3 var2) (and (and (and (and (= (read var5 var2) var1) (= (getInt var1) var0)) (not (<= 0 (+ (+ var4 (* (- 1) var0)) (- 1))))) (not (valid var5 var2))) (= defObj var3))))))
(check-sat)
