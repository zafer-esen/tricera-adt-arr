(set-logic HORN)
(set-info :source |
    Benchmark: C_VC
    Output by Princess (http://www.philipp.ruemmer.org/princess.shtml)
|)
(set-info :status unknown)
(declare-datatype bool ((true) (false)))
;===============================================================================
; Encoding of Heap sorts and operations
;-------------------------------------------------------------------------------
(define-sort Addr() Int)
(declare-datatypes ((AddrRange 0))
                   (((AddrRange (AddrRangeStart Addr) (AddrRangeSize Int)))))

(declare-datatypes ((HeapObject 0) (item 0))
                   (((O_Int (getInt Int)) (O_UInt (getUInt Int)) (O_Addr (getAddr Addr)) (O_AddrRange (getAddrRange AddrRange)) (O_item (getitem item)) (defObj))
                   ((item (|item::next| Addr) (|item::data| Addr)))))
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
(declare-fun inv_main539_5 (Heap Addr) Bool)
(declare-fun inv_main539_5_1 (Heap Addr Addr) Bool)
(declare-fun inv_main554_12 (Heap Addr Int) Bool)
(declare-fun inv_main_5 (Heap Addr Addr) Bool)
(assert (forall ((var0 Addr) (var1 Heap)) (or (not (and (= var1 emptyHeap) (= var0 nullAddr))) (inv_main539_5 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main_5 var3 var2 var1) (and (= var1 nullAddr) (= var0 0)))) (inv_main554_12 var3 var2 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Addr) (var5 Bool) (var6 Addr) (var7 item) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Int) (var12 Int) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Heap) (var18 Addr) (var19 Heap) (var20 Int) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Heap) (var25 Addr) (var26 Addr) (var27 Addr) (var28 Heap) (var29 Addr) (var30 Addr) (var31 Addr) (var32 Addr) (var33 Addr) (var34 Heap) (var35 Heap) (var36 Addr) (var37 Addr) (var38 Heap)) (or (not (and (inv_main539_5_1 var38 var37 var36) (and (and (and (and (and (and (= var35 var34) (= var33 var32)) (= var31 var30)) (= var29 (|item::next| (getitem (read var34 var30))))) (and (and (and (= var28 (write var35 (|item::data| (getitem (read var35 var31))) defObj)) (or (and (= var33 (|item::data| (getitem (read var35 var31)))) (= var27 nullAddr)) (and (not (= var33 (|item::data| (getitem (read var35 var31))))) (= var27 var33)))) (= var26 var31)) (= var25 var29))) (and (and (and (= var24 (write var28 var26 defObj)) (or (and (= var27 var26) (= var23 nullAddr)) (and (not (= var27 var26)) (= var23 var27)))) (= var22 var26)) (= var21 var25))) (and (not (= var30 nullAddr)) (and (= var20 0) (and (and (and (and (not (= (|item::next| (getitem (read var19 var18))) nullAddr)) (and (and (and (and (and (= var17 var19) (= var16 var15)) (= var14 var13)) (= var12 var11)) (= var10 var18)) (= var9 (|item::data| (getitem (read var19 (|item::next| (getitem (read var19 var18))))))))) (and (and (and (and (= var8 (newHeap (alloc var38 (O_item var7)))) (or (and var5 (= var6 (newAddr (alloc var38 (O_item var7))))) (and (not var5) (= var6 var37)))) (= var4 var36)) (= var3 2)) (= var2 (newAddr (alloc var38 (O_item var7)))))) (and (and (and (and (= var19 (write var8 var2 (O_item (item var4 (|item::data| (getitem (read var8 var2))))))) (= var15 var6)) (= var13 var4)) (= var11 var3)) (= var18 var2))) (and (and (and (and (= var34 (write var17 var10 (O_item (item (|item::next| (getitem (read var17 var10))) var9)))) (= var32 var16)) (= var1 var14)) (= var0 var12)) (= var30 var10)))))))) (inv_main_5 var24 var23 var21))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Addr) (var5 Bool) (var6 Addr) (var7 item) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Int) (var12 Int) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Bool) (var17 Addr) (var18 item) (var19 Heap) (var20 Addr) (var21 Heap) (var22 Int) (var23 Addr) (var24 Addr) (var25 Addr) (var26 Heap) (var27 Addr) (var28 Addr) (var29 Addr) (var30 Heap) (var31 Addr) (var32 Addr) (var33 Addr) (var34 Addr) (var35 Addr) (var36 Heap) (var37 Heap) (var38 Addr) (var39 Addr) (var40 Heap)) (or (not (and (inv_main539_5_1 var40 var39 var38) (and (and (and (and (and (and (= var37 var36) (= var35 var34)) (= var33 var32)) (= var31 (|item::next| (getitem (read var36 var32))))) (and (and (and (= var30 (write var37 (|item::data| (getitem (read var37 var33))) defObj)) (or (and (= var35 (|item::data| (getitem (read var37 var33)))) (= var29 nullAddr)) (and (not (= var35 (|item::data| (getitem (read var37 var33))))) (= var29 var35)))) (= var28 var33)) (= var27 var31))) (and (and (and (= var26 (write var30 var28 defObj)) (or (and (= var29 var28) (= var25 nullAddr)) (and (not (= var29 var28)) (= var25 var29)))) (= var24 var28)) (= var23 var27))) (and (not (= var32 nullAddr)) (and (= var22 0) (and (and (and (and (= (|item::next| (getitem (read var21 var20))) nullAddr) (and (and (and (and (and (= var19 (newHeap (alloc var21 (O_item var18)))) (or (and var16 (= var17 (newAddr (alloc var21 (O_item var18))))) (and (not var16) (= var17 var15)))) (= var14 var13)) (= var12 var11)) (= var10 var20)) (= var9 (newAddr (alloc var21 (O_item var18)))))) (and (and (and (and (= var8 (newHeap (alloc var40 (O_item var7)))) (or (and var5 (= var6 (newAddr (alloc var40 (O_item var7))))) (and (not var5) (= var6 var39)))) (= var4 var38)) (= var3 2)) (= var2 (newAddr (alloc var40 (O_item var7)))))) (and (and (and (and (= var21 (write var8 var2 (O_item (item var4 (|item::data| (getitem (read var8 var2))))))) (= var15 var6)) (= var13 var4)) (= var11 var3)) (= var20 var2))) (and (and (and (and (= var36 (write var19 var10 (O_item (item (|item::next| (getitem (read var19 var10))) var9)))) (= var34 var17)) (= var1 var14)) (= var0 var12)) (= var32 var10)))))))) (inv_main_5 var26 var25 var23))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Int) (var6 Addr) (var7 Bool) (var8 Addr) (var9 item) (var10 Heap) (var11 Addr) (var12 Addr) (var13 Int) (var14 Int) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Heap) (var20 Addr) (var21 Heap) (var22 Int) (var23 Addr) (var24 Addr) (var25 Addr) (var26 Heap)) (or (not (and (inv_main539_5_1 var26 var25 var24) (and (= var23 nullAddr) (and (= var22 0) (and (and (and (and (not (= (|item::next| (getitem (read var21 var20))) nullAddr)) (and (and (and (and (and (= var19 var21) (= var18 var17)) (= var16 var15)) (= var14 var13)) (= var12 var20)) (= var11 (|item::data| (getitem (read var21 (|item::next| (getitem (read var21 var20))))))))) (and (and (and (and (= var10 (newHeap (alloc var26 (O_item var9)))) (or (and var7 (= var8 (newAddr (alloc var26 (O_item var9))))) (and (not var7) (= var8 var25)))) (= var6 var24)) (= var5 2)) (= var4 (newAddr (alloc var26 (O_item var9)))))) (and (and (and (and (= var21 (write var10 var4 (O_item (item var6 (|item::data| (getitem (read var10 var4))))))) (= var17 var8)) (= var15 var6)) (= var13 var5)) (= var20 var4))) (and (and (and (and (= var3 (write var19 var12 (O_item (item (|item::next| (getitem (read var19 var12))) var11)))) (= var2 var18)) (= var1 var16)) (= var0 var14)) (= var23 var12))))))) (inv_main_5 var3 var2 var23))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Int) (var6 Addr) (var7 Bool) (var8 Addr) (var9 item) (var10 Heap) (var11 Addr) (var12 Addr) (var13 Int) (var14 Int) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Bool) (var19 Addr) (var20 item) (var21 Heap) (var22 Addr) (var23 Heap) (var24 Int) (var25 Addr) (var26 Addr) (var27 Addr) (var28 Heap)) (or (not (and (inv_main539_5_1 var28 var27 var26) (and (= var25 nullAddr) (and (= var24 0) (and (and (and (and (= (|item::next| (getitem (read var23 var22))) nullAddr) (and (and (and (and (and (= var21 (newHeap (alloc var23 (O_item var20)))) (or (and var18 (= var19 (newAddr (alloc var23 (O_item var20))))) (and (not var18) (= var19 var17)))) (= var16 var15)) (= var14 var13)) (= var12 var22)) (= var11 (newAddr (alloc var23 (O_item var20)))))) (and (and (and (and (= var10 (newHeap (alloc var28 (O_item var9)))) (or (and var7 (= var8 (newAddr (alloc var28 (O_item var9))))) (and (not var7) (= var8 var27)))) (= var6 var26)) (= var5 2)) (= var4 (newAddr (alloc var28 (O_item var9)))))) (and (and (and (and (= var23 (write var10 var4 (O_item (item var6 (|item::data| (getitem (read var10 var4))))))) (= var17 var8)) (= var15 var6)) (= var13 var5)) (= var22 var4))) (and (and (and (and (= var3 (write var21 var12 (O_item (item (|item::next| (getitem (read var21 var12))) var11)))) (= var2 var19)) (= var1 var16)) (= var0 var14)) (= var25 var12))))))) (inv_main_5 var3 var2 var25))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main_5 var10 var9 var8) (and (and (and (and (and (= var7 var10) (= var6 var9)) (= var5 var8)) (= var4 (|item::next| (getitem (read var10 var8))))) (and (and (and (= var3 (write var7 var5 defObj)) (or (and (= var6 var5) (= var2 nullAddr)) (and (not (= var6 var5)) (= var2 var6)))) (= var1 var5)) (= var0 var4))) (not (= var8 nullAddr))))) (inv_main_5 var3 var2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (and (inv_main539_5 var2 var1) (= var0 nullAddr))) (inv_main539_5_1 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Int) (var7 Addr) (var8 Bool) (var9 Addr) (var10 item) (var11 Heap) (var12 Addr) (var13 Addr) (var14 Int) (var15 Int) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Heap) (var21 Addr) (var22 Heap) (var23 Int) (var24 Addr) (var25 Addr) (var26 Heap)) (or (not (and (inv_main539_5_1 var26 var25 var24) (and (not (= var23 0)) (and (and (and (and (not (= (|item::next| (getitem (read var22 var21))) nullAddr)) (and (and (and (and (and (= var20 var22) (= var19 var18)) (= var17 var16)) (= var15 var14)) (= var13 var21)) (= var12 (|item::data| (getitem (read var22 (|item::next| (getitem (read var22 var21))))))))) (and (and (and (and (= var11 (newHeap (alloc var26 (O_item var10)))) (or (and var8 (= var9 (newAddr (alloc var26 (O_item var10))))) (and (not var8) (= var9 var25)))) (= var7 var24)) (= var6 2)) (= var5 (newAddr (alloc var26 (O_item var10)))))) (and (and (and (and (= var22 (write var11 var5 (O_item (item var7 (|item::data| (getitem (read var11 var5))))))) (= var18 var9)) (= var16 var7)) (= var14 var6)) (= var21 var5))) (and (and (and (and (= var4 (write var20 var13 (O_item (item (|item::next| (getitem (read var20 var13))) var12)))) (= var3 var19)) (= var2 var17)) (= var1 var15)) (= var0 var13)))))) (inv_main539_5_1 var4 var3 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Int) (var7 Addr) (var8 Bool) (var9 Addr) (var10 item) (var11 Heap) (var12 Addr) (var13 Addr) (var14 Int) (var15 Int) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Bool) (var20 Addr) (var21 item) (var22 Heap) (var23 Addr) (var24 Heap) (var25 Int) (var26 Addr) (var27 Addr) (var28 Heap)) (or (not (and (inv_main539_5_1 var28 var27 var26) (and (not (= var25 0)) (and (and (and (and (= (|item::next| (getitem (read var24 var23))) nullAddr) (and (and (and (and (and (= var22 (newHeap (alloc var24 (O_item var21)))) (or (and var19 (= var20 (newAddr (alloc var24 (O_item var21))))) (and (not var19) (= var20 var18)))) (= var17 var16)) (= var15 var14)) (= var13 var23)) (= var12 (newAddr (alloc var24 (O_item var21)))))) (and (and (and (and (= var11 (newHeap (alloc var28 (O_item var10)))) (or (and var8 (= var9 (newAddr (alloc var28 (O_item var10))))) (and (not var8) (= var9 var27)))) (= var7 var26)) (= var6 2)) (= var5 (newAddr (alloc var28 (O_item var10)))))) (and (and (and (and (= var24 (write var11 var5 (O_item (item var7 (|item::data| (getitem (read var11 var5))))))) (= var18 var9)) (= var16 var7)) (= var14 var6)) (= var23 var5))) (and (and (and (and (= var4 (write var22 var13 (O_item (item (|item::next| (getitem (read var22 var13))) var12)))) (= var3 var20)) (= var2 var17)) (= var1 var15)) (= var0 var13)))))) (inv_main539_5_1 var4 var3 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap)) (not (and (inv_main554_12 var2 var1 var0) (not (= var1 nullAddr))))))
(check-sat)
