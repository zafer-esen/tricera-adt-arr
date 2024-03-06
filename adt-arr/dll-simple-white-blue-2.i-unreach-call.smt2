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

(declare-datatypes ((HeapObject 0) (TSLL 0))
                   (((O_Int (getInt Int)) (O_UInt (getUInt Int)) (O_Addr (getAddr Addr)) (O_AddrRange (getAddrRange AddrRange)) (O_TSLL (getTSLL TSLL)) (defObj))
                   ((TSLL (|TSLL::next| Addr) (|TSLL::prev| Addr) (|TSLL::data| Int)))))
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
(declare-fun inv_main1000_2 (Heap) Bool)
(declare-fun inv_main1005_2 (Heap Addr Addr) Bool)
(declare-fun inv_main1062_13 (Heap Addr Addr) Bool)
(declare-fun inv_main_15 (Heap Addr Addr) Bool)
(declare-fun inv_main_26 (Heap Addr Addr) Bool)
(declare-fun inv_main_29 (Heap Addr Addr) Bool)
(declare-fun inv_main_37 (Heap Addr Addr) Bool)
(assert (forall ((var0 Heap)) (or (not (= var0 emptyHeap)) (inv_main1000_2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Int) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main_29 var6 var5 var4) (and (and (= var3 1) (and (and (and (= var2 var6) (= var1 var5)) (= var0 var4)) (= var3 (|TSLL::data| (getTSLL (read var6 var4)))))) (not (= var4 nullAddr))))) (inv_main1062_13 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main_26 var10 var9 var8) (and (and (and (and (= var7 var6) (= var5 var4)) (= var3 var2)) (= var1 (|TSLL::next| (getTSLL (read var6 var2))))) (and (not (= var0 1)) (and (and (and (= var6 var10) (= var4 var9)) (= var2 var8)) (= var0 (|TSLL::data| (getTSLL (read var10 var8))))))))) (inv_main_26 var7 var5 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Heap) (var9 Int) (var10 Int) (var11 Addr) (var12 Addr) (var13 Addr) (var14 TSLL) (var15 Heap) (var16 Addr) (var17 Addr) (var18 Heap)) (or (not (and (inv_main1005_2 var18 var17 var16) (and (and (and (and (and (and (and (= var15 (newHeap (alloc var18 (O_TSLL var14)))) (= var13 var17)) (= var12 var16)) (= var11 (newAddr (alloc var18 (O_TSLL var14))))) (and (not (= var10 0)) (= var9 0))) (and (and (= var8 (write var15 var11 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var15 var11))) (|TSLL::prev| (getTSLL (read var15 var11))) 1)))) (= var7 var13)) (= var6 var11))) (and (and (= var5 (write var8 var6 (O_TSLL (TSLL var7 (|TSLL::prev| (getTSLL (read var8 var6))) (|TSLL::data| (getTSLL (read var8 var6))))))) (= var4 var7)) (= var3 var6))) (and (and (= var2 (write var5 var3 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var5 var3))) nullAddr (|TSLL::data| (getTSLL (read var5 var3))))))) (= var1 var4)) (= var0 var3))))) (inv_main_26 var2 var0 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Heap) (var12 Addr) (var13 Addr) (var14 Heap) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Addr) (var22 TSLL) (var23 Heap) (var24 Heap) (var25 Addr) (var26 Addr) (var27 Addr) (var28 Heap)) (or (not (and (inv_main_15 var28 var27 var26) (and (and (and (= var25 nullAddr) (and (and (and (and (and (and (and (= var24 (newHeap (alloc var23 (O_TSLL var22)))) (= var21 var20)) (= var19 var18)) (= var17 var16)) (= var15 (newAddr (alloc var23 (O_TSLL var22))))) (and (and (and (= var23 var14) (= var20 var13)) (= var18 var12)) (= var16 (|TSLL::next| (getTSLL (read var14 var12)))))) (and (and (and (= var11 (write var24 var19 (O_TSLL (TSLL var15 (|TSLL::prev| (getTSLL (read var24 var19))) (|TSLL::data| (getTSLL (read var24 var19))))))) (= var10 var21)) (= var9 var19)) (= var8 var17))) (and (and (and (= var7 (write var11 var9 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var11 var9))) (|TSLL::prev| (getTSLL (read var11 var9))) 1)))) (= var6 var10)) (= var5 var9)) (= var4 var8)))) (and (and (and (= var3 (write var7 var5 (O_TSLL (TSLL var4 (|TSLL::prev| (getTSLL (read var7 var5))) (|TSLL::data| (getTSLL (read var7 var5))))))) (= var2 var6)) (= var1 var5)) (= var25 var4))) (and (= var0 nullAddr) (and (and (and (= var14 var28) (= var13 var27)) (= var12 var26)) (= var0 (|TSLL::next| (getTSLL (read var28 var26))))))))) (inv_main_26 var3 var2 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Heap) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Heap) (var16 Addr) (var17 Addr) (var18 Heap) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Addr) (var25 Addr) (var26 TSLL) (var27 Heap) (var28 Heap) (var29 Addr) (var30 Addr) (var31 Addr) (var32 Addr) (var33 Addr) (var34 Addr) (var35 Addr) (var36 Heap) (var37 Heap) (var38 Addr) (var39 Addr) (var40 Heap)) (or (not (and (inv_main_15 var40 var39 var38) (and (and (and (and (and (and (and (and (= var37 var36) (= var35 var34)) (= var33 var32)) (= var31 var30)) (= var29 (|TSLL::prev| (getTSLL (read var36 var30))))) (and (and (not (= var30 nullAddr)) (and (and (and (and (and (and (and (= var28 (newHeap (alloc var27 (O_TSLL var26)))) (= var25 var24)) (= var23 var22)) (= var21 var20)) (= var19 (newAddr (alloc var27 (O_TSLL var26))))) (and (and (and (= var27 var18) (= var24 var17)) (= var22 var16)) (= var20 (|TSLL::next| (getTSLL (read var18 var16)))))) (and (and (and (= var15 (write var28 var23 (O_TSLL (TSLL var19 (|TSLL::prev| (getTSLL (read var28 var23))) (|TSLL::data| (getTSLL (read var28 var23))))))) (= var14 var25)) (= var13 var23)) (= var12 var21))) (and (and (and (= var11 (write var15 var13 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var15 var13))) (|TSLL::prev| (getTSLL (read var15 var13))) 1)))) (= var10 var14)) (= var9 var13)) (= var8 var12)))) (and (and (and (= var36 (write var11 var9 (O_TSLL (TSLL var8 (|TSLL::prev| (getTSLL (read var11 var9))) (|TSLL::data| (getTSLL (read var11 var9))))))) (= var34 var10)) (= var32 var9)) (= var30 var8)))) (and (and (and (= var7 (write var37 var33 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var37 var33))) var29 (|TSLL::data| (getTSLL (read var37 var33))))))) (= var6 var35)) (= var5 var33)) (= var4 var31))) (and (= var3 nullAddr) (and (and (and (= var18 var40) (= var17 var39)) (= var16 var38)) (= var3 (|TSLL::next| (getTSLL (read var40 var38))))))) (and (and (= var2 (write var7 var4 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var7 var4))) var5 (|TSLL::data| (getTSLL (read var7 var4))))))) (= var1 var6)) (= var0 var5))))) (inv_main_26 var2 var1 var1))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Heap) (var13 Addr) (var14 Addr) (var15 Heap) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Addr) (var23 TSLL) (var24 Heap) (var25 Heap) (var26 Addr) (var27 Addr) (var28 Addr) (var29 Heap)) (or (not (and (inv_main_15 var29 var28 var27) (and (and (and (= var26 nullAddr) (and (and (and (and (and (and (and (= var25 (newHeap (alloc var24 (O_TSLL var23)))) (= var22 var21)) (= var20 var19)) (= var18 var17)) (= var16 (newAddr (alloc var24 (O_TSLL var23))))) (and (and (and (= var24 var15) (= var21 var14)) (= var19 var13)) (= var17 (|TSLL::next| (getTSLL (read var15 var13)))))) (and (and (and (= var12 (write var25 var20 (O_TSLL (TSLL var16 (|TSLL::prev| (getTSLL (read var25 var20))) (|TSLL::data| (getTSLL (read var25 var20))))))) (= var11 var22)) (= var10 var20)) (= var9 var18))) (and (and (and (= var8 (write var12 var10 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var12 var10))) (|TSLL::prev| (getTSLL (read var12 var10))) 1)))) (= var7 var11)) (= var6 var10)) (= var5 var9)))) (and (and (and (= var4 (write var8 var6 (O_TSLL (TSLL var5 (|TSLL::prev| (getTSLL (read var8 var6))) (|TSLL::data| (getTSLL (read var8 var6))))))) (= var3 var7)) (= var2 var6)) (= var26 var5))) (and (not (= var1 0)) (and (not (= var0 nullAddr)) (and (and (and (= var15 var29) (= var14 var28)) (= var13 var27)) (= var0 (|TSLL::next| (getTSLL (read var29 var27)))))))))) (inv_main_26 var4 var3 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Int) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Heap) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Heap) (var17 Addr) (var18 Addr) (var19 Heap) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Addr) (var25 Addr) (var26 Addr) (var27 TSLL) (var28 Heap) (var29 Heap) (var30 Addr) (var31 Addr) (var32 Addr) (var33 Addr) (var34 Addr) (var35 Addr) (var36 Addr) (var37 Heap) (var38 Heap) (var39 Addr) (var40 Addr) (var41 Heap)) (or (not (and (inv_main_15 var41 var40 var39) (and (and (and (and (and (and (and (and (= var38 var37) (= var36 var35)) (= var34 var33)) (= var32 var31)) (= var30 (|TSLL::prev| (getTSLL (read var37 var31))))) (and (and (not (= var31 nullAddr)) (and (and (and (and (and (and (and (= var29 (newHeap (alloc var28 (O_TSLL var27)))) (= var26 var25)) (= var24 var23)) (= var22 var21)) (= var20 (newAddr (alloc var28 (O_TSLL var27))))) (and (and (and (= var28 var19) (= var25 var18)) (= var23 var17)) (= var21 (|TSLL::next| (getTSLL (read var19 var17)))))) (and (and (and (= var16 (write var29 var24 (O_TSLL (TSLL var20 (|TSLL::prev| (getTSLL (read var29 var24))) (|TSLL::data| (getTSLL (read var29 var24))))))) (= var15 var26)) (= var14 var24)) (= var13 var22))) (and (and (and (= var12 (write var16 var14 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var16 var14))) (|TSLL::prev| (getTSLL (read var16 var14))) 1)))) (= var11 var15)) (= var10 var14)) (= var9 var13)))) (and (and (and (= var37 (write var12 var10 (O_TSLL (TSLL var9 (|TSLL::prev| (getTSLL (read var12 var10))) (|TSLL::data| (getTSLL (read var12 var10))))))) (= var35 var11)) (= var33 var10)) (= var31 var9)))) (and (and (and (= var8 (write var38 var34 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var38 var34))) var30 (|TSLL::data| (getTSLL (read var38 var34))))))) (= var7 var36)) (= var6 var34)) (= var5 var32))) (and (not (= var4 0)) (and (not (= var3 nullAddr)) (and (and (and (= var19 var41) (= var18 var40)) (= var17 var39)) (= var3 (|TSLL::next| (getTSLL (read var41 var39)))))))) (and (and (= var2 (write var8 var5 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var8 var5))) var6 (|TSLL::data| (getTSLL (read var8 var5))))))) (= var1 var7)) (= var0 var6))))) (inv_main_26 var2 var1 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main_26 var10 var9 var8) (and (and (and (and (= var7 var6) (= var5 var4)) (= var3 var2)) (= var1 (|TSLL::next| (getTSLL (read var6 var2))))) (and (= var0 1) (and (and (and (= var6 var10) (= var4 var9)) (= var2 var8)) (= var0 (|TSLL::data| (getTSLL (read var10 var8))))))))) (inv_main_29 var7 var5 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main_29 var10 var9 var8) (and (and (and (and (= var7 var6) (= var5 var4)) (= var3 var2)) (= var1 (|TSLL::next| (getTSLL (read var6 var2))))) (and (and (not (= var0 1)) (and (and (and (= var6 var10) (= var4 var9)) (= var2 var8)) (= var0 (|TSLL::data| (getTSLL (read var10 var8)))))) (not (= var8 nullAddr)))))) (inv_main_29 var7 var5 var1))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main1005_2 var4 var3 var2) (and (= var1 0) (= var0 0)))) (inv_main_15 var4 var3 var3))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Heap)) (or (not (and (inv_main_15 var11 var10 var9) (and (and (and (and (= var8 var7) (= var6 var5)) (= var4 var3)) (= var2 (|TSLL::next| (getTSLL (read var7 var3))))) (and (= var1 0) (and (not (= var0 nullAddr)) (and (and (and (= var7 var11) (= var5 var10)) (= var3 var9)) (= var0 (|TSLL::next| (getTSLL (read var11 var9)))))))))) (inv_main_15 var8 var6 var2))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Int) (var8 Addr) (var9 Addr) (var10 Addr) (var11 TSLL) (var12 Heap) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Heap) (var19 Heap) (var20 Addr) (var21 Addr) (var22 Heap)) (or (not (and (inv_main1005_2 var22 var21 var20) (and (and (and (and (and (and (and (= var19 var18) (= var17 var16)) (= var15 var14)) (= var13 (|TSLL::next| (getTSLL (read var18 var14))))) (and (and (and (and (and (= var12 (newHeap (alloc var22 (O_TSLL var11)))) (= var10 var21)) (= var9 var20)) (= var8 (newAddr (alloc var22 (O_TSLL var11))))) (not (= var7 0))) (and (and (= var6 (write var12 var9 (O_TSLL (TSLL var8 (|TSLL::prev| (getTSLL (read var12 var9))) (|TSLL::data| (getTSLL (read var12 var9))))))) (= var5 var10)) (= var4 var9)))) (and (and (= var18 (write var6 (|TSLL::next| (getTSLL (read var6 var4))) (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var6 (|TSLL::next| (getTSLL (read var6 var4)))))) var4 (|TSLL::data| (getTSLL (read var6 (|TSLL::next| (getTSLL (read var6 var4)))))))))) (= var16 var5)) (= var14 var4))) (and (and (= var3 (write var19 var13 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var19 var13))) (|TSLL::prev| (getTSLL (read var19 var13))) 0)))) (= var2 var17)) (= var1 var13))) (= var0 (write var3 var1 (O_TSLL (TSLL nullAddr (|TSLL::prev| (getTSLL (read var3 var1))) (|TSLL::data| (getTSLL (read var3 var1)))))))))) (inv_main1005_2 var0 var2 var1))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Heap) (var6 Addr) (var7 TSLL) (var8 Heap) (var9 Heap)) (or (not (and (inv_main1000_2 var9) (and (and (and (and (= var8 (newHeap (alloc var9 (O_TSLL var7)))) (= var6 (newAddr (alloc var9 (O_TSLL var7))))) (and (= var5 (write var8 var6 (O_TSLL (TSLL nullAddr (|TSLL::prev| (getTSLL (read var8 var6))) (|TSLL::data| (getTSLL (read var8 var6))))))) (= var4 var6))) (and (= var3 (write var5 var4 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var5 var4))) nullAddr (|TSLL::data| (getTSLL (read var5 var4))))))) (= var2 var4))) (and (= var1 (write var3 var2 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var3 var2))) (|TSLL::prev| (getTSLL (read var3 var2))) 0)))) (= var0 var2))))) (inv_main1005_2 var1 var0 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (and (inv_main_29 var2 var1 var0) (= var0 nullAddr))) (inv_main_37 var2 var1 var1))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main_37 var7 var6 var5) (and (and (and (and (and (= var4 var7) (= var3 var5)) (= var2 var5)) (= var1 (|TSLL::next| (getTSLL (read var7 var5))))) (not (= var5 nullAddr))) (= var0 (write var4 var3 defObj))))) (inv_main_37 var0 var3 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (inv_main1062_13 var2 var1 var0))))
(check-sat)
