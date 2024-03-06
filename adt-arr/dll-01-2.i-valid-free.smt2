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
                   ((TSLL (|TSLL::next| Addr) (|TSLL::prev| Addr) (|TSLL::inner| Addr)))))
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
(declare-fun inv_main1003_2 (Heap) Bool)
(declare-fun inv_main1008_2 (Heap Addr Addr) Bool)
(declare-fun inv_main1031_3 (Heap Addr Addr Int Addr) Bool)
(declare-fun inv_main_38 (Heap Addr Addr) Bool)
(declare-fun inv_main_66 (Heap Addr Addr) Bool)
(declare-fun inv_main_70 (Heap Addr Addr) Bool)
(assert (forall ((var0 Heap)) (or (not (= var0 emptyHeap)) (inv_main1003_2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main_38 var10 var9 var8) (and (and (and (and (= var7 var6) (= var5 var4)) (= var3 var2)) (= var1 (|TSLL::next| (getTSLL (read var6 var4))))) (and (= nullAddr var2) (and (and (and (and (= var6 var10) (= var4 var9)) (= var0 var8)) (= var2 (|TSLL::inner| (getTSLL (read var10 var9))))) (not (= nullAddr var9))))))) (inv_main_70 var7 var5 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Heap)) (or (not (and (inv_main_66 var12 var11 var10) (and (and (and (and (and (= var9 var8) (= var7 var6)) (= var5 var4)) (= var3 (|TSLL::next| (getTSLL (read var8 var6))))) (and (and (= var2 (write var12 var10 defObj)) (= var1 var11)) (= var0 var10))) (and (and (= var8 (write var2 var1 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var2 var1))) (|TSLL::prev| (getTSLL (read var2 var1))) nullAddr)))) (= var6 var1)) (= var4 var0))))) (inv_main_70 var9 var7 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main_70 var5 var4 var3) (and (and (= var2 (write var5 var4 defObj)) (= var1 var4)) (= var0 var3)))) (inv_main_38 var2 var0 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Int) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main1031_3 var10 var9 var8 var7 var6) (and (= nullAddr var5) (and (and (and (and (and (and (= var4 var10) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var0 var6)) (= var5 (|TSLL::next| (getTSLL (read var10 var8))))) (and (<= 0 (+ 1 (* (- 1) var7))) (= nullAddr var6)))))) (inv_main_38 var4 var3 var5))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main1008_2 var6 var5 var4) (and (= nullAddr var3) (and (not (= nullAddr var3)) (and (= var2 0) (and (and (= var1 var6) (= var3 var5)) (= var0 nullAddr))))))) (inv_main_38 var1 var3 var3))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Int) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Int) (var10 Addr) (var11 Addr) (var12 Heap)) (or (not (and (inv_main1031_3 var12 var11 var10 var9 var8) (and (and (and (not (= nullAddr var7)) (and (and (and (and (and (and (= var6 var12) (= var5 var11)) (= var4 var10)) (= var3 var9)) (= var2 var8)) (= var7 (|TSLL::next| (getTSLL (read var12 var10))))) (and (<= 0 (+ 1 (* (- 1) var9))) (= nullAddr var8)))) (= var1 0)) (= var0 (|TSLL::inner| (getTSLL (read var6 var7))))))) (inv_main1031_3 var6 var5 var7 var1 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main1008_2 var8 var7 var6) (and (and (and (not (= nullAddr var5)) (and (not (= nullAddr var5)) (and (= var4 0) (and (and (= var3 var8) (= var5 var7)) (= var2 nullAddr))))) (= var1 0)) (= var0 (|TSLL::inner| (getTSLL (read var3 var5))))))) (inv_main1031_3 var3 var5 var5 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Int) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main1031_3 var10 var9 var8 var7 var6) (and (and (and (and (and (and (and (= var5 var10) (= var4 var9)) (= var3 var8)) (= var2 1)) (= var1 var6)) (= var0 (|TSLL::inner| (getTSLL (read var10 var6))))) (and (= nullAddr (|TSLL::next| (getTSLL (read var10 var6)))) (and (= nullAddr (|TSLL::inner| (getTSLL (read var10 var6)))) (not (= nullAddr var6))))) (and (= var7 0) (not (= nullAddr var6)))))) (inv_main1031_3 var5 var4 var3 var2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Int) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main1031_3 var10 var9 var8 var7 var6) (and (and (and (and (and (and (and (= var5 var10) (= var4 var9)) (= var3 var8)) (= var2 2)) (= var1 var6)) (= var0 (|TSLL::inner| (getTSLL (read var10 var6))))) (and (= nullAddr (|TSLL::next| (getTSLL (read var10 var6)))) (and (= nullAddr (|TSLL::inner| (getTSLL (read var10 var6)))) (not (= nullAddr var6))))) (and (not (= var7 0)) (not (= nullAddr var6)))))) (inv_main1031_3 var5 var4 var3 var2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main_38 var6 var5 var4) (and (= nullAddr (|TSLL::next| (getTSLL (read var3 var2)))) (and (= nullAddr (|TSLL::inner| (getTSLL (read var3 var2)))) (and (not (= nullAddr var2)) (and (not (= nullAddr var2)) (and (and (and (and (= var3 var6) (= var1 var5)) (= var0 var4)) (= var2 (|TSLL::inner| (getTSLL (read var6 var5))))) (not (= nullAddr var5))))))))) (inv_main_66 var3 var1 var2))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Int) (var6 Addr) (var7 Addr) (var8 Addr) (var9 TSLL) (var10 Heap) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Heap) (var17 Heap) (var18 Addr) (var19 Int) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Heap) (var25 Heap) (var26 Addr) (var27 Addr) (var28 Addr) (var29 Heap)) (or (not (and (inv_main1008_2 var29 var28 var27) (and (and (and (not (= var26 nullAddr)) (and (and (and (= var25 var24) (= var23 var22)) (= var21 var20)) (= var26 (|TSLL::inner| (getTSLL (read var24 var20)))))) (and (not (= var19 0)) (and (not (= var18 nullAddr)) (and (and (not (= nullAddr var18)) (and (and (and (and (and (= var17 var16) (= var15 var14)) (= var13 var12)) (= var11 (|TSLL::next| (getTSLL (read var16 var12))))) (and (and (and (and (and (= var10 (newHeap (alloc var29 (O_TSLL var9)))) (= var8 var28)) (= var7 var27)) (= var6 (newAddr (alloc var29 (O_TSLL var9))))) (not (= var5 0))) (and (and (= var4 (write var10 var7 (O_TSLL (TSLL var6 (|TSLL::prev| (getTSLL (read var10 var7))) (|TSLL::inner| (getTSLL (read var10 var7))))))) (= var3 var8)) (= var2 var7)))) (and (and (= var16 (write var4 (|TSLL::next| (getTSLL (read var4 var2))) (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var4 (|TSLL::next| (getTSLL (read var4 var2)))))) var2 (|TSLL::inner| (getTSLL (read var4 (|TSLL::next| (getTSLL (read var4 var2)))))))))) (= var14 var3)) (= var12 var2)))) (and (and (= var1 (write var17 var11 (O_TSLL (TSLL nullAddr (|TSLL::prev| (getTSLL (read var17 var11))) (|TSLL::inner| (getTSLL (read var17 var11))))))) (= var0 var15)) (= var18 var11)))))) (and (and (= var24 (write var1 var18 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var1 var18))) (|TSLL::prev| (getTSLL (read var1 var18))) nullAddr)))) (= var22 var0)) (= var20 var18))))) (inv_main1008_2 var25 var23 var21))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Int) (var6 Addr) (var7 Addr) (var8 Addr) (var9 TSLL) (var10 Heap) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Heap) (var17 Heap) (var18 Addr) (var19 Int) (var20 Addr) (var21 Addr) (var22 Heap) (var23 Addr) (var24 Addr) (var25 Addr) (var26 Heap) (var27 Addr) (var28 Addr) (var29 Addr) (var30 Addr) (var31 Heap) (var32 Heap) (var33 Addr) (var34 Int) (var35 Addr) (var36 Addr) (var37 Heap)) (or (not (and (inv_main1008_2 var37 var36 var35) (and (and (and (and (not (= var34 0)) (and (and (= var33 nullAddr) (and (and (and (= var32 var31) (= var30 var29)) (= var28 var27)) (= var33 (|TSLL::inner| (getTSLL (read var31 var27)))))) (and (and (and (= var26 var32) (= var25 var30)) (= var24 var28)) (= var23 (|TSLL::inner| (getTSLL (read var32 var28))))))) (and (and (and (= var22 var26) (= var21 var25)) (= var20 var24)) (or (and (= var23 nullAddr) (= var34 1)) (and (not (= var23 nullAddr)) (= var34 0))))) (and (not (= var19 0)) (and (not (= var18 nullAddr)) (and (and (not (= nullAddr var18)) (and (and (and (and (and (= var17 var16) (= var15 var14)) (= var13 var12)) (= var11 (|TSLL::next| (getTSLL (read var16 var12))))) (and (and (and (and (and (= var10 (newHeap (alloc var37 (O_TSLL var9)))) (= var8 var36)) (= var7 var35)) (= var6 (newAddr (alloc var37 (O_TSLL var9))))) (not (= var5 0))) (and (and (= var4 (write var10 var7 (O_TSLL (TSLL var6 (|TSLL::prev| (getTSLL (read var10 var7))) (|TSLL::inner| (getTSLL (read var10 var7))))))) (= var3 var8)) (= var2 var7)))) (and (and (= var16 (write var4 (|TSLL::next| (getTSLL (read var4 var2))) (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var4 (|TSLL::next| (getTSLL (read var4 var2)))))) var2 (|TSLL::inner| (getTSLL (read var4 (|TSLL::next| (getTSLL (read var4 var2)))))))))) (= var14 var3)) (= var12 var2)))) (and (and (= var1 (write var17 var11 (O_TSLL (TSLL nullAddr (|TSLL::prev| (getTSLL (read var17 var11))) (|TSLL::inner| (getTSLL (read var17 var11))))))) (= var0 var15)) (= var18 var11)))))) (and (and (= var31 (write var1 var18 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var1 var18))) (|TSLL::prev| (getTSLL (read var1 var18))) nullAddr)))) (= var29 var0)) (= var27 var18))))) (inv_main1008_2 var22 var21 var20))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Heap) (var9 Int) (var10 Addr) (var11 Addr) (var12 Addr) (var13 TSLL) (var14 Heap) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Heap) (var21 Heap) (var22 Int) (var23 Addr) (var24 Addr) (var25 Addr) (var26 Addr) (var27 Addr) (var28 TSLL) (var29 Heap) (var30 Heap) (var31 Addr) (var32 Addr) (var33 Addr) (var34 Addr) (var35 Heap) (var36 Heap) (var37 Addr) (var38 Addr) (var39 Addr) (var40 Heap)) (or (not (and (inv_main1008_2 var40 var39 var38) (and (and (and (not (= var37 nullAddr)) (and (and (and (= var36 var35) (= var34 var33)) (= var32 var31)) (= var37 (|TSLL::inner| (getTSLL (read var35 var31)))))) (and (and (and (and (and (and (= var30 (newHeap (alloc var29 (O_TSLL var28)))) (= var27 var26)) (= var25 var24)) (= var23 (newAddr (alloc var29 (O_TSLL var28))))) (and (= var22 0) (and (not (= var24 nullAddr)) (and (and (not (= nullAddr var24)) (and (and (and (and (and (= var21 var20) (= var19 var18)) (= var17 var16)) (= var15 (|TSLL::next| (getTSLL (read var20 var16))))) (and (and (and (and (and (= var14 (newHeap (alloc var40 (O_TSLL var13)))) (= var12 var39)) (= var11 var38)) (= var10 (newAddr (alloc var40 (O_TSLL var13))))) (not (= var9 0))) (and (and (= var8 (write var14 var11 (O_TSLL (TSLL var10 (|TSLL::prev| (getTSLL (read var14 var11))) (|TSLL::inner| (getTSLL (read var14 var11))))))) (= var7 var12)) (= var6 var11)))) (and (and (= var20 (write var8 (|TSLL::next| (getTSLL (read var8 var6))) (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var8 (|TSLL::next| (getTSLL (read var8 var6)))))) var6 (|TSLL::inner| (getTSLL (read var8 (|TSLL::next| (getTSLL (read var8 var6)))))))))) (= var18 var7)) (= var16 var6)))) (and (and (= var29 (write var21 var15 (O_TSLL (TSLL nullAddr (|TSLL::prev| (getTSLL (read var21 var15))) (|TSLL::inner| (getTSLL (read var21 var15))))))) (= var26 var19)) (= var24 var15)))))) (and (and (= var5 (write var30 var25 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var30 var25))) (|TSLL::prev| (getTSLL (read var30 var25))) var23)))) (= var4 var27)) (= var3 var25))) (and (and (= var2 (write var5 (|TSLL::inner| (getTSLL (read var5 var3))) (O_TSLL (TSLL nullAddr (|TSLL::prev| (getTSLL (read var5 (|TSLL::inner| (getTSLL (read var5 var3)))))) (|TSLL::inner| (getTSLL (read var5 (|TSLL::inner| (getTSLL (read var5 var3)))))))))) (= var1 var4)) (= var0 var3)))) (and (and (= var35 (write var2 (|TSLL::inner| (getTSLL (read var2 var0))) (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var2 (|TSLL::inner| (getTSLL (read var2 var0)))))) (|TSLL::prev| (getTSLL (read var2 (|TSLL::inner| (getTSLL (read var2 var0)))))) nullAddr)))) (= var33 var1)) (= var31 var0))))) (inv_main1008_2 var36 var34 var32))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Heap) (var9 Int) (var10 Addr) (var11 Addr) (var12 Addr) (var13 TSLL) (var14 Heap) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Heap) (var21 Heap) (var22 Int) (var23 Addr) (var24 Addr) (var25 Addr) (var26 Addr) (var27 Addr) (var28 TSLL) (var29 Heap) (var30 Heap) (var31 Addr) (var32 Addr) (var33 Heap) (var34 Addr) (var35 Addr) (var36 Addr) (var37 Heap) (var38 Addr) (var39 Addr) (var40 Addr) (var41 Addr) (var42 Heap) (var43 Heap) (var44 Addr) (var45 Int) (var46 Addr) (var47 Addr) (var48 Heap)) (or (not (and (inv_main1008_2 var48 var47 var46) (and (and (and (and (not (= var45 0)) (and (and (= var44 nullAddr) (and (and (and (= var43 var42) (= var41 var40)) (= var39 var38)) (= var44 (|TSLL::inner| (getTSLL (read var42 var38)))))) (and (and (and (= var37 var43) (= var36 var41)) (= var35 var39)) (= var34 (|TSLL::inner| (getTSLL (read var43 var39))))))) (and (and (and (= var33 var37) (= var32 var36)) (= var31 var35)) (or (and (= var34 nullAddr) (= var45 1)) (and (not (= var34 nullAddr)) (= var45 0))))) (and (and (and (and (and (and (= var30 (newHeap (alloc var29 (O_TSLL var28)))) (= var27 var26)) (= var25 var24)) (= var23 (newAddr (alloc var29 (O_TSLL var28))))) (and (= var22 0) (and (not (= var24 nullAddr)) (and (and (not (= nullAddr var24)) (and (and (and (and (and (= var21 var20) (= var19 var18)) (= var17 var16)) (= var15 (|TSLL::next| (getTSLL (read var20 var16))))) (and (and (and (and (and (= var14 (newHeap (alloc var48 (O_TSLL var13)))) (= var12 var47)) (= var11 var46)) (= var10 (newAddr (alloc var48 (O_TSLL var13))))) (not (= var9 0))) (and (and (= var8 (write var14 var11 (O_TSLL (TSLL var10 (|TSLL::prev| (getTSLL (read var14 var11))) (|TSLL::inner| (getTSLL (read var14 var11))))))) (= var7 var12)) (= var6 var11)))) (and (and (= var20 (write var8 (|TSLL::next| (getTSLL (read var8 var6))) (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var8 (|TSLL::next| (getTSLL (read var8 var6)))))) var6 (|TSLL::inner| (getTSLL (read var8 (|TSLL::next| (getTSLL (read var8 var6)))))))))) (= var18 var7)) (= var16 var6)))) (and (and (= var29 (write var21 var15 (O_TSLL (TSLL nullAddr (|TSLL::prev| (getTSLL (read var21 var15))) (|TSLL::inner| (getTSLL (read var21 var15))))))) (= var26 var19)) (= var24 var15)))))) (and (and (= var5 (write var30 var25 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var30 var25))) (|TSLL::prev| (getTSLL (read var30 var25))) var23)))) (= var4 var27)) (= var3 var25))) (and (and (= var2 (write var5 (|TSLL::inner| (getTSLL (read var5 var3))) (O_TSLL (TSLL nullAddr (|TSLL::prev| (getTSLL (read var5 (|TSLL::inner| (getTSLL (read var5 var3)))))) (|TSLL::inner| (getTSLL (read var5 (|TSLL::inner| (getTSLL (read var5 var3)))))))))) (= var1 var4)) (= var0 var3)))) (and (and (= var42 (write var2 (|TSLL::inner| (getTSLL (read var2 var0))) (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var2 (|TSLL::inner| (getTSLL (read var2 var0)))))) (|TSLL::prev| (getTSLL (read var2 (|TSLL::inner| (getTSLL (read var2 var0)))))) nullAddr)))) (= var40 var1)) (= var38 var0))))) (inv_main1008_2 var33 var32 var31))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Heap) (var3 Addr) (var4 TSLL) (var5 Heap) (var6 Addr) (var7 Int) (var8 Addr) (var9 Addr) (var10 Heap) (var11 Heap) (var12 Addr) (var13 Heap)) (or (not (and (inv_main1003_2 var13) (and (and (and (not (= var12 nullAddr)) (and (and (= var11 var10) (= var9 var8)) (= var12 (|TSLL::inner| (getTSLL (read var10 var8)))))) (and (not (= var7 0)) (and (and (not (= var6 nullAddr)) (and (and (= var5 (newHeap (alloc var13 (O_TSLL var4)))) (= var3 (newAddr (alloc var13 (O_TSLL var4))))) (and (= var2 (write var5 var3 (O_TSLL (TSLL nullAddr (|TSLL::prev| (getTSLL (read var5 var3))) (|TSLL::inner| (getTSLL (read var5 var3))))))) (= var1 var3)))) (and (= var0 (write var2 var1 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var2 var1))) nullAddr (|TSLL::inner| (getTSLL (read var2 var1))))))) (= var6 var1))))) (and (= var10 (write var0 var6 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var0 var6))) (|TSLL::prev| (getTSLL (read var0 var6))) nullAddr)))) (= var8 var6))))) (inv_main1008_2 var11 var9 var9))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Heap) (var3 Addr) (var4 TSLL) (var5 Heap) (var6 Addr) (var7 Int) (var8 Addr) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Heap) (var13 Addr) (var14 Addr) (var15 Heap) (var16 Heap) (var17 Addr) (var18 Int) (var19 Heap)) (or (not (and (inv_main1003_2 var19) (and (and (and (and (not (= var18 0)) (and (and (= var17 nullAddr) (and (and (= var16 var15) (= var14 var13)) (= var17 (|TSLL::inner| (getTSLL (read var15 var13)))))) (and (and (= var12 var16) (= var11 var14)) (= var10 (|TSLL::inner| (getTSLL (read var16 var14))))))) (and (and (= var9 var12) (= var8 var11)) (or (and (= var10 nullAddr) (= var18 1)) (and (not (= var10 nullAddr)) (= var18 0))))) (and (not (= var7 0)) (and (and (not (= var6 nullAddr)) (and (and (= var5 (newHeap (alloc var19 (O_TSLL var4)))) (= var3 (newAddr (alloc var19 (O_TSLL var4))))) (and (= var2 (write var5 var3 (O_TSLL (TSLL nullAddr (|TSLL::prev| (getTSLL (read var5 var3))) (|TSLL::inner| (getTSLL (read var5 var3))))))) (= var1 var3)))) (and (= var0 (write var2 var1 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var2 var1))) nullAddr (|TSLL::inner| (getTSLL (read var2 var1))))))) (= var6 var1))))) (and (= var15 (write var0 var6 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var0 var6))) (|TSLL::prev| (getTSLL (read var0 var6))) nullAddr)))) (= var13 var6))))) (inv_main1008_2 var9 var8 var8))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Heap) (var6 Addr) (var7 TSLL) (var8 Heap) (var9 Int) (var10 Addr) (var11 Addr) (var12 Addr) (var13 TSLL) (var14 Heap) (var15 Heap) (var16 Addr) (var17 Addr) (var18 Heap) (var19 Heap) (var20 Addr) (var21 Heap)) (or (not (and (inv_main1003_2 var21) (and (and (and (not (= var20 nullAddr)) (and (and (= var19 var18) (= var17 var16)) (= var20 (|TSLL::inner| (getTSLL (read var18 var16)))))) (and (and (and (and (and (= var15 (newHeap (alloc var14 (O_TSLL var13)))) (= var12 var11)) (= var10 (newAddr (alloc var14 (O_TSLL var13))))) (and (= var9 0) (and (and (not (= var11 nullAddr)) (and (and (= var8 (newHeap (alloc var21 (O_TSLL var7)))) (= var6 (newAddr (alloc var21 (O_TSLL var7))))) (and (= var5 (write var8 var6 (O_TSLL (TSLL nullAddr (|TSLL::prev| (getTSLL (read var8 var6))) (|TSLL::inner| (getTSLL (read var8 var6))))))) (= var4 var6)))) (and (= var14 (write var5 var4 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var5 var4))) nullAddr (|TSLL::inner| (getTSLL (read var5 var4))))))) (= var11 var4))))) (and (= var3 (write var15 var12 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var15 var12))) (|TSLL::prev| (getTSLL (read var15 var12))) var10)))) (= var2 var12))) (and (= var1 (write var3 (|TSLL::inner| (getTSLL (read var3 var2))) (O_TSLL (TSLL nullAddr (|TSLL::prev| (getTSLL (read var3 (|TSLL::inner| (getTSLL (read var3 var2)))))) (|TSLL::inner| (getTSLL (read var3 (|TSLL::inner| (getTSLL (read var3 var2)))))))))) (= var0 var2)))) (and (= var18 (write var1 (|TSLL::inner| (getTSLL (read var1 var0))) (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var1 (|TSLL::inner| (getTSLL (read var1 var0)))))) (|TSLL::prev| (getTSLL (read var1 (|TSLL::inner| (getTSLL (read var1 var0)))))) nullAddr)))) (= var16 var0))))) (inv_main1008_2 var19 var17 var17))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Heap) (var6 Addr) (var7 TSLL) (var8 Heap) (var9 Int) (var10 Addr) (var11 Addr) (var12 Addr) (var13 TSLL) (var14 Heap) (var15 Heap) (var16 Addr) (var17 Heap) (var18 Addr) (var19 Addr) (var20 Heap) (var21 Addr) (var22 Addr) (var23 Heap) (var24 Heap) (var25 Addr) (var26 Int) (var27 Heap)) (or (not (and (inv_main1003_2 var27) (and (and (and (and (not (= var26 0)) (and (and (= var25 nullAddr) (and (and (= var24 var23) (= var22 var21)) (= var25 (|TSLL::inner| (getTSLL (read var23 var21)))))) (and (and (= var20 var24) (= var19 var22)) (= var18 (|TSLL::inner| (getTSLL (read var24 var22))))))) (and (and (= var17 var20) (= var16 var19)) (or (and (= var18 nullAddr) (= var26 1)) (and (not (= var18 nullAddr)) (= var26 0))))) (and (and (and (and (and (= var15 (newHeap (alloc var14 (O_TSLL var13)))) (= var12 var11)) (= var10 (newAddr (alloc var14 (O_TSLL var13))))) (and (= var9 0) (and (and (not (= var11 nullAddr)) (and (and (= var8 (newHeap (alloc var27 (O_TSLL var7)))) (= var6 (newAddr (alloc var27 (O_TSLL var7))))) (and (= var5 (write var8 var6 (O_TSLL (TSLL nullAddr (|TSLL::prev| (getTSLL (read var8 var6))) (|TSLL::inner| (getTSLL (read var8 var6))))))) (= var4 var6)))) (and (= var14 (write var5 var4 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var5 var4))) nullAddr (|TSLL::inner| (getTSLL (read var5 var4))))))) (= var11 var4))))) (and (= var3 (write var15 var12 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var15 var12))) (|TSLL::prev| (getTSLL (read var15 var12))) var10)))) (= var2 var12))) (and (= var1 (write var3 (|TSLL::inner| (getTSLL (read var3 var2))) (O_TSLL (TSLL nullAddr (|TSLL::prev| (getTSLL (read var3 (|TSLL::inner| (getTSLL (read var3 var2)))))) (|TSLL::inner| (getTSLL (read var3 (|TSLL::inner| (getTSLL (read var3 var2)))))))))) (= var0 var2)))) (and (= var23 (write var1 (|TSLL::inner| (getTSLL (read var1 var0))) (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var1 (|TSLL::inner| (getTSLL (read var1 var0)))))) (|TSLL::prev| (getTSLL (read var1 (|TSLL::inner| (getTSLL (read var1 var0)))))) nullAddr)))) (= var21 var0))))) (inv_main1008_2 var17 var16 var16))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_66 var2 var1 var0) (and (not (= var0 nullAddr)) (= (read var2 var0) defObj))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_70 var2 var1 var0) (and (not (= var1 nullAddr)) (= (read var2 var1) defObj))))))
(check-sat)
