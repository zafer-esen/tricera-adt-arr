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
                   ((TSLL (|TSLL::next| Addr) (|TSLL::inner| Addr)))))
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
(declare-fun inv_main1002_2 (Heap) Bool)
(declare-fun inv_main1006_2 (Heap Addr Addr) Bool)
(declare-fun inv_main1028_3 (Heap Addr Addr Int Addr) Bool)
(declare-fun inv_main_36 (Heap Addr Addr) Bool)
(declare-fun inv_main_64 (Heap Addr Addr) Bool)
(declare-fun inv_main_68 (Heap Addr Addr) Bool)
(assert (forall ((var0 Heap)) (or (not (= var0 emptyHeap)) (inv_main1002_2 var0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 TSLL) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Heap) (var14 Heap) (var15 Addr) (var16 Int) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Heap) (var22 Heap) (var23 Addr) (var24 Addr) (var25 Addr) (var26 Heap)) (or (not (and (inv_main1006_2 var26 var25 var24) (and (and (and (not (= var23 nullAddr)) (and (and (and (= var22 var21) (= var20 var19)) (= var18 var17)) (= var23 (|TSLL::inner| (getTSLL (read var21 var17)))))) (and (not (= var16 0)) (and (not (= var15 nullAddr)) (and (and (not (= nullAddr var15)) (and (and (and (and (and (= var14 var13) (= var12 var11)) (= var10 var9)) (= var8 (|TSLL::next| (getTSLL (read var13 var9))))) (and (and (and (and (= var7 (newHeap (alloc var26 (O_TSLL var6)))) (= var5 var25)) (= var4 var24)) (= var3 (newAddr (alloc var26 (O_TSLL var6))))) (not (= var2 0)))) (and (and (= var13 (write var7 var4 (O_TSLL (TSLL var3 (|TSLL::inner| (getTSLL (read var7 var4))))))) (= var11 var5)) (= var9 var4)))) (and (and (= var1 (write var14 var8 (O_TSLL (TSLL nullAddr (|TSLL::inner| (getTSLL (read var14 var8))))))) (= var0 var12)) (= var15 var8)))))) (and (and (= var21 (write var1 var15 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var1 var15))) nullAddr)))) (= var19 var0)) (= var17 var15))))) (inv_main1006_2 var22 var20 var18))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 TSLL) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Heap) (var14 Heap) (var15 Addr) (var16 Int) (var17 Addr) (var18 Addr) (var19 Heap) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Heap) (var24 Addr) (var25 Addr) (var26 Addr) (var27 Addr) (var28 Heap) (var29 Heap) (var30 Addr) (var31 Int) (var32 Addr) (var33 Addr) (var34 Heap)) (or (not (and (inv_main1006_2 var34 var33 var32) (and (and (and (and (not (= var31 0)) (and (and (= var30 nullAddr) (and (and (and (= var29 var28) (= var27 var26)) (= var25 var24)) (= var30 (|TSLL::inner| (getTSLL (read var28 var24)))))) (and (and (and (= var23 var29) (= var22 var27)) (= var21 var25)) (= var20 (|TSLL::inner| (getTSLL (read var29 var25))))))) (and (and (and (= var19 var23) (= var18 var22)) (= var17 var21)) (or (and (= var20 nullAddr) (= var31 1)) (and (not (= var20 nullAddr)) (= var31 0))))) (and (not (= var16 0)) (and (not (= var15 nullAddr)) (and (and (not (= nullAddr var15)) (and (and (and (and (and (= var14 var13) (= var12 var11)) (= var10 var9)) (= var8 (|TSLL::next| (getTSLL (read var13 var9))))) (and (and (and (and (= var7 (newHeap (alloc var34 (O_TSLL var6)))) (= var5 var33)) (= var4 var32)) (= var3 (newAddr (alloc var34 (O_TSLL var6))))) (not (= var2 0)))) (and (and (= var13 (write var7 var4 (O_TSLL (TSLL var3 (|TSLL::inner| (getTSLL (read var7 var4))))))) (= var11 var5)) (= var9 var4)))) (and (and (= var1 (write var14 var8 (O_TSLL (TSLL nullAddr (|TSLL::inner| (getTSLL (read var14 var8))))))) (= var0 var12)) (= var15 var8)))))) (and (and (= var28 (write var1 var15 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var1 var15))) nullAddr)))) (= var26 var0)) (= var24 var15))))) (inv_main1006_2 var19 var18 var17))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Int) (var7 Addr) (var8 Addr) (var9 Addr) (var10 TSLL) (var11 Heap) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Heap) (var18 Heap) (var19 Int) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Addr) (var25 TSLL) (var26 Heap) (var27 Heap) (var28 Addr) (var29 Addr) (var30 Addr) (var31 Addr) (var32 Heap) (var33 Heap) (var34 Addr) (var35 Addr) (var36 Addr) (var37 Heap)) (or (not (and (inv_main1006_2 var37 var36 var35) (and (and (and (not (= var34 nullAddr)) (and (and (and (= var33 var32) (= var31 var30)) (= var29 var28)) (= var34 (|TSLL::inner| (getTSLL (read var32 var28)))))) (and (and (and (and (and (and (= var27 (newHeap (alloc var26 (O_TSLL var25)))) (= var24 var23)) (= var22 var21)) (= var20 (newAddr (alloc var26 (O_TSLL var25))))) (and (= var19 0) (and (not (= var21 nullAddr)) (and (and (not (= nullAddr var21)) (and (and (and (and (and (= var18 var17) (= var16 var15)) (= var14 var13)) (= var12 (|TSLL::next| (getTSLL (read var17 var13))))) (and (and (and (and (= var11 (newHeap (alloc var37 (O_TSLL var10)))) (= var9 var36)) (= var8 var35)) (= var7 (newAddr (alloc var37 (O_TSLL var10))))) (not (= var6 0)))) (and (and (= var17 (write var11 var8 (O_TSLL (TSLL var7 (|TSLL::inner| (getTSLL (read var11 var8))))))) (= var15 var9)) (= var13 var8)))) (and (and (= var26 (write var18 var12 (O_TSLL (TSLL nullAddr (|TSLL::inner| (getTSLL (read var18 var12))))))) (= var23 var16)) (= var21 var12)))))) (and (and (= var5 (write var27 var22 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var27 var22))) var20)))) (= var4 var24)) (= var3 var22))) (and (and (= var2 (write var5 (|TSLL::inner| (getTSLL (read var5 var3))) (O_TSLL (TSLL nullAddr (|TSLL::inner| (getTSLL (read var5 (|TSLL::inner| (getTSLL (read var5 var3)))))))))) (= var1 var4)) (= var0 var3)))) (and (and (= var32 (write var2 (|TSLL::inner| (getTSLL (read var2 var0))) (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var2 (|TSLL::inner| (getTSLL (read var2 var0)))))) nullAddr)))) (= var30 var1)) (= var28 var0))))) (inv_main1006_2 var33 var31 var29))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Int) (var7 Addr) (var8 Addr) (var9 Addr) (var10 TSLL) (var11 Heap) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Heap) (var18 Heap) (var19 Int) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Addr) (var25 TSLL) (var26 Heap) (var27 Heap) (var28 Addr) (var29 Addr) (var30 Heap) (var31 Addr) (var32 Addr) (var33 Addr) (var34 Heap) (var35 Addr) (var36 Addr) (var37 Addr) (var38 Addr) (var39 Heap) (var40 Heap) (var41 Addr) (var42 Int) (var43 Addr) (var44 Addr) (var45 Heap)) (or (not (and (inv_main1006_2 var45 var44 var43) (and (and (and (and (not (= var42 0)) (and (and (= var41 nullAddr) (and (and (and (= var40 var39) (= var38 var37)) (= var36 var35)) (= var41 (|TSLL::inner| (getTSLL (read var39 var35)))))) (and (and (and (= var34 var40) (= var33 var38)) (= var32 var36)) (= var31 (|TSLL::inner| (getTSLL (read var40 var36))))))) (and (and (and (= var30 var34) (= var29 var33)) (= var28 var32)) (or (and (= var31 nullAddr) (= var42 1)) (and (not (= var31 nullAddr)) (= var42 0))))) (and (and (and (and (and (and (= var27 (newHeap (alloc var26 (O_TSLL var25)))) (= var24 var23)) (= var22 var21)) (= var20 (newAddr (alloc var26 (O_TSLL var25))))) (and (= var19 0) (and (not (= var21 nullAddr)) (and (and (not (= nullAddr var21)) (and (and (and (and (and (= var18 var17) (= var16 var15)) (= var14 var13)) (= var12 (|TSLL::next| (getTSLL (read var17 var13))))) (and (and (and (and (= var11 (newHeap (alloc var45 (O_TSLL var10)))) (= var9 var44)) (= var8 var43)) (= var7 (newAddr (alloc var45 (O_TSLL var10))))) (not (= var6 0)))) (and (and (= var17 (write var11 var8 (O_TSLL (TSLL var7 (|TSLL::inner| (getTSLL (read var11 var8))))))) (= var15 var9)) (= var13 var8)))) (and (and (= var26 (write var18 var12 (O_TSLL (TSLL nullAddr (|TSLL::inner| (getTSLL (read var18 var12))))))) (= var23 var16)) (= var21 var12)))))) (and (and (= var5 (write var27 var22 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var27 var22))) var20)))) (= var4 var24)) (= var3 var22))) (and (and (= var2 (write var5 (|TSLL::inner| (getTSLL (read var5 var3))) (O_TSLL (TSLL nullAddr (|TSLL::inner| (getTSLL (read var5 (|TSLL::inner| (getTSLL (read var5 var3)))))))))) (= var1 var4)) (= var0 var3)))) (and (and (= var39 (write var2 (|TSLL::inner| (getTSLL (read var2 var0))) (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var2 (|TSLL::inner| (getTSLL (read var2 var0)))))) nullAddr)))) (= var37 var1)) (= var35 var0))))) (inv_main1006_2 var30 var29 var28))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 TSLL) (var3 Heap) (var4 Addr) (var5 Int) (var6 Addr) (var7 Addr) (var8 Heap) (var9 Heap) (var10 Addr) (var11 Heap)) (or (not (and (inv_main1002_2 var11) (and (and (and (not (= var10 nullAddr)) (and (and (= var9 var8) (= var7 var6)) (= var10 (|TSLL::inner| (getTSLL (read var8 var6)))))) (and (not (= var5 0)) (and (and (not (= var4 nullAddr)) (and (= var3 (newHeap (alloc var11 (O_TSLL var2)))) (= var1 (newAddr (alloc var11 (O_TSLL var2)))))) (and (= var0 (write var3 var1 (O_TSLL (TSLL nullAddr (|TSLL::inner| (getTSLL (read var3 var1))))))) (= var4 var1))))) (and (= var8 (write var0 var4 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var0 var4))) nullAddr)))) (= var6 var4))))) (inv_main1006_2 var9 var7 var7))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 TSLL) (var3 Heap) (var4 Addr) (var5 Int) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Heap) (var11 Addr) (var12 Addr) (var13 Heap) (var14 Heap) (var15 Addr) (var16 Int) (var17 Heap)) (or (not (and (inv_main1002_2 var17) (and (and (and (and (not (= var16 0)) (and (and (= var15 nullAddr) (and (and (= var14 var13) (= var12 var11)) (= var15 (|TSLL::inner| (getTSLL (read var13 var11)))))) (and (and (= var10 var14) (= var9 var12)) (= var8 (|TSLL::inner| (getTSLL (read var14 var12))))))) (and (and (= var7 var10) (= var6 var9)) (or (and (= var8 nullAddr) (= var16 1)) (and (not (= var8 nullAddr)) (= var16 0))))) (and (not (= var5 0)) (and (and (not (= var4 nullAddr)) (and (= var3 (newHeap (alloc var17 (O_TSLL var2)))) (= var1 (newAddr (alloc var17 (O_TSLL var2)))))) (and (= var0 (write var3 var1 (O_TSLL (TSLL nullAddr (|TSLL::inner| (getTSLL (read var3 var1))))))) (= var4 var1))))) (and (= var13 (write var0 var4 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var0 var4))) nullAddr)))) (= var11 var4))))) (inv_main1006_2 var7 var6 var6))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Heap) (var4 Addr) (var5 TSLL) (var6 Heap) (var7 Int) (var8 Addr) (var9 Addr) (var10 Addr) (var11 TSLL) (var12 Heap) (var13 Heap) (var14 Addr) (var15 Addr) (var16 Heap) (var17 Heap) (var18 Addr) (var19 Heap)) (or (not (and (inv_main1002_2 var19) (and (and (and (not (= var18 nullAddr)) (and (and (= var17 var16) (= var15 var14)) (= var18 (|TSLL::inner| (getTSLL (read var16 var14)))))) (and (and (and (and (and (= var13 (newHeap (alloc var12 (O_TSLL var11)))) (= var10 var9)) (= var8 (newAddr (alloc var12 (O_TSLL var11))))) (and (= var7 0) (and (and (not (= var9 nullAddr)) (and (= var6 (newHeap (alloc var19 (O_TSLL var5)))) (= var4 (newAddr (alloc var19 (O_TSLL var5)))))) (and (= var12 (write var6 var4 (O_TSLL (TSLL nullAddr (|TSLL::inner| (getTSLL (read var6 var4))))))) (= var9 var4))))) (and (= var3 (write var13 var10 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var13 var10))) var8)))) (= var2 var10))) (and (= var1 (write var3 (|TSLL::inner| (getTSLL (read var3 var2))) (O_TSLL (TSLL nullAddr (|TSLL::inner| (getTSLL (read var3 (|TSLL::inner| (getTSLL (read var3 var2)))))))))) (= var0 var2)))) (and (= var16 (write var1 (|TSLL::inner| (getTSLL (read var1 var0))) (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var1 (|TSLL::inner| (getTSLL (read var1 var0)))))) nullAddr)))) (= var14 var0))))) (inv_main1006_2 var17 var15 var15))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Heap) (var4 Addr) (var5 TSLL) (var6 Heap) (var7 Int) (var8 Addr) (var9 Addr) (var10 Addr) (var11 TSLL) (var12 Heap) (var13 Heap) (var14 Addr) (var15 Heap) (var16 Addr) (var17 Addr) (var18 Heap) (var19 Addr) (var20 Addr) (var21 Heap) (var22 Heap) (var23 Addr) (var24 Int) (var25 Heap)) (or (not (and (inv_main1002_2 var25) (and (and (and (and (not (= var24 0)) (and (and (= var23 nullAddr) (and (and (= var22 var21) (= var20 var19)) (= var23 (|TSLL::inner| (getTSLL (read var21 var19)))))) (and (and (= var18 var22) (= var17 var20)) (= var16 (|TSLL::inner| (getTSLL (read var22 var20))))))) (and (and (= var15 var18) (= var14 var17)) (or (and (= var16 nullAddr) (= var24 1)) (and (not (= var16 nullAddr)) (= var24 0))))) (and (and (and (and (and (= var13 (newHeap (alloc var12 (O_TSLL var11)))) (= var10 var9)) (= var8 (newAddr (alloc var12 (O_TSLL var11))))) (and (= var7 0) (and (and (not (= var9 nullAddr)) (and (= var6 (newHeap (alloc var25 (O_TSLL var5)))) (= var4 (newAddr (alloc var25 (O_TSLL var5)))))) (and (= var12 (write var6 var4 (O_TSLL (TSLL nullAddr (|TSLL::inner| (getTSLL (read var6 var4))))))) (= var9 var4))))) (and (= var3 (write var13 var10 (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var13 var10))) var8)))) (= var2 var10))) (and (= var1 (write var3 (|TSLL::inner| (getTSLL (read var3 var2))) (O_TSLL (TSLL nullAddr (|TSLL::inner| (getTSLL (read var3 (|TSLL::inner| (getTSLL (read var3 var2)))))))))) (= var0 var2)))) (and (= var21 (write var1 (|TSLL::inner| (getTSLL (read var1 var0))) (O_TSLL (TSLL (|TSLL::next| (getTSLL (read var1 (|TSLL::inner| (getTSLL (read var1 var0)))))) nullAddr)))) (= var19 var0))))) (inv_main1006_2 var15 var14 var14))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main_36 var6 var5 var4) (and (= nullAddr (|TSLL::next| (getTSLL (read var3 var2)))) (and (= nullAddr (|TSLL::inner| (getTSLL (read var3 var2)))) (and (not (= nullAddr var2)) (and (not (= nullAddr var2)) (and (and (and (and (= var3 var6) (= var1 var5)) (= var0 var4)) (= var2 (|TSLL::inner| (getTSLL (read var6 var5))))) (not (= nullAddr var5))))))))) (inv_main_64 var3 var1 var2))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Int) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Int) (var10 Addr) (var11 Addr) (var12 Heap)) (or (not (and (inv_main1028_3 var12 var11 var10 var9 var8) (and (and (and (not (= nullAddr var7)) (and (and (and (and (and (and (= var6 var12) (= var5 var11)) (= var4 var10)) (= var3 var9)) (= var2 var8)) (= var7 (|TSLL::next| (getTSLL (read var12 var10))))) (and (<= 0 (+ 1 (* (- 1) var9))) (= nullAddr var8)))) (= var1 0)) (= var0 (|TSLL::inner| (getTSLL (read var6 var7))))))) (inv_main1028_3 var6 var5 var7 var1 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main1006_2 var8 var7 var6) (and (and (and (not (= nullAddr var5)) (and (not (= nullAddr var5)) (and (= var4 0) (and (and (= var3 var8) (= var5 var7)) (= var2 nullAddr))))) (= var1 0)) (= var0 (|TSLL::inner| (getTSLL (read var3 var5))))))) (inv_main1028_3 var3 var5 var5 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Int) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main1028_3 var10 var9 var8 var7 var6) (and (and (and (and (and (and (and (= var5 var10) (= var4 var9)) (= var3 var8)) (= var2 1)) (= var1 var6)) (= var0 (|TSLL::inner| (getTSLL (read var10 var6))))) (and (= nullAddr (|TSLL::next| (getTSLL (read var10 var6)))) (and (= nullAddr (|TSLL::inner| (getTSLL (read var10 var6)))) (not (= nullAddr var6))))) (and (= var7 0) (not (= nullAddr var6)))))) (inv_main1028_3 var5 var4 var3 var2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Int) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main1028_3 var10 var9 var8 var7 var6) (and (and (and (and (and (and (and (= var5 var10) (= var4 var9)) (= var3 var8)) (= var2 2)) (= var1 var6)) (= var0 (|TSLL::inner| (getTSLL (read var10 var6))))) (and (= nullAddr (|TSLL::next| (getTSLL (read var10 var6)))) (and (= nullAddr (|TSLL::inner| (getTSLL (read var10 var6)))) (not (= nullAddr var6))))) (and (not (= var7 0)) (not (= nullAddr var6)))))) (inv_main1028_3 var5 var4 var3 var2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main_68 var5 var4 var3) (and (and (= var2 (write var5 var4 defObj)) (= var1 var4)) (= var0 var3)))) (inv_main_36 var2 var0 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Int) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main1028_3 var10 var9 var8 var7 var6) (and (= nullAddr var5) (and (and (and (and (and (and (= var4 var10) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var0 var6)) (= var5 (|TSLL::next| (getTSLL (read var10 var8))))) (and (<= 0 (+ 1 (* (- 1) var7))) (= nullAddr var6)))))) (inv_main_36 var4 var3 var5))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main1006_2 var6 var5 var4) (and (= nullAddr var3) (and (not (= nullAddr var3)) (and (= var2 0) (and (and (= var1 var6) (= var3 var5)) (= var0 nullAddr))))))) (inv_main_36 var1 var3 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main_36 var10 var9 var8) (and (and (and (and (= var7 var6) (= var5 var4)) (= var3 var2)) (= var1 (|TSLL::next| (getTSLL (read var6 var4))))) (and (= nullAddr var2) (and (and (and (and (= var6 var10) (= var4 var9)) (= var0 var8)) (= var2 (|TSLL::inner| (getTSLL (read var10 var9))))) (not (= nullAddr var9))))))) (inv_main_68 var7 var5 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Heap)) (or (not (and (inv_main_64 var12 var11 var10) (and (and (and (and (and (= var9 var8) (= var7 var6)) (= var5 var4)) (= var3 (|TSLL::next| (getTSLL (read var8 var6))))) (and (and (= var2 (write var12 var10 defObj)) (= var1 var11)) (= var0 var10))) (and (and (= var8 var2) (= var6 var1)) (= var4 nullAddr))))) (inv_main_68 var9 var7 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_64 var2 var1 var0) (and (not (= var0 nullAddr)) (= (read var2 var0) defObj))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_68 var2 var1 var0) (and (not (= var1 nullAddr)) (= (read var2 var1) defObj))))))
(check-sat)