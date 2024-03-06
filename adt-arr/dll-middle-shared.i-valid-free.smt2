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

(declare-datatypes ((HeapObject 0) (dll 0))
                   (((O_Int (getInt Int)) (O_UInt (getUInt Int)) (O_Addr (getAddr Addr)) (O_AddrRange (getAddrRange AddrRange)) (O_dll (getdll dll)) (defObj))
                   ((dll (|dll::data1| Addr) (|dll::next| Addr) (|dll::prev| Addr) (|dll::data2| Addr)))))
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
(declare-fun inv_main2430_5 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main2438_9 (Heap Addr Addr) Bool)
(declare-fun inv_main2443_9 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main2450_5 (Heap) Bool)
(declare-fun inv_main_24 (Heap Addr Addr) Bool)
(declare-fun inv_main_5 (Heap Addr Addr Addr Addr) Bool)
(assert (forall ((var0 Heap)) (or (not (= var0 emptyHeap)) (inv_main2450_5 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main_24 var6 var5 var4) (and (and (not (= var3 nullAddr)) (and (and (= var2 (write var6 (|dll::data2| (getdll (read var6 var4))) defObj)) (= var1 var5)) (= var3 var4))) (= var0 (|dll::next| (getdll (read var2 var3))))))) (inv_main2443_9 var2 var1 var3 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main2443_9 var8 var7 var6 var5) (and (and (not (= var4 nullAddr)) (and (and (and (= var3 (write var8 var6 defObj)) (= var2 var7)) (= var1 var6)) (= var4 var5))) (= var0 (|dll::next| (getdll (read var3 var4))))))) (inv_main2443_9 var3 var2 var4 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main2430_5 var4 var3 var2 var1) (and (and (not (= var3 nullAddr)) (and (= var3 nullAddr) (= var1 nullAddr))) (= var0 (|dll::next| (getdll (read var4 var3))))))) (inv_main2443_9 var4 var3 var3 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Heap) (var15 Int) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Heap) (var22 Addr) (var23 Addr) (var24 Addr) (var25 Addr) (var26 Addr) (var27 Heap) (var28 Addr) (var29 Addr) (var30 Addr) (var31 Addr) (var32 Addr) (var33 dll) (var34 Heap) (var35 Addr) (var36 Addr) (var37 Addr) (var38 Addr) (var39 Addr) (var40 Addr) (var41 Addr) (var42 Addr) (var43 Addr) (var44 Heap) (var45 Heap) (var46 Addr) (var47 Addr) (var48 Addr) (var49 Addr) (var50 Heap)) (or (not (and (inv_main_5 var50 var49 var48 var47 var46) (and (and (and (and (and (and (and (= var45 var44) (= var43 var42)) (= var41 var40)) (= var39 var38)) (= var37 var36)) (= var35 (|dll::next| (getdll (read var44 var40))))) (and (and (and (and (and (and (and (and (and (and (and (= var34 (newHeap (alloc var50 (O_dll var33)))) (= var32 var49)) (= var31 var48)) (= var30 var47)) (= var29 var46)) (= var28 (newAddr (alloc var50 (O_dll var33))))) (and (and (and (and (and (= var27 (write var34 var28 (O_dll (dll (|dll::data1| (getdll (read var34 var28))) nullAddr (|dll::prev| (getdll (read var34 var28))) (|dll::data2| (getdll (read var34 var28))))))) (= var26 var32)) (= var25 var31)) (= var24 var30)) (= var23 var29)) (= var22 var28))) (and (and (and (and (and (= var21 (write var27 var22 (O_dll (dll (|dll::data1| (getdll (read var27 var22))) (|dll::next| (getdll (read var27 var22))) nullAddr (|dll::data2| (getdll (read var27 var22))))))) (= var20 var26)) (= var19 var25)) (= var18 var24)) (= var17 var23)) (= var16 var22))) (not (= var15 0))) (and (and (and (and (= var14 (write var21 var19 (O_dll (dll (|dll::data1| (getdll (read var21 var19))) var16 (|dll::prev| (getdll (read var21 var19))) (|dll::data2| (getdll (read var21 var19))))))) (= var13 var20)) (= var12 var19)) (= var11 var18)) (= var10 var17))) (and (and (and (and (= var9 (write var14 (|dll::next| (getdll (read var14 var12))) (O_dll (dll (|dll::data1| (getdll (read var14 (|dll::next| (getdll (read var14 var12)))))) (|dll::next| (getdll (read var14 (|dll::next| (getdll (read var14 var12)))))) var12 (|dll::data2| (getdll (read var14 (|dll::next| (getdll (read var14 var12)))))))))) (= var8 var13)) (= var7 var12)) (= var6 var11)) (= var5 var10))) (and (and (and (and (= var4 (write var9 (|dll::next| (getdll (read var9 var7))) (O_dll (dll var6 (|dll::next| (getdll (read var9 (|dll::next| (getdll (read var9 var7)))))) (|dll::prev| (getdll (read var9 (|dll::next| (getdll (read var9 var7)))))) (|dll::data2| (getdll (read var9 (|dll::next| (getdll (read var9 var7)))))))))) (= var3 var8)) (= var2 var7)) (= var1 var6)) (= var0 var5)))) (and (and (and (and (= var44 (write var4 (|dll::next| (getdll (read var4 var2))) (O_dll (dll (|dll::data1| (getdll (read var4 (|dll::next| (getdll (read var4 var2)))))) (|dll::next| (getdll (read var4 (|dll::next| (getdll (read var4 var2)))))) (|dll::prev| (getdll (read var4 (|dll::next| (getdll (read var4 var2)))))) var0)))) (= var42 var3)) (= var40 var2)) (= var38 var1)) (= var36 var0))))) (inv_main_5 var45 var43 var35 var39 var37))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Heap) (var3 Addr) (var4 dll) (var5 Heap) (var6 Int) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Int) (var12 Heap) (var13 Heap) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Heap) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Int) (var24 Heap) (var25 Addr) (var26 Addr) (var27 Addr) (var28 Addr) (var29 Addr) (var30 Addr) (var31 Addr) (var32 Int) (var33 Heap) (var34 Heap) (var35 Heap)) (or (not (and (inv_main2450_5 var35) (and (and (and (and (and (and (and (and (and (and (= var34 (newHeap (alloc var33 (O_Int var32)))) (= var31 var30)) (= var29 var28)) (= var27 var26)) (= var25 (newAddr (alloc var33 (O_Int var32))))) (and (and (and (and (= var24 (write var34 var25 (O_Int var23))) (= var22 var31)) (= var21 var29)) (= var20 var27)) (= var19 var25))) (and (and (and (and (= var18 (write var24 var21 (O_dll (dll var20 (|dll::next| (getdll (read var24 var21))) (|dll::prev| (getdll (read var24 var21))) (|dll::data2| (getdll (read var24 var21))))))) (= var17 var22)) (= var16 var21)) (= var15 var20)) (= var14 var19))) (and (and (and (= var13 (newHeap (alloc var12 (O_Int var11)))) (= var10 var9)) (= var8 var9)) (= var7 (newAddr (alloc var12 (O_Int var11)))))) (and (and (and (= var33 (write var13 var7 (O_Int var6))) (= var30 var10)) (= var28 var8)) (= var26 var7))) (and (and (and (= var5 (newHeap (alloc var35 (O_dll var4)))) (= var3 (newAddr (alloc var35 (O_dll var4))))) (and (= var2 (write var5 var3 (O_dll (dll (|dll::data1| (getdll (read var5 var3))) nullAddr (|dll::prev| (getdll (read var5 var3))) (|dll::data2| (getdll (read var5 var3))))))) (= var1 var3))) (and (= var12 (write var2 var1 (O_dll (dll (|dll::data1| (getdll (read var2 var1))) (|dll::next| (getdll (read var2 var1))) nullAddr (|dll::data2| (getdll (read var2 var1))))))) (= var9 var1)))) (= var0 (write var18 var16 (O_dll (dll (|dll::data1| (getdll (read var18 var16))) (|dll::next| (getdll (read var18 var16))) (|dll::prev| (getdll (read var18 var16))) var14))))))) (inv_main_5 var0 var17 var16 var15 var14))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main2430_5 var3 var2 var1 var0) (and (not (= var2 nullAddr)) (= var0 nullAddr)))) (inv_main2438_9 var3 var2 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap) (var10 Heap) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Heap)) (or (not (and (inv_main2430_5 var14 var13 var12 var11) (and (and (and (and (and (= var10 var9) (= var8 var7)) (= var6 var5)) (= var4 var3)) (= var2 (|dll::next| (getdll (read var9 var3))))) (and (and (and (and (and (and (= var9 var14) (= var7 var13)) (= var5 var12)) (= var3 var11)) (= var1 (|dll::data1| (getdll (read var14 var12))))) (= var0 (|dll::data2| (getdll (read var14 var12))))) (not (= var11 nullAddr)))))) (inv_main2430_5 var10 var8 var6 var2))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main_5 var5 var4 var3 var2 var1) (= var0 0))) (inv_main2430_5 var5 var4 var4 var4))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main2438_9 var3 var2 var1) (= var0 (write var3 (|dll::data1| (getdll (read var3 var1))) defObj)))) (inv_main_24 var0 var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main2438_9 var2 var1 var0) (and (not (= (|dll::data1| (getdll (read var2 var0))) nullAddr)) (= (read var2 (|dll::data1| (getdll (read var2 var0)))) defObj))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_24 var2 var1 var0) (and (not (= (|dll::data2| (getdll (read var2 var0))) nullAddr)) (= (read var2 (|dll::data2| (getdll (read var2 var0)))) defObj))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main2443_9 var3 var2 var1 var0) (and (not (= var1 nullAddr)) (= (read var3 var1) defObj))))))
(check-sat)
