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
                   ((dll (|dll::next| Addr) (|dll::prev| Addr) (|dll::data| Addr)))))
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
(declare-fun inv_main2424_5 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main2432_9 (Heap Addr Addr) Bool)
(declare-fun inv_main2435_9 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main2442_5 (Heap) Bool)
(declare-fun inv_main_3 (Heap Addr Addr Addr) Bool)
(assert (forall ((var0 Heap)) (or (not (= var0 emptyHeap)) (inv_main2442_5 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Int) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Heap) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Heap) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Addr) (var23 dll) (var24 Heap) (var25 Addr) (var26 Addr) (var27 Addr) (var28 Addr) (var29 Addr) (var30 Addr) (var31 Addr) (var32 Heap) (var33 Heap) (var34 Addr) (var35 Addr) (var36 Addr) (var37 Heap)) (or (not (and (inv_main_3 var37 var36 var35 var34) (and (and (and (and (and (and (= var33 var32) (= var31 var30)) (= var29 var28)) (= var27 var26)) (= var25 (|dll::next| (getdll (read var32 var28))))) (and (and (and (and (and (and (and (and (and (= var24 (newHeap (alloc var37 (O_dll var23)))) (= var22 var36)) (= var21 var35)) (= var20 var34)) (= var19 (newAddr (alloc var37 (O_dll var23))))) (and (and (and (and (= var18 (write var24 var19 (O_dll (dll nullAddr (|dll::prev| (getdll (read var24 var19))) (|dll::data| (getdll (read var24 var19))))))) (= var17 var22)) (= var16 var21)) (= var15 var20)) (= var14 var19))) (and (and (and (and (= var13 (write var18 var14 (O_dll (dll (|dll::next| (getdll (read var18 var14))) nullAddr (|dll::data| (getdll (read var18 var14))))))) (= var12 var17)) (= var11 var16)) (= var10 var15)) (= var9 var14))) (not (= var8 0))) (and (and (and (= var7 (write var13 var11 (O_dll (dll var9 (|dll::prev| (getdll (read var13 var11))) (|dll::data| (getdll (read var13 var11))))))) (= var6 var12)) (= var5 var11)) (= var4 var10))) (and (and (and (= var3 (write var7 (|dll::next| (getdll (read var7 var5))) (O_dll (dll (|dll::next| (getdll (read var7 (|dll::next| (getdll (read var7 var5)))))) var5 (|dll::data| (getdll (read var7 (|dll::next| (getdll (read var7 var5)))))))))) (= var2 var6)) (= var1 var5)) (= var0 var4)))) (and (and (and (= var32 (write var3 (|dll::next| (getdll (read var3 var1))) (O_dll (dll (|dll::next| (getdll (read var3 (|dll::next| (getdll (read var3 var1)))))) (|dll::prev| (getdll (read var3 (|dll::next| (getdll (read var3 var1)))))) var0)))) (= var30 var2)) (= var28 var1)) (= var26 var0))))) (inv_main_3 var33 var31 var25 var27))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Heap) (var3 Addr) (var4 dll) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Int) (var10 Heap) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Int) (var16 Heap) (var17 Heap) (var18 Heap)) (or (not (and (inv_main2442_5 var18) (and (and (and (and (and (and (= var17 (newHeap (alloc var16 (O_Int var15)))) (= var14 var13)) (= var12 var13)) (= var11 (newAddr (alloc var16 (O_Int var15))))) (and (and (and (= var10 (write var17 var11 (O_Int var9))) (= var8 var14)) (= var7 var12)) (= var6 var11))) (and (and (and (= var5 (newHeap (alloc var18 (O_dll var4)))) (= var3 (newAddr (alloc var18 (O_dll var4))))) (and (= var2 (write var5 var3 (O_dll (dll nullAddr (|dll::prev| (getdll (read var5 var3))) (|dll::data| (getdll (read var5 var3))))))) (= var1 var3))) (and (= var16 (write var2 var1 (O_dll (dll (|dll::next| (getdll (read var2 var1))) nullAddr (|dll::data| (getdll (read var2 var1))))))) (= var13 var1)))) (= var0 (write var10 var7 (O_dll (dll (|dll::next| (getdll (read var10 var7))) (|dll::prev| (getdll (read var10 var7))) var6))))))) (inv_main_3 var0 var8 var7 var6))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main2432_9 var6 var5 var4) (and (and (not (= var3 nullAddr)) (and (and (= var2 (write var6 (|dll::data| (getdll (read var6 var4))) defObj)) (= var1 var5)) (= var3 var4))) (= var0 (|dll::next| (getdll (read var2 var3))))))) (inv_main2435_9 var2 var1 var3 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main2435_9 var8 var7 var6 var5) (and (and (not (= var4 nullAddr)) (and (and (and (= var3 (write var8 var6 defObj)) (= var2 var7)) (= var1 var6)) (= var4 var5))) (= var0 (|dll::next| (getdll (read var3 var4))))))) (inv_main2435_9 var3 var2 var4 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main2424_5 var4 var3 var2 var1) (and (and (not (= var3 nullAddr)) (and (= var3 nullAddr) (= var1 nullAddr))) (= var0 (|dll::next| (getdll (read var4 var3))))))) (inv_main2435_9 var4 var3 var3 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main2424_5 var3 var2 var1 var0) (and (not (= var2 nullAddr)) (= var0 nullAddr)))) (inv_main2432_9 var3 var2 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Heap)) (or (not (and (inv_main2424_5 var13 var12 var11 var10) (and (and (and (and (and (= var9 var8) (= var7 var6)) (= var5 var4)) (= var3 var2)) (= var1 (|dll::next| (getdll (read var8 var2))))) (and (and (and (and (and (= var8 var13) (= var6 var12)) (= var4 var11)) (= var2 var10)) (= var0 (|dll::data| (getdll (read var13 var11))))) (not (= var10 nullAddr)))))) (inv_main2424_5 var9 var7 var5 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main_3 var4 var3 var2 var1) (= var0 0))) (inv_main2424_5 var4 var3 var3 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main2432_9 var2 var1 var0) (and (not (= (|dll::data| (getdll (read var2 var0))) nullAddr)) (= (read var2 (|dll::data| (getdll (read var2 var0)))) defObj))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main2435_9 var3 var2 var1 var0) (and (not (= var1 nullAddr)) (= (read var3 var1) defObj))))))
(check-sat)
