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

(declare-datatypes ((HeapObject 0) (dll 0))
                   (((O_Int (getInt Int)) (O_UInt (getUInt Int)) (O_Addr (getAddr Addr)) (O_AddrRange (getAddrRange AddrRange)) (O_dll (getdll dll)) (defObj))
                   ((dll (|dll::next| Addr) (|dll::prev| Addr)))))
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
(declare-fun inv_main2406_5 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main2416_5 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main2424_5 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main2439_5 (Heap Addr) Bool)
(declare-fun inv_main2443_5 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main2444_12 (Heap Addr Int) Bool)
(assert (forall ((var0 Addr) (var1 Heap)) (or (not (and (= var1 emptyHeap) (= var0 nullAddr))) (inv_main2439_5 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main2443_5 var4 var3 var2 var1) (and (= var1 nullAddr) (= var0 0)))) (inv_main2444_12 var4 var3 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Heap)) (or (not (and (inv_main2443_5 var13 var12 var11 var10) (and (and (and (and (and (and (= var9 var13) (= var8 var12)) (= var7 var11)) (= var6 var10)) (= var5 (|dll::prev| (getdll (read var13 var10))))) (and (and (and (and (= var4 (write var9 var6 defObj)) (or (and (= var8 var6) (= var3 nullAddr)) (and (not (= var8 var6)) (= var3 var8)))) (= var2 var7)) (= var1 var6)) (= var0 var5))) (not (= var10 nullAddr))))) (inv_main2443_5 var4 var3 var2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main2424_5 var4 var3 var2 var1 var0) (= var0 nullAddr))) (inv_main2443_5 var4 var3 var2 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main2416_5 var10 var9 var8 var7 var6) (and (not (= var5 nullAddr)) (and (and (and (and (and (= var4 var10) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var0 var6)) (= var5 (|dll::next| (getdll (read var10 var7)))))))) (inv_main2416_5 var4 var3 var2 var5 var5))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main2406_5 var5 var4 var3 var2) (= var1 0))) (inv_main2416_5 var5 var4 var3 var3 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Heap) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Bool) (var19 Addr) (var20 dll) (var21 Heap) (var22 Addr) (var23 Addr) (var24 Addr) (var25 Addr) (var26 Addr) (var27 Addr) (var28 Addr) (var29 Heap) (var30 Heap) (var31 Addr) (var32 Addr) (var33 Addr) (var34 Heap)) (or (not (and (inv_main2406_5 var34 var33 var32 var31) (and (and (and (and (and (and (= var30 var29) (= var28 var27)) (= var26 var25)) (= var24 var23)) (= var22 (|dll::next| (getdll (read var29 var23))))) (and (and (and (and (and (and (and (and (= var21 (newHeap (alloc var34 (O_dll var20)))) (or (and var18 (= var19 (newAddr (alloc var34 (O_dll var20))))) (and (not var18) (= var19 var33)))) (= var17 var32)) (= var16 var31)) (= var15 (newAddr (alloc var34 (O_dll var20))))) (and (and (and (and (= var14 (write var21 var15 (O_dll (dll nullAddr (|dll::prev| (getdll (read var21 var15))))))) (= var13 var19)) (= var12 var17)) (= var11 var16)) (= var10 var15))) (and (and (and (and (= var9 (write var14 var10 (O_dll (dll (|dll::next| (getdll (read var14 var10))) nullAddr)))) (= var8 var13)) (= var7 var12)) (= var6 var11)) (= var5 var10))) (not (= var4 0))) (and (and (and (= var3 (write var9 var6 (O_dll (dll var5 (|dll::prev| (getdll (read var9 var6))))))) (= var2 var8)) (= var1 var7)) (= var0 var6)))) (and (and (and (= var29 (write var3 (|dll::next| (getdll (read var3 var0))) (O_dll (dll (|dll::next| (getdll (read var3 (|dll::next| (getdll (read var3 var0)))))) var0)))) (= var27 var2)) (= var25 var1)) (= var23 var0))))) (inv_main2406_5 var30 var28 var26 var22))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Bool) (var8 Addr) (var9 dll) (var10 Heap) (var11 Addr) (var12 Heap)) (or (not (and (inv_main2439_5 var12 var11) (and (and (and (and (= var10 (newHeap (alloc var12 (O_dll var9)))) (or (and var7 (= var8 (newAddr (alloc var12 (O_dll var9))))) (and (not var7) (= var8 var11)))) (= var6 (newAddr (alloc var12 (O_dll var9))))) (and (and (= var5 (write var10 var6 (O_dll (dll nullAddr (|dll::prev| (getdll (read var10 var6))))))) (= var4 var8)) (= var3 var6))) (and (and (= var2 (write var5 var3 (O_dll (dll (|dll::next| (getdll (read var5 var3))) nullAddr)))) (= var1 var4)) (= var0 var3))))) (inv_main2406_5 var2 var1 var0 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main2424_5 var10 var9 var8 var7 var6) (and (and (and (and (and (and (= var5 var10) (= var4 var9)) (= var3 var8)) (= var2 var7)) (= var1 var6)) (= var0 (|dll::prev| (getdll (read var10 var6))))) (not (= var6 nullAddr))))) (inv_main2424_5 var5 var4 var3 var2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main2416_5 var10 var9 var8 var7 var6) (and (= var5 nullAddr) (and (and (and (and (and (= var4 var10) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var0 var6)) (= var5 (|dll::next| (getdll (read var10 var7)))))))) (inv_main2424_5 var4 var3 var1 var1 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap)) (not (and (inv_main2444_12 var2 var1 var0) (not (= var1 nullAddr))))))
(check-sat)
