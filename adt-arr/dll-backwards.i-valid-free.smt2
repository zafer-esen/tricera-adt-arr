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
(declare-fun inv_main2406_5 (Heap Addr Addr) Bool)
(declare-fun inv_main2416_5 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main2424_5 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main2432_9 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main2439_5 (Heap) Bool)
(assert (forall ((var0 Heap)) (or (not (= var0 emptyHeap)) (inv_main2439_5 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main2432_9 var8 var7 var6 var5) (and (and (not (= var4 nullAddr)) (and (and (and (= var3 (write var8 var6 defObj)) (= var2 var7)) (= var1 var6)) (= var4 var5))) (= var0 (|dll::prev| (getdll (read var3 var4))))))) (inv_main2432_9 var3 var2 var4 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main2424_5 var4 var3 var2 var1) (and (and (not (= var3 nullAddr)) (= var1 nullAddr)) (= var0 (|dll::prev| (getdll (read var4 var3))))))) (inv_main2432_9 var4 var3 var3 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Int) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Heap) (var12 Addr) (var13 Addr) (var14 Addr) (var15 dll) (var16 Heap) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Heap) (var23 Heap) (var24 Addr) (var25 Addr) (var26 Heap)) (or (not (and (inv_main2406_5 var26 var25 var24) (and (and (and (and (and (= var23 var22) (= var21 var20)) (= var19 var18)) (= var17 (|dll::next| (getdll (read var22 var18))))) (and (and (and (and (and (and (and (= var16 (newHeap (alloc var26 (O_dll var15)))) (= var14 var25)) (= var13 var24)) (= var12 (newAddr (alloc var26 (O_dll var15))))) (and (and (and (= var11 (write var16 var12 (O_dll (dll nullAddr (|dll::prev| (getdll (read var16 var12))))))) (= var10 var14)) (= var9 var13)) (= var8 var12))) (and (and (and (= var7 (write var11 var8 (O_dll (dll (|dll::next| (getdll (read var11 var8))) nullAddr)))) (= var6 var10)) (= var5 var9)) (= var4 var8))) (not (= var3 0))) (and (and (= var2 (write var7 var5 (O_dll (dll var4 (|dll::prev| (getdll (read var7 var5))))))) (= var1 var6)) (= var0 var5)))) (and (and (= var22 (write var2 (|dll::next| (getdll (read var2 var0))) (O_dll (dll (|dll::next| (getdll (read var2 (|dll::next| (getdll (read var2 var0)))))) var0)))) (= var20 var1)) (= var18 var0))))) (inv_main2406_5 var23 var21 var17))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Heap) (var4 Addr) (var5 dll) (var6 Heap) (var7 Heap)) (or (not (and (inv_main2439_5 var7) (and (and (and (= var6 (newHeap (alloc var7 (O_dll var5)))) (= var4 (newAddr (alloc var7 (O_dll var5))))) (and (= var3 (write var6 var4 (O_dll (dll nullAddr (|dll::prev| (getdll (read var6 var4))))))) (= var2 var4))) (and (= var1 (write var3 var2 (O_dll (dll (|dll::next| (getdll (read var3 var2))) nullAddr)))) (= var0 var2))))) (inv_main2406_5 var1 var0 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main2424_5 var8 var7 var6 var5) (and (and (and (and (and (= var4 var8) (= var3 var7)) (= var2 var6)) (= var1 var5)) (= var0 (|dll::prev| (getdll (read var8 var5))))) (not (= var5 nullAddr))))) (inv_main2424_5 var4 var3 var2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main2416_5 var8 var7 var6 var5) (and (= var4 nullAddr) (and (and (and (and (= var3 var8) (= var2 var7)) (= var1 var6)) (= var0 var5)) (= var4 (|dll::next| (getdll (read var8 var6)))))))) (inv_main2424_5 var3 var1 var1 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main2416_5 var8 var7 var6 var5) (and (not (= var4 nullAddr)) (and (and (and (and (= var3 var8) (= var2 var7)) (= var1 var6)) (= var0 var5)) (= var4 (|dll::next| (getdll (read var8 var6)))))))) (inv_main2416_5 var3 var2 var4 var4))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main2406_5 var4 var3 var2) (= var1 0))) (inv_main2416_5 var4 var3 var3 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main2432_9 var3 var2 var1 var0) (and (not (= var1 nullAddr)) (= (read var3 var1) defObj))))))
(check-sat)
