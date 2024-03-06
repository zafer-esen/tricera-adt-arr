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
(declare-fun inv_main (Heap Addr) Bool)
(declare-fun inv_main2396_1_5 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main2398_5 (Heap Addr) Bool)
(declare-fun inv_main2398_5_6 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main2416_5_12 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main2431_5 (Heap) Bool)
(declare-fun inv_main2433_5_14 (Heap Addr Addr) Bool)
(declare-fun inv_main_4 (Heap Addr Addr) Bool)
(declare-fun inv_main_7 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main_9 (Heap Addr Addr) Bool)
(assert (forall ((var0 Heap)) (or (not (= var0 emptyHeap)) (inv_main2431_5 var0))))
(assert (forall ((var0 Addr) (var1 dll) (var2 Heap) (var3 Heap)) (or (not (and (inv_main2431_5 var3) (and (= var2 (newHeap (alloc var3 (O_dll var1)))) (= var0 (newAddr (alloc var3 (O_dll var1))))))) (inv_main2398_5 var2 var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Heap)) (or (not (and (inv_main2398_5 var2 var1) (and (and (is-O_dll (read var2 var1)) (is-O_dll (read var2 var1))) (= var0 (write var2 var1 (O_dll (dll nullAddr (|dll::prev| (getdll (read var2 var1)))))))))) (inv_main var0 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main2416_5_12 var8 var7 var6 var5) (and (not (= var4 nullAddr)) (and (is-O_dll (read var8 var5)) (and (and (and (and (= var3 var8) (= var2 var7)) (= var1 var6)) (= var0 var5)) (= var4 (|dll::next| (getdll (read var8 var5))))))))) (inv_main2416_5_12 var3 var2 var1 var4))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Int) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main_9 var7 var6 var5) (and (not (= var4 nullAddr)) (and (= var3 0) (and (is-O_dll (read var7 var5)) (and (and (and (= var2 var7) (= var4 var6)) (= var1 var5)) (= var0 (|dll::next| (getdll (read var7 var5)))))))))) (inv_main2416_5_12 var2 var4 var4 var4))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main var4 var3) (and (not (= var2 nullAddr)) (and (= var1 0) (and (and (is-O_dll (read var4 var3)) (is-O_dll (read var4 var3))) (and (= var0 (write var4 var3 (O_dll (dll (|dll::next| (getdll (read var4 var3))) nullAddr)))) (= var2 var3))))))) (inv_main2416_5_12 var0 var2 var2 var2))))
(assert (forall ((var0 Addr) (var1 dll) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Int) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main_9 var10 var9 var8) (and (and (and (not (= var7 0)) (and (is-O_dll (read var10 var8)) (and (and (and (= var6 var10) (= var5 var9)) (= var4 var8)) (= var3 (|dll::next| (getdll (read var10 var8))))))) (= var2 (newHeap (alloc var6 (O_dll var1))))) (= var0 (newAddr (alloc var6 (O_dll var1))))))) (inv_main2398_5_6 var2 var5 var3 var0))))
(assert (forall ((var0 Addr) (var1 dll) (var2 Heap) (var3 Addr) (var4 Heap) (var5 Int) (var6 Addr) (var7 Heap)) (or (not (and (inv_main var7 var6) (and (and (and (not (= var5 0)) (and (and (is-O_dll (read var7 var6)) (is-O_dll (read var7 var6))) (and (= var4 (write var7 var6 (O_dll (dll (|dll::next| (getdll (read var7 var6))) nullAddr)))) (= var3 var6)))) (= var2 (newHeap (alloc var4 (O_dll var1))))) (= var0 (newAddr (alloc var4 (O_dll var1))))))) (inv_main2398_5_6 var2 var3 var3 var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main2398_5_6 var4 var3 var2 var1) (and (and (is-O_dll (read var4 var1)) (is-O_dll (read var4 var1))) (= var0 (write var4 var1 (O_dll (dll nullAddr (|dll::prev| (getdll (read var4 var1)))))))))) (inv_main_7 var0 var3 var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main_7 var7 var6 var5 var4) (and (and (is-O_dll (read var7 var4)) (is-O_dll (read var7 var4))) (and (and (and (= var3 (write var7 var4 (O_dll (dll (|dll::next| (getdll (read var7 var4))) nullAddr)))) (= var2 var6)) (= var1 var5)) (= var0 var4))))) (inv_main2396_1_5 var3 var2 var1 var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main_4 var3 var2 var1) (and (and (and (is-O_dll (read var3 var1)) (is-O_dll (read var3 (|dll::next| (getdll (read var3 var1)))))) (is-O_dll (read var3 (|dll::next| (getdll (read var3 var1)))))) (= var0 (write var3 (|dll::next| (getdll (read var3 var1))) (O_dll (dll (|dll::next| (getdll (read var3 (|dll::next| (getdll (read var3 var1)))))) var1))))))) (inv_main_9 var0 var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main2433_5_14 var10 var9 var8) (and (not (= var7 nullAddr)) (and (and (is-O_dll (read var10 var8)) (and (and (and (= var6 var10) (= var5 var9)) (= var4 var8)) (= var3 (|dll::next| (getdll (read var10 var8)))))) (and (and (and (= var2 (write var6 var4 defObj)) (= var1 var5)) (= var0 var4)) (= var7 var3)))))) (inv_main2433_5_14 var2 var1 var7))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main2416_5_12 var8 var7 var6 var5) (and (not (= var4 nullAddr)) (and (= var3 nullAddr) (and (is-O_dll (read var8 var5)) (and (and (and (and (= var2 var8) (= var4 var7)) (= var1 var6)) (= var0 var5)) (= var3 (|dll::next| (getdll (read var8 var5)))))))))) (inv_main2433_5_14 var2 var4 var4))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Int) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main_9 var7 var6 var5) (and (not (= var4 nullAddr)) (and (= var4 nullAddr) (and (= var3 0) (and (is-O_dll (read var7 var5)) (and (and (and (= var2 var7) (= var4 var6)) (= var1 var5)) (= var0 (|dll::next| (getdll (read var7 var5))))))))))) (inv_main2433_5_14 var2 var4 var4))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main var4 var3) (and (not (= var2 nullAddr)) (and (= var2 nullAddr) (and (= var1 0) (and (and (is-O_dll (read var4 var3)) (is-O_dll (read var4 var3))) (and (= var0 (write var4 var3 (O_dll (dll (|dll::next| (getdll (read var4 var3))) nullAddr)))) (= var2 var3)))))))) (inv_main2433_5_14 var0 var2 var2))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main2396_1_5 var4 var3 var2 var1) (and (and (is-O_dll (read var4 var2)) (is-O_dll (read var4 var2))) (= var0 (write var4 var2 (O_dll (dll var1 (|dll::prev| (getdll (read var4 var2)))))))))) (inv_main_4 var0 var3 var2))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main2398_5 var1 var0) (not (is-O_dll (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main2398_5 var1 var0) (and (is-O_dll (read var1 var0)) (not (is-O_dll (read var1 var0))))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main var1 var0) (not (is-O_dll (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main var1 var0) (and (is-O_dll (read var1 var0)) (not (is-O_dll (read var1 var0))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main2398_5_6 var3 var2 var1 var0) (not (is-O_dll (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main2398_5_6 var3 var2 var1 var0) (and (is-O_dll (read var3 var0)) (not (is-O_dll (read var3 var0))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_7 var3 var2 var1 var0) (not (is-O_dll (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_7 var3 var2 var1 var0) (and (is-O_dll (read var3 var0)) (not (is-O_dll (read var3 var0))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main2396_1_5 var3 var2 var1 var0) (not (is-O_dll (read var3 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main2396_1_5 var3 var2 var1 var0) (and (is-O_dll (read var3 var1)) (not (is-O_dll (read var3 var1))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_4 var2 var1 var0) (not (is-O_dll (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_4 var2 var1 var0) (and (is-O_dll (read var2 var0)) (not (is-O_dll (read var2 (|dll::next| (getdll (read var2 var0)))))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_4 var2 var1 var0) (and (and (is-O_dll (read var2 var0)) (is-O_dll (read var2 (|dll::next| (getdll (read var2 var0)))))) (not (is-O_dll (read var2 (|dll::next| (getdll (read var2 var0)))))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_9 var2 var1 var0) (not (is-O_dll (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main2416_5_12 var3 var2 var1 var0) (not (is-O_dll (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main2433_5_14 var2 var1 var0) (not (is-O_dll (read var2 var0)))))))
(check-sat)
