(set-logic HORN)
(set-info :source |
    Benchmark: C_VC
    Output by Princess (http://www.philipp.ruemmer.org/princess.shtml)
|)
(set-info :status unsat)
;===============================================================================
; Encoding of Heap sorts and operations
;-------------------------------------------------------------------------------
(define-sort Addr() Int)
(declare-datatypes ((AddrRange 0))
                   (((AddrRange (AddrRangeStart Addr) (AddrRangeSize Int)))))

(declare-datatypes ((HeapObject 0) (node 0))
                   (((O_Int (getInt Int)) (O_UInt (getUInt Int)) (O_Addr (getAddr Addr)) (O_AddrRange (getAddrRange AddrRange)) (O_node (getnode node)) (defObj))
                   ((node (|node::left| Addr) (|node::right| Addr) (|node::parent| Addr) (|node::value| Int)))))
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
(declare-fun inv_main577_13 (Heap Addr Addr) Bool)
(declare-fun inv_main586_5 (Heap Addr Addr) Bool)
(declare-fun inv_main593_13 (Heap Addr Addr) Bool)
(declare-fun inv_main595_9 (Heap Addr Addr Int) Bool)
(declare-fun inv_main600_9 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main612_5_40 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main619_13 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main621_13 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main630_5 (Heap) Bool)
(declare-fun inv_main_13 (Heap Addr Addr) Bool)
(declare-fun inv_main_15 (Heap Addr Addr) Bool)
(declare-fun inv_main_16 (Heap Addr Addr) Bool)
(declare-fun inv_main_17 (Heap Addr Addr) Bool)
(declare-fun inv_main_18 (Heap Addr Addr) Bool)
(declare-fun inv_main_26 (Heap Addr Addr) Bool)
(declare-fun inv_main_27 (Heap Addr Addr) Bool)
(declare-fun inv_main_3 (Heap Addr Addr) Bool)
(declare-fun inv_main_33 (Heap Addr Addr) Bool)
(declare-fun inv_main_41 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main_45 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main_46 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main_5 (Heap Addr Addr) Bool)
(declare-fun inv_main_50 (Heap Addr Addr Addr) Bool)
(assert (forall ((var0 Heap)) (or (not (= var0 emptyHeap)) (inv_main630_5 var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main_3 var3 var2 var1) (and (and (is-O_node (read var3 var1)) (is-O_node (read var3 var1))) (= var0 (write var3 var1 (O_node (node nullAddr (|node::right| (getnode (read var3 var1))) (|node::parent| (getnode (read var3 var1))) (|node::value| (getnode (read var3 var1)))))))))) (inv_main_5 var0 var2 var1))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main_13 var3 var2 var1) (and (and (and (is-O_node (read var3 var1)) (is-O_node (read var3 (|node::left| (getnode (read var3 var1)))))) (is-O_node (read var3 (|node::left| (getnode (read var3 var1)))))) (= var0 (write var3 (|node::left| (getnode (read var3 var1))) (O_node (node nullAddr (|node::right| (getnode (read var3 (|node::left| (getnode (read var3 var1)))))) (|node::parent| (getnode (read var3 (|node::left| (getnode (read var3 var1)))))) (|node::value| (getnode (read var3 (|node::left| (getnode (read var3 var1))))))))))))) (inv_main_15 var0 var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main_33 var6 var5 var4) (and (not (= var3 nullAddr)) (and (is-O_node (read var6 var4)) (and (and (and (= var2 var6) (= var1 var5)) (= var0 var4)) (= var3 (|node::parent| (getnode (read var6 var4))))))))) (inv_main_26 var2 var1 var3))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main_18 var6 var5 var4) (and (and (not (= var3 nullAddr)) (not (= var3 nullAddr))) (and (not (= var3 nullAddr)) (and (= var2 nullAddr) (and (is-O_node (read var6 var4)) (and (and (and (= var1 var6) (= var3 var5)) (= var0 var4)) (= var2 (|node::right| (getnode (read var6 var4))))))))))) (inv_main_26 var1 var3 var3))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main586_5 var3 var2 var1) (and (and (not (= var2 nullAddr)) (not (= var2 nullAddr))) (and (not (= var2 nullAddr)) (and (= var1 nullAddr) (= var0 0)))))) (inv_main_26 var3 var2 var2))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main_15 var3 var2 var1) (and (and (and (is-O_node (read var3 var1)) (is-O_node (read var3 (|node::left| (getnode (read var3 var1)))))) (is-O_node (read var3 (|node::left| (getnode (read var3 var1)))))) (= var0 (write var3 (|node::left| (getnode (read var3 var1))) (O_node (node (|node::left| (getnode (read var3 (|node::left| (getnode (read var3 var1)))))) nullAddr (|node::parent| (getnode (read var3 (|node::left| (getnode (read var3 var1)))))) (|node::value| (getnode (read var3 (|node::left| (getnode (read var3 var1))))))))))))) (inv_main_16 var0 var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main612_5_40 var8 var7 var6 var5) (and (and (not (= var4 nullAddr)) (is-O_node (read var8 var6))) (and (and (and (and (= var3 var8) (= var2 var7)) (= var1 var6)) (= var0 var5)) (= var4 (|node::right| (getnode (read var8 var6)))))))) (inv_main_41 var3 var2 var1 var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main_17 var3 var2 var1) (and (and (and (is-O_node (read var3 var1)) (is-O_node (read var3 (|node::left| (getnode (read var3 var1)))))) (is-O_node (read var3 (|node::left| (getnode (read var3 var1)))))) (= var0 (write var3 (|node::left| (getnode (read var3 var1))) (O_node (node (|node::left| (getnode (read var3 (|node::left| (getnode (read var3 var1)))))) (|node::right| (getnode (read var3 (|node::left| (getnode (read var3 var1)))))) var1 (|node::value| (getnode (read var3 (|node::left| (getnode (read var3 var1))))))))))))) (inv_main_18 var0 var2 var1))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main_5 var5 var4 var3) (and (and (not (= var2 nullAddr)) (and (is-O_node (read var5 var3)) (is-O_node (read var5 var3)))) (and (and (= var1 (write var5 var3 (O_node (node (|node::left| (getnode (read var5 var3))) var4 (|node::parent| (getnode (read var5 var3))) (|node::value| (getnode (read var5 var3))))))) (= var2 var4)) (= var0 var3))))) (inv_main593_13 var1 var2 var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main619_13 var4 var3 var2 var1) (and (is-O_node (read var4 var2)) (= var0 (write var4 (|node::left| (getnode (read var4 var2))) defObj))))) (inv_main_46 var0 var3 var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main_45 var3 var2 var1 var0) (and (is-O_node (read var3 var1)) (= (|node::left| (getnode (read var3 var1))) nullAddr)))) (inv_main_46 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main_41 var8 var7 var6 var5) (and (is-O_node (read var8 var6)) (and (and (and (and (= var4 var8) (= var3 var7)) (= var2 var6)) (= var1 var5)) (= var0 (|node::right| (getnode (read var8 var6)))))))) (inv_main612_5_40 var4 var3 var0 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main_33 var10 var9 var8) (and (and (and (and (= var7 var6) (= var5 var4)) (= var3 var4)) (= var2 nullAddr)) (and (= var1 nullAddr) (and (is-O_node (read var10 var8)) (and (and (and (= var6 var10) (= var4 var9)) (= var0 var8)) (= var1 (|node::parent| (getnode (read var10 var8)))))))))) (inv_main612_5_40 var7 var5 var3 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main_18 var10 var9 var8) (and (and (and (and (and (= var7 var6) (= var5 var4)) (= var3 var4)) (= var2 nullAddr)) (and (= var4 nullAddr) (not (= var4 nullAddr)))) (and (not (= var4 nullAddr)) (and (= var1 nullAddr) (and (is-O_node (read var10 var8)) (and (and (and (= var6 var10) (= var4 var9)) (= var0 var8)) (= var1 (|node::right| (getnode (read var10 var8))))))))))) (inv_main612_5_40 var7 var5 var3 var2))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main586_5 var7 var6 var5) (and (and (and (and (and (= var4 var7) (= var3 var6)) (= var2 var6)) (= var1 nullAddr)) (and (= var6 nullAddr) (not (= var6 nullAddr)))) (and (not (= var6 nullAddr)) (and (= var5 nullAddr) (= var0 0)))))) (inv_main612_5_40 var4 var3 var2 var1))))
(assert (forall ((var0 Addr) (var1 node) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main_18 var9 var8 var7) (and (and (and (not (= var6 nullAddr)) (and (is-O_node (read var9 var7)) (and (and (and (= var5 var9) (= var4 var8)) (= var3 var7)) (= var6 (|node::right| (getnode (read var9 var7))))))) (= var2 (newHeap (alloc var5 (O_node var1))))) (= var0 (newAddr (alloc var5 (O_node var1))))))) (inv_main600_9 var2 var4 var6 var0))))
(assert (forall ((var0 Addr) (var1 node) (var2 Heap) (var3 Int) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main586_5 var6 var5 var4) (and (and (and (not (= var4 nullAddr)) (= var3 0)) (= var2 (newHeap (alloc var6 (O_node var1))))) (= var0 (newAddr (alloc var6 (O_node var1))))))) (inv_main600_9 var2 var5 var4 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main593_13 var6 var5 var4) (and (and (is-O_node (read var6 var5)) (is-O_node (read var6 var5))) (and (and (= var3 (write var6 var5 (O_node (node (|node::left| (getnode (read var6 var5))) (|node::right| (getnode (read var6 var5))) var4 (|node::value| (getnode (read var6 var5))))))) (= var2 var5)) (= var1 var4))))) (inv_main595_9 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main_5 var6 var5 var4) (and (and (= var3 nullAddr) (and (is-O_node (read var6 var4)) (is-O_node (read var6 var4)))) (and (and (= var2 (write var6 var4 (O_node (node (|node::left| (getnode (read var6 var4))) var5 (|node::parent| (getnode (read var6 var4))) (|node::value| (getnode (read var6 var4))))))) (= var3 var5)) (= var1 var4))))) (inv_main595_9 var2 var3 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (and (inv_main_26 var2 var1 var0) (and (is-O_node (read var2 var0)) (not (= (|node::left| (getnode (read var2 var0))) nullAddr))))) (inv_main577_13 var2 var1 var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main_16 var3 var2 var1) (and (and (and (is-O_node (read var3 var1)) (is-O_node (read var3 (|node::left| (getnode (read var3 var1)))))) (is-O_node (read var3 (|node::left| (getnode (read var3 var1)))))) (= var0 (write var3 (|node::left| (getnode (read var3 var1))) (O_node (node (|node::left| (getnode (read var3 (|node::left| (getnode (read var3 var1)))))) (|node::right| (getnode (read var3 (|node::left| (getnode (read var3 var1)))))) (|node::parent| (getnode (read var3 (|node::left| (getnode (read var3 var1)))))) 42))))))) (inv_main_17 var0 var2 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main595_9 var7 var6 var5 var4) (and (and (is-O_node (read var7 var5)) (is-O_node (read var7 var5))) (and (and (and (= var3 (write var7 var5 (O_node (node (|node::left| (getnode (read var7 var5))) (|node::right| (getnode (read var7 var5))) (|node::parent| (getnode (read var7 var5))) var4)))) (= var2 var6)) (= var1 var5)) (= var0 var4))))) (inv_main586_5 var3 var1 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Heap)) (or (not (and (inv_main630_5 var3) (and (and (= var2 var3) (= var1 nullAddr)) (= var0 nullAddr)))) (inv_main586_5 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (and (inv_main_27 var2 var1 var0) (and (is-O_node (read var2 var0)) (not (= (|node::value| (getnode (read var2 var0))) 0))))) (inv_main_33 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main621_13 var7 var6 var5 var4) (and (is-O_node (read var7 var5)) (and (and (and (= var3 (write var7 (|node::right| (getnode (read var7 var5))) defObj)) (= var2 var6)) (= var1 var5)) (= var0 var4))))) (inv_main_50 var3 var2 var1 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main_46 var3 var2 var1 var0) (and (is-O_node (read var3 var1)) (= (|node::right| (getnode (read var3 var1))) nullAddr)))) (inv_main_50 var3 var2 var1 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main_46 var3 var2 var1 var0) (and (is-O_node (read var3 var1)) (not (= (|node::right| (getnode (read var3 var1))) nullAddr))))) (inv_main621_13 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main_50 var8 var7 var6 var5) (and (not (= var4 nullAddr)) (and (is-O_node (read var8 var6)) (and (and (and (and (= var3 var8) (= var2 var7)) (= var1 var6)) (= var0 var5)) (= var4 (|node::parent| (getnode (read var8 var6))))))))) (inv_main_45 var3 var2 var4 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main612_5_40 var8 var7 var6 var5) (and (not (= var4 nullAddr)) (and (and (= var3 nullAddr) (is-O_node (read var8 var6))) (and (and (and (and (= var2 var8) (= var1 var7)) (= var4 var6)) (= var0 var5)) (= var3 (|node::right| (getnode (read var8 var6))))))))) (inv_main_45 var2 var1 var4 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main_45 var3 var2 var1 var0) (and (is-O_node (read var3 var1)) (not (= (|node::left| (getnode (read var3 var1))) nullAddr))))) (inv_main619_13 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 node) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main586_5 var8 var7 var6) (and (not (= var5 nullAddr)) (and (and (and (and (= var4 (newHeap (alloc var8 (O_node var3)))) (= var2 var7)) (= var1 var6)) (= var5 (newAddr (alloc var8 (O_node var3))))) (not (= var0 0)))))) (inv_main_3 var4 var2 var5))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main600_9 var6 var5 var4 var3) (and (and (not (= var2 nullAddr)) (and (is-O_node (read var6 var4)) (is-O_node (read var6 var4)))) (and (and (= var1 (write var6 var4 (O_node (node var3 (|node::right| (getnode (read var6 var4))) (|node::parent| (getnode (read var6 var4))) (|node::value| (getnode (read var6 var4))))))) (= var0 var5)) (= var2 var4))))) (inv_main_13 var1 var0 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (and (inv_main_26 var2 var1 var0) (and (is-O_node (read var2 var0)) (= (|node::left| (getnode (read var2 var0))) nullAddr)))) (inv_main_27 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Int) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main577_13 var6 var5 var4) (and (and (= var3 42) (and (is-O_node (read var6 var4)) (is-O_node (read var6 (|node::left| (getnode (read var6 var4))))))) (and (and (and (= var2 var6) (= var1 var5)) (= var0 var4)) (= var3 (|node::value| (getnode (read var6 (|node::left| (getnode (read var6 var4))))))))))) (inv_main_27 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_3 var2 var1 var0) (not (is-O_node (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_3 var2 var1 var0) (and (is-O_node (read var2 var0)) (not (is-O_node (read var2 var0))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_5 var2 var1 var0) (not (is-O_node (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_5 var2 var1 var0) (and (is-O_node (read var2 var0)) (not (is-O_node (read var2 var0))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main593_13 var2 var1 var0) (not (is-O_node (read var2 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main593_13 var2 var1 var0) (and (is-O_node (read var2 var1)) (not (is-O_node (read var2 var1))))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main595_9 var3 var2 var1 var0) (not (is-O_node (read var3 var1)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main595_9 var3 var2 var1 var0) (and (is-O_node (read var3 var1)) (not (is-O_node (read var3 var1))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main600_9 var3 var2 var1 var0) (not (is-O_node (read var3 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main600_9 var3 var2 var1 var0) (and (is-O_node (read var3 var1)) (not (is-O_node (read var3 var1))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_13 var2 var1 var0) (not (is-O_node (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_13 var2 var1 var0) (and (is-O_node (read var2 var0)) (not (is-O_node (read var2 (|node::left| (getnode (read var2 var0)))))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_13 var2 var1 var0) (and (and (is-O_node (read var2 var0)) (is-O_node (read var2 (|node::left| (getnode (read var2 var0)))))) (not (is-O_node (read var2 (|node::left| (getnode (read var2 var0)))))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_15 var2 var1 var0) (not (is-O_node (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_15 var2 var1 var0) (and (is-O_node (read var2 var0)) (not (is-O_node (read var2 (|node::left| (getnode (read var2 var0)))))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_15 var2 var1 var0) (and (and (is-O_node (read var2 var0)) (is-O_node (read var2 (|node::left| (getnode (read var2 var0)))))) (not (is-O_node (read var2 (|node::left| (getnode (read var2 var0)))))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_16 var2 var1 var0) (not (is-O_node (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_16 var2 var1 var0) (and (is-O_node (read var2 var0)) (not (is-O_node (read var2 (|node::left| (getnode (read var2 var0)))))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_16 var2 var1 var0) (and (and (is-O_node (read var2 var0)) (is-O_node (read var2 (|node::left| (getnode (read var2 var0)))))) (not (is-O_node (read var2 (|node::left| (getnode (read var2 var0)))))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_17 var2 var1 var0) (not (is-O_node (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_17 var2 var1 var0) (and (is-O_node (read var2 var0)) (not (is-O_node (read var2 (|node::left| (getnode (read var2 var0)))))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_17 var2 var1 var0) (and (and (is-O_node (read var2 var0)) (is-O_node (read var2 (|node::left| (getnode (read var2 var0)))))) (not (is-O_node (read var2 (|node::left| (getnode (read var2 var0)))))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_18 var2 var1 var0) (not (is-O_node (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_26 var2 var1 var0) (not (is-O_node (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main577_13 var2 var1 var0) (not (is-O_node (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main577_13 var2 var1 var0) (and (is-O_node (read var2 var0)) (not (is-O_node (read var2 (|node::left| (getnode (read var2 var0)))))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_27 var2 var1 var0) (not (is-O_node (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_33 var2 var1 var0) (not (is-O_node (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main612_5_40 var3 var2 var1 var0) (not (is-O_node (read var3 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_41 var3 var2 var1 var0) (not (is-O_node (read var3 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_45 var3 var2 var1 var0) (not (is-O_node (read var3 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main619_13 var3 var2 var1 var0) (not (is-O_node (read var3 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_46 var3 var2 var1 var0) (not (is-O_node (read var3 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main621_13 var3 var2 var1 var0) (not (is-O_node (read var3 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_50 var3 var2 var1 var0) (not (is-O_node (read var3 var1)))))))
(check-sat)
