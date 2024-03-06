(set-logic HORN)
(set-info :source |
    Benchmark: C_VC
    Output by Princess (http://www.philipp.ruemmer.org/princess.shtml)
|)
(set-info :status unsat)
(declare-datatype bool ((true) (false)))
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
(declare-fun inv_exit (Heap Addr) Bool)
(declare-fun inv_main586_5 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main614_5 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main632_5 (Heap Addr) Bool)
(declare-fun inv_main637_12 (Heap Addr Int) Bool)
(declare-fun inv_main_10 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main_25 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main_41 (Heap Addr Addr Addr Addr) Bool)
(assert (forall ((var0 Addr) (var1 Heap)) (or (not (and (= var1 emptyHeap) (= var0 nullAddr))) (inv_main632_5 var1 var0))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main586_5 var5 var4 var3 var2) (and (and (not (= var2 nullAddr)) (= var1 0)) (= var0 (write var5 var2 (O_node (node (|node::left| (getnode (read var5 var2))) (|node::right| (getnode (read var5 var2))) nullAddr (|node::value| (getnode (read var5 var2)))))))))) (inv_main_10 var0 var4 var3 var2))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main586_5 var4 var3 var2 var1) (and (= var1 nullAddr) (= var0 0)))) (inv_main_10 var4 var3 var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Heap) (var12 Addr) (var13 Addr) (var14 Heap) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Bool) (var19 Addr) (var20 node) (var21 Heap) (var22 Addr) (var23 Addr) (var24 Addr) (var25 Addr) (var26 Addr) (var27 Addr) (var28 Addr) (var29 Addr) (var30 Heap) (var31 Heap) (var32 Addr) (var33 Addr) (var34 Addr) (var35 Heap)) (or (not (and (inv_main_10 var35 var34 var33 var32) (and (and (and (and (and (and (= var31 var30) (= var29 var28)) (= var27 var26)) (= var25 var24)) (= var23 (|node::right| (getnode (read var30 var24))))) (and (and (and (and (and (not (= var22 nullAddr)) (and (and (and (and (and (= var21 (newHeap (alloc var35 (O_node var20)))) (or (and var18 (= var19 (newAddr (alloc var35 (O_node var20))))) (and (not var18) (= var19 var34)))) (= var17 var33)) (= var16 var32)) (= var15 (newAddr (alloc var35 (O_node var20))))) (not (= var32 nullAddr)))) (and (and (and (= var14 (write var21 var16 (O_node (node var15 (|node::right| (getnode (read var21 var16))) (|node::parent| (getnode (read var21 var16))) (|node::value| (getnode (read var21 var16))))))) (= var13 var19)) (= var12 var17)) (= var22 var16))) (and (and (and (= var11 (write var14 (|node::left| (getnode (read var14 var22))) (O_node (node nullAddr (|node::right| (getnode (read var14 (|node::left| (getnode (read var14 var22)))))) (|node::parent| (getnode (read var14 (|node::left| (getnode (read var14 var22)))))) (|node::value| (getnode (read var14 (|node::left| (getnode (read var14 var22)))))))))) (= var10 var13)) (= var9 var12)) (= var8 var22))) (and (and (and (= var7 (write var11 (|node::left| (getnode (read var11 var8))) (O_node (node (|node::left| (getnode (read var11 (|node::left| (getnode (read var11 var8)))))) nullAddr (|node::parent| (getnode (read var11 (|node::left| (getnode (read var11 var8)))))) (|node::value| (getnode (read var11 (|node::left| (getnode (read var11 var8)))))))))) (= var6 var10)) (= var5 var9)) (= var4 var8))) (and (and (and (= var3 (write var7 (|node::left| (getnode (read var7 var4))) (O_node (node (|node::left| (getnode (read var7 (|node::left| (getnode (read var7 var4)))))) (|node::right| (getnode (read var7 (|node::left| (getnode (read var7 var4)))))) (|node::parent| (getnode (read var7 (|node::left| (getnode (read var7 var4)))))) 42)))) (= var2 var6)) (= var1 var5)) (= var0 var4)))) (and (and (and (= var30 (write var3 (|node::left| (getnode (read var3 var0))) (O_node (node (|node::left| (getnode (read var3 (|node::left| (getnode (read var3 var0)))))) (|node::right| (getnode (read var3 (|node::left| (getnode (read var3 var0)))))) var0 (|node::value| (getnode (read var3 (|node::left| (getnode (read var3 var0)))))))))) (= var28 var2)) (= var26 var1)) (= var24 var0))))) (inv_main_10 var31 var29 var27 var23))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main_25 var8 var7 var6 var5) (and (and (and (and (and (= var4 var8) (= var3 var7)) (= var2 var6)) (= var1 var5)) (= var0 (|node::parent| (getnode (read var8 var5))))) (and (not (= (|node::value| (getnode (read var8 var5))) 0)) (and (= (|node::left| (getnode (read var8 var5))) nullAddr) (not (= var5 nullAddr))))))) (inv_main_25 var4 var3 var2 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Heap)) (or (not (and (inv_main_25 var13 var12 var11 var10) (and (and (and (and (and (= var9 var8) (= var7 var6)) (= var5 var4)) (= var3 var2)) (= var1 (|node::parent| (getnode (read var8 var2))))) (and (not (= (|node::value| (getnode (read var8 var2))) 0)) (and (and (= var0 42) (and (and (and (and (= var8 var13) (= var6 var12)) (= var4 var11)) (= var2 var10)) (= var0 (|node::value| (getnode (read var13 (|node::left| (getnode (read var13 var10))))))))) (and (not (= (|node::left| (getnode (read var13 var10))) nullAddr)) (not (= var10 nullAddr)))))))) (inv_main_25 var9 var7 var5 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main_10 var3 var2 var1 var0) (and (not (= var1 nullAddr)) (and (not (= var1 nullAddr)) (= var0 nullAddr))))) (inv_main_25 var3 var2 var1 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main_10 var4 var3 var2 var1) (and (and (= var2 nullAddr) (= var1 nullAddr)) (= var0 0)))) (inv_main637_12 var4 var3 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main_41 var9 var8 var7 var6 var5) (and (and (= var6 nullAddr) (and (and (and (= var4 (write var9 var5 defObj)) (or (and (= var8 var5) (= var3 nullAddr)) (and (not (= var8 var5)) (= var3 var8)))) (= var2 var7)) (= var1 var6))) (= var0 0)))) (inv_main637_12 var4 var3 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main614_5 var10 var9 var8 var7 var6) (and (= var5 nullAddr) (and (and (and (and (and (= var4 var10) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var0 var6)) (= var5 (|node::right| (getnode (read var10 var7)))))))) (inv_main_41 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Heap) (var15 Heap) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Heap)) (or (not (and (inv_main_41 var20 var19 var18 var17 var16) (and (and (and (and (and (and (and (= var15 var14) (= var13 var12)) (= var11 var10)) (= var9 var8)) (= var7 var8)) (= var6 (|node::parent| (getnode (read var14 var8))))) (and (and (not (= (|node::right| (getnode (read var5 var4))) nullAddr)) (and (not (= (|node::left| (getnode (read var20 var17))) nullAddr)) (not (= var17 nullAddr)))) (and (and (and (and (= var5 (write var20 (|node::left| (getnode (read var20 var17))) defObj)) (or (and (= var19 (|node::left| (getnode (read var20 var17)))) (= var3 nullAddr)) (and (not (= var19 (|node::left| (getnode (read var20 var17))))) (= var3 var19)))) (= var2 var18)) (= var4 var17)) (= var1 var16)))) (and (and (and (and (= var14 (write var5 (|node::right| (getnode (read var5 var4))) defObj)) (or (and (= var3 (|node::right| (getnode (read var5 var4)))) (= var12 nullAddr)) (and (not (= var3 (|node::right| (getnode (read var5 var4))))) (= var12 var3)))) (= var10 var2)) (= var8 var4)) (= var0 var1))))) (inv_main_41 var15 var13 var11 var6 var7))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap) (var10 Heap) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Heap)) (or (not (and (inv_main_41 var15 var14 var13 var12 var11) (and (and (and (and (and (and (= var10 var9) (= var8 var7)) (= var6 var5)) (= var4 var3)) (= var2 var3)) (= var1 (|node::parent| (getnode (read var9 var3))))) (and (and (= (|node::right| (getnode (read var9 var3))) nullAddr) (and (not (= (|node::left| (getnode (read var15 var12))) nullAddr)) (not (= var12 nullAddr)))) (and (and (and (and (= var9 (write var15 (|node::left| (getnode (read var15 var12))) defObj)) (or (and (= var14 (|node::left| (getnode (read var15 var12)))) (= var7 nullAddr)) (and (not (= var14 (|node::left| (getnode (read var15 var12))))) (= var7 var14)))) (= var5 var13)) (= var3 var12)) (= var0 var11)))))) (inv_main_41 var10 var8 var6 var1 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap) (var10 Heap) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Heap)) (or (not (and (inv_main_41 var15 var14 var13 var12 var11) (and (and (and (and (and (and (and (= var10 var9) (= var8 var7)) (= var6 var5)) (= var4 var3)) (= var2 var3)) (= var1 (|node::parent| (getnode (read var9 var3))))) (and (not (= (|node::right| (getnode (read var15 var12))) nullAddr)) (and (= (|node::left| (getnode (read var15 var12))) nullAddr) (not (= var12 nullAddr))))) (and (and (and (and (= var9 (write var15 (|node::right| (getnode (read var15 var12))) defObj)) (or (and (= var14 (|node::right| (getnode (read var15 var12)))) (= var7 nullAddr)) (and (not (= var14 (|node::right| (getnode (read var15 var12))))) (= var7 var14)))) (= var5 var13)) (= var3 var12)) (= var0 var11))))) (inv_main_41 var10 var8 var6 var1 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main_41 var10 var9 var8 var7 var6) (and (and (and (and (and (and (= var5 var10) (= var4 var9)) (= var3 var8)) (= var2 var7)) (= var1 var7)) (= var0 (|node::parent| (getnode (read var10 var7))))) (and (= (|node::right| (getnode (read var10 var7))) nullAddr) (and (= (|node::left| (getnode (read var10 var7))) nullAddr) (not (= var7 nullAddr))))))) (inv_main_41 var5 var4 var3 var0 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Int) (var8 Addr) (var9 Addr) (var10 Bool) (var11 Addr) (var12 node) (var13 Heap) (var14 Addr) (var15 Addr) (var16 Int) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Int) (var23 Addr) (var24 Heap) (var25 Heap) (var26 Addr) (var27 Addr) (var28 Addr) (var29 Heap)) (or (not (and (inv_main586_5 var29 var28 var27 var26) (and (and (and (and (and (and (= var25 (write var24 var23 (O_node (node (|node::left| (getnode (read var24 var23))) (|node::right| (getnode (read var24 var23))) (|node::parent| (getnode (read var24 var23))) var22)))) (= var21 var20)) (= var19 var18)) (= var17 var23)) (= var16 var22)) (and (and (not (= var15 nullAddr)) (and (and (not (= var14 nullAddr)) (and (and (and (and (and (= var13 (newHeap (alloc var29 (O_node var12)))) (or (and var10 (= var11 (newAddr (alloc var29 (O_node var12))))) (and (not var10) (= var11 var28)))) (= var9 var27)) (= var8 var26)) (= var14 (newAddr (alloc var29 (O_node var12))))) (not (= var7 0)))) (and (and (and (= var6 (write var13 var14 (O_node (node nullAddr (|node::right| (getnode (read var13 var14))) (|node::parent| (getnode (read var13 var14))) (|node::value| (getnode (read var13 var14))))))) (= var5 var11)) (= var4 var9)) (= var3 var14)))) (and (and (and (= var2 (write var6 var3 (O_node (node (|node::left| (getnode (read var6 var3))) var4 (|node::parent| (getnode (read var6 var3))) (|node::value| (getnode (read var6 var3))))))) (= var1 var5)) (= var15 var4)) (= var0 var3)))) (and (and (and (= var24 (write var2 var15 (O_node (node (|node::left| (getnode (read var2 var15))) (|node::right| (getnode (read var2 var15))) var0 (|node::value| (getnode (read var2 var15))))))) (= var20 var1)) (= var18 var15)) (= var23 var0))))) (inv_main586_5 var25 var21 var17 var17))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr) (var7 Bool) (var8 Addr) (var9 node) (var10 Heap) (var11 Addr) (var12 Int) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Int) (var19 Addr) (var20 Heap) (var21 Heap) (var22 Addr) (var23 Addr) (var24 Addr) (var25 Heap)) (or (not (and (inv_main586_5 var25 var24 var23 var22) (and (and (and (and (and (= var21 (write var20 var19 (O_node (node (|node::left| (getnode (read var20 var19))) (|node::right| (getnode (read var20 var19))) (|node::parent| (getnode (read var20 var19))) var18)))) (= var17 var16)) (= var15 var14)) (= var13 var19)) (= var12 var18)) (and (and (= var14 nullAddr) (and (and (not (= var11 nullAddr)) (and (and (and (and (and (= var10 (newHeap (alloc var25 (O_node var9)))) (or (and var7 (= var8 (newAddr (alloc var25 (O_node var9))))) (and (not var7) (= var8 var24)))) (= var6 var23)) (= var5 var22)) (= var11 (newAddr (alloc var25 (O_node var9))))) (not (= var4 0)))) (and (and (and (= var3 (write var10 var11 (O_node (node nullAddr (|node::right| (getnode (read var10 var11))) (|node::parent| (getnode (read var10 var11))) (|node::value| (getnode (read var10 var11))))))) (= var2 var8)) (= var1 var6)) (= var0 var11)))) (and (and (and (= var20 (write var3 var0 (O_node (node (|node::left| (getnode (read var3 var0))) var1 (|node::parent| (getnode (read var3 var0))) (|node::value| (getnode (read var3 var0))))))) (= var16 var2)) (= var14 var1)) (= var19 var0)))))) (inv_main586_5 var21 var17 var13 var13))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Heap)) (or (not (and (inv_main632_5 var5 var4) (and (and (and (= var3 var5) (= var2 var4)) (= var1 nullAddr)) (= var0 nullAddr)))) (inv_main586_5 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap) (var11 Heap) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Heap)) (or (not (and (inv_main614_5 var16 var15 var14 var13 var12) (and (and (and (and (and (and (= var11 var10) (= var9 var8)) (= var7 var6)) (= var5 var4)) (= var3 var2)) (= var1 (|node::right| (getnode (read var10 var4))))) (and (not (= var0 nullAddr)) (and (and (and (and (and (= var10 var16) (= var8 var15)) (= var6 var14)) (= var4 var13)) (= var2 var12)) (= var0 (|node::right| (getnode (read var16 var13))))))))) (inv_main614_5 var11 var9 var7 var1 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main_25 var4 var3 var2 var1) (and (= var1 nullAddr) (= var0 nullAddr)))) (inv_main614_5 var4 var3 var2 var2 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Bool) (var4 Addr) (var5 node) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Heap)) (or (not (and (inv_main586_5 var11 var10 var9 var8) (and (= var7 nullAddr) (and (and (and (and (and (= var6 (newHeap (alloc var11 (O_node var5)))) (or (and var3 (= var4 (newAddr (alloc var11 (O_node var5))))) (and (not var3) (= var4 var10)))) (= var2 var9)) (= var1 var8)) (= var7 (newAddr (alloc var11 (O_node var5))))) (not (= var0 0)))))) (inv_exit var6 var4))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Bool) (var7 Addr) (var8 node) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Heap)) (or (not (and (inv_main_10 var14 var13 var12 var11) (and (and (= var10 nullAddr) (and (and (and (and (and (= var9 (newHeap (alloc var14 (O_node var8)))) (or (and var6 (= var7 (newAddr (alloc var14 (O_node var8))))) (and (not var6) (= var7 var13)))) (= var5 var12)) (= var4 var11)) (= var3 (newAddr (alloc var14 (O_node var8))))) (not (= var11 nullAddr)))) (and (and (and (= var2 (write var9 var4 (O_node (node var3 (|node::right| (getnode (read var9 var4))) (|node::parent| (getnode (read var9 var4))) (|node::value| (getnode (read var9 var4))))))) (= var1 var7)) (= var0 var5)) (= var10 var4))))) (inv_exit var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main_25 var8 var7 var6 var5) (and (and (not (= var4 42)) (and (and (and (and (= var3 var8) (= var2 var7)) (= var1 var6)) (= var0 var5)) (= var4 (|node::value| (getnode (read var8 (|node::left| (getnode (read var8 var5))))))))) (and (not (= (|node::left| (getnode (read var8 var5))) nullAddr)) (not (= var5 nullAddr)))))) (inv_exit var3 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main_25 var3 var2 var1 var0) (and (= (|node::value| (getnode (read var3 var0))) 0) (and (= (|node::left| (getnode (read var3 var0))) nullAddr) (not (= var0 nullAddr)))))) (inv_exit var3 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main_25 var8 var7 var6 var5) (and (= (|node::value| (getnode (read var4 var3))) 0) (and (and (= var2 42) (and (and (and (and (= var4 var8) (= var1 var7)) (= var0 var6)) (= var3 var5)) (= var2 (|node::value| (getnode (read var8 (|node::left| (getnode (read var8 var5))))))))) (and (not (= (|node::left| (getnode (read var8 var5))) nullAddr)) (not (= var5 nullAddr))))))) (inv_exit var4 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main_10 var3 var2 var1 var0) (and (= var1 nullAddr) (and (not (= var1 nullAddr)) (= var0 nullAddr))))) (inv_exit var3 var2))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_exit var1 var0) (not (= var0 nullAddr))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap)) (not (and (inv_main637_12 var2 var1 var0) (not (= var1 nullAddr))))))
(check-sat)
