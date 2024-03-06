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

(declare-datatypes ((HeapObject 0) (node 0))
                   (((O_Int (getInt Int)) (O_UInt (getUInt Int)) (O_Addr (getAddr Addr)) (O_AddrRange (getAddrRange AddrRange)) (O_node (getnode node)) (defObj))
                   ((node (|node::next| Addr) (|node::prev| Addr)))))
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
(declare-fun inv_main588_5 (Heap Addr Addr Int Int Addr) Bool)
(declare-fun inv_main603_10 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main627_22 (Heap Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main627_22_164 (Heap Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main627_22_79 (Heap Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main628_22 (Heap Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main628_22_172 (Heap Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main628_22_87 (Heap Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main629_10 (Heap Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main629_10_176 (Heap Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main629_10_91 (Heap Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main630_26 (Heap Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main630_26_183 (Heap Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main630_26_98 (Heap Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main633_22 (Heap Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main633_22_133 (Heap Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main633_22_199 (Heap Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main634_22 (Heap Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main634_22_141 (Heap Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main634_22_207 (Heap Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main635_10 (Heap Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main635_10_145 (Heap Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main635_10_211 (Heap Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main636_26 (Heap Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main636_26_152 (Heap Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main636_26_218 (Heap Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main641_5 (Heap Addr Addr) Bool)
(declare-fun inv_main644_28 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main645_28 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main650_5 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main654_5 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main_192 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main_22 (Heap Addr Addr Int Int Addr) Bool)
(declare-fun inv_main_7 (Heap Addr Addr Int Int Addr) Bool)
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (= var2 emptyHeap)) (inv_main641_5 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Heap)) (or (not (and (inv_main635_10_211 var12 var11 var10 var9 var8 var7) (and (and (and (and (and (and (and (= var6 var12) (= var5 var11)) (= var4 var10)) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var0 (|node::prev| (getnode (read var12 var8))))) (and (not (= var8 nullAddr)) (not (= var7 var8)))))) (inv_main635_10_211 var6 var5 var4 var3 var0 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Heap)) (or (not (and (inv_main654_5 var11 var10 var9 var8 var7) (and (and (and (and (and (and (and (and (= var6 var11) (= var5 var10)) (= var4 var9)) (= var3 var8)) (= var2 var10)) (= var1 var9)) (= var0 (|node::prev| (getnode (read var11 var10))))) (and (not (= var9 nullAddr)) (not (= var10 nullAddr)))) (= var7 nullAddr)))) (inv_main635_10_211 var6 var5 var4 var3 var0 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main629_10_91 var5 var4 var3 var2 var1 var0) (and (= var1 nullAddr) (not (= var0 var1))))) (inv_main630_26_98 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main635_10_145 var5 var4 var3 var2 var1 var0) (and (= var1 nullAddr) (not (= var0 var1))))) (inv_main636_26_152 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Heap) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Heap) (var24 Heap) (var25 Addr) (var26 Addr) (var27 Addr) (var28 Addr) (var29 Heap)) (or (not (and (inv_main650_5 var29 var28 var27 var26 var25) (and (and (and (and (and (and (and (and (and (and (= var24 var23) (= var22 var21)) (= var20 var19)) (= var18 var17)) (= var16 var15)) (= var14 var13)) (= var12 (|node::prev| (getnode (read var23 var15))))) (and (and (and (and (and (= var23 var29) (= var21 var28)) (= var19 var27)) (= var17 var26)) (= var15 var25)) (= var13 (|node::next| (getnode (read var29 var25)))))) (and (and (and (and (and (= var11 (write var24 var16 (O_node (node var12 (|node::prev| (getnode (read var24 var16))))))) (= var10 var22)) (= var9 var20)) (= var8 var18)) (= var7 var16)) (= var6 var14))) (and (and (and (and (and (= var5 (write var11 var7 (O_node (node (|node::next| (getnode (read var11 var7))) var6)))) (= var4 var10)) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var0 var6))) (not (= var25 nullAddr))))) (inv_main650_5 var5 var4 var3 var2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main635_10 var5 var4 var3 var2 var1 var0) (= var0 var1))) (inv_main650_5 var5 var4 var3 var2 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main603_10 var10 var9 var8 var7 var6) (and (= var5 nullAddr) (and (= var4 nullAddr) (and (and (and (and (and (= var3 var10) (= var5 var9)) (= var2 var8)) (= var1 var7)) (= var0 var6)) (= var4 (|node::next| (getnode (read var10 var6))))))))) (inv_main627_22_79 var3 var5 var2 var1 var5 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main629_10 var5 var4 var3 var2 var1 var0) (and (not (= (|node::prev| (getnode (read var5 var3))) nullAddr)) (and (= (|node::prev| (getnode (read var5 var4))) nullAddr) (= var0 var1))))) (inv_main645_28 var5 var4 var3 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main654_5 var4 var3 var2 var1 var0) (and (and (= var2 nullAddr) (not (= var3 nullAddr))) (= var0 nullAddr)))) (inv_main634_22_207 var4 var3 var2 var1 var3 var2))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Int) (var4 Int) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Int) (var9 Addr) (var10 Int) (var11 Int) (var12 Addr) (var13 Addr) (var14 Heap) (var15 Addr) (var16 Int) (var17 Addr) (var18 Int) (var19 Int) (var20 Addr) (var21 Addr) (var22 Heap) (var23 Int) (var24 Addr) (var25 Int) (var26 Int) (var27 Addr) (var28 Addr) (var29 node) (var30 Heap) (var31 Addr) (var32 Int) (var33 Addr) (var34 Addr) (var35 Int) (var36 Int) (var37 Addr) (var38 Addr) (var39 Heap)) (or (not (and (inv_main_22 var39 var38 var37 var36 var35 var34) (and (= var33 nullAddr) (and (= var32 0) (and (and (and (and (not (= var31 nullAddr)) (and (and (and (and (and (and (and (= var30 (newHeap (alloc var39 (O_node var29)))) (= var28 var38)) (= var27 var37)) (= var26 var36)) (= var25 var35)) (= var24 var34)) (= var23 5)) (= var31 (newAddr (alloc var39 (O_node var29)))))) (and (and (and (and (and (and (and (= var22 (write var30 var31 (O_node (node nullAddr (|node::prev| (getnode (read var30 var31))))))) (= var21 var28)) (= var20 var27)) (= var19 var26)) (= var18 var25)) (= var17 var24)) (= var16 var23)) (= var15 var31))) (and (and (and (and (and (and (and (= var14 (write var22 var15 (O_node (node (|node::next| (getnode (read var22 var15))) nullAddr)))) (= var13 var21)) (= var12 var20)) (= var11 var19)) (= var10 var18)) (= var9 var17)) (= var8 var16)) (= var7 var15))) (and (and (and (and (and (and (and (= var6 (write var14 var7 (O_node (node var9 (|node::prev| (getnode (read var14 var7))))))) (= var33 var13)) (= var5 var12)) (= var4 var11)) (= var3 var10)) (= var2 var9)) (= var1 var8)) (= var0 var7))))))) (inv_main627_22 var6 var33 var5 var0 var33 var5))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main650_5 var4 var3 var2 var1 var0) (and (and (= var2 nullAddr) (not (= var3 nullAddr))) (= var0 nullAddr)))) (inv_main634_22_141 var4 var3 var2 var1 var3 var2))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Int) (var4 Int) (var5 Heap) (var6 Addr) (var7 Int) (var8 Addr) (var9 Int) (var10 Int) (var11 Addr) (var12 Addr) (var13 Heap) (var14 Addr) (var15 Int) (var16 Addr) (var17 Int) (var18 Int) (var19 Addr) (var20 Addr) (var21 Heap) (var22 Int) (var23 Addr) (var24 Int) (var25 Int) (var26 Addr) (var27 Addr) (var28 node) (var29 Heap) (var30 Addr) (var31 Int) (var32 Addr) (var33 Addr) (var34 Addr) (var35 Int) (var36 Int) (var37 Addr) (var38 Addr) (var39 Heap)) (or (not (and (inv_main_22 var39 var38 var37 var36 var35 var34) (and (and (= var33 nullAddr) (not (= var32 nullAddr))) (and (= var31 0) (and (and (and (and (not (= var30 nullAddr)) (and (and (and (and (and (and (and (= var29 (newHeap (alloc var39 (O_node var28)))) (= var27 var38)) (= var26 var37)) (= var25 var36)) (= var24 var35)) (= var23 var34)) (= var22 5)) (= var30 (newAddr (alloc var39 (O_node var28)))))) (and (and (and (and (and (and (and (= var21 (write var29 var30 (O_node (node nullAddr (|node::prev| (getnode (read var29 var30))))))) (= var20 var27)) (= var19 var26)) (= var18 var25)) (= var17 var24)) (= var16 var23)) (= var15 var22)) (= var14 var30))) (and (and (and (and (and (and (and (= var13 (write var21 var14 (O_node (node (|node::next| (getnode (read var21 var14))) nullAddr)))) (= var12 var20)) (= var11 var19)) (= var10 var18)) (= var9 var17)) (= var8 var16)) (= var7 var15)) (= var6 var14))) (and (and (and (and (and (and (and (= var5 (write var13 var6 (O_node (node var8 (|node::prev| (getnode (read var13 var6))))))) (= var32 var12)) (= var33 var11)) (= var4 var10)) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var0 var6))))))) (inv_main628_22 var5 var32 var33 var0 var32 var33))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main635_10_211 var5 var4 var3 var2 var1 var0) (= var0 var1))) (inv_main_192 var5 var4 var3 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Heap)) (or (not (and (inv_main_192 var13 var12 var11 var10) (and (and (and (and (and (and (= var9 var13) (= var8 var12)) (= var7 var11)) (= var6 var10)) (= var5 (|node::prev| (getnode (read var13 var10))))) (and (and (and (and (= var4 (write var9 var6 defObj)) (= var3 var8)) (= var2 var7)) (= var1 var6)) (= var0 var5))) (not (= var10 nullAddr))))) (inv_main_192 var4 var3 var2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Heap)) (or (not (and (inv_main629_10_91 var12 var11 var10 var9 var8 var7) (and (and (and (and (and (and (and (= var6 var12) (= var5 var11)) (= var4 var10)) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var0 (|node::next| (getnode (read var12 var8))))) (and (not (= var8 nullAddr)) (not (= var7 var8)))))) (inv_main629_10_91 var6 var5 var4 var3 var0 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Heap) (var12 Heap) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Heap)) (or (not (and (inv_main603_10 var17 var16 var15 var14 var13) (and (and (and (and (and (and (and (and (= var12 var11) (= var10 var9)) (= var8 var7)) (= var6 var5)) (= var4 var9)) (= var3 var7)) (= var2 (|node::next| (getnode (read var11 var9))))) (and (not (= var7 nullAddr)) (not (= var9 nullAddr)))) (and (= var1 nullAddr) (and (and (and (and (and (= var11 var17) (= var9 var16)) (= var7 var15)) (= var5 var14)) (= var0 var13)) (= var1 (|node::next| (getnode (read var17 var13))))))))) (inv_main629_10_91 var12 var10 var8 var6 var2 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main650_5 var4 var3 var2 var1 var0) (and (= var3 nullAddr) (= var0 nullAddr)))) (inv_main633_22_133 var4 var3 var2 var1 var3 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main629_10_91 var5 var4 var3 var2 var1 var0) (and (and (= var4 nullAddr) (not (= var3 nullAddr))) (= var0 var1)))) (inv_main634_22 var5 var4 var3 var2 var3 var4))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Heap)) (or (not (and (inv_main635_10_145 var12 var11 var10 var9 var8 var7) (and (and (and (and (and (and (and (= var6 var12) (= var5 var11)) (= var4 var10)) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var0 (|node::prev| (getnode (read var12 var8))))) (and (not (= var8 nullAddr)) (not (= var7 var8)))))) (inv_main635_10_145 var6 var5 var4 var3 var0 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Heap)) (or (not (and (inv_main650_5 var11 var10 var9 var8 var7) (and (and (and (and (and (and (and (and (= var6 var11) (= var5 var10)) (= var4 var9)) (= var3 var8)) (= var2 var10)) (= var1 var9)) (= var0 (|node::prev| (getnode (read var11 var10))))) (and (not (= var9 nullAddr)) (not (= var10 nullAddr)))) (= var7 nullAddr)))) (inv_main635_10_145 var6 var5 var4 var3 var0 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main629_10 var5 var4 var3 var2 var1 var0) (and (not (= (|node::prev| (getnode (read var5 var4))) nullAddr)) (= var0 var1)))) (inv_main644_28 var5 var4 var3 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main635_10_145 var5 var4 var3 var2 var1 var0) (and (= var3 nullAddr) (= var0 var1)))) (inv_main627_22_164 var5 var4 var3 var2 var3 var4))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Int) (var4 Int) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Int) (var10 Addr) (var11 Int) (var12 Int) (var13 Addr) (var14 Addr) (var15 Heap) (var16 Addr) (var17 Int) (var18 Addr) (var19 Int) (var20 Int) (var21 Addr) (var22 Addr) (var23 Heap) (var24 Int) (var25 Addr) (var26 Int) (var27 Int) (var28 Addr) (var29 Addr) (var30 node) (var31 Heap) (var32 Addr) (var33 Int) (var34 Addr) (var35 Int) (var36 Int) (var37 Addr) (var38 Addr) (var39 Heap)) (or (not (and (inv_main_7 var39 var38 var37 var36 var35 var34) (and (= var33 0) (and (and (and (and (not (= var32 nullAddr)) (and (and (and (and (and (and (and (= var31 (newHeap (alloc var39 (O_node var30)))) (= var29 var38)) (= var28 var37)) (= var27 var36)) (= var26 var35)) (= var25 var34)) (= var24 5)) (= var32 (newAddr (alloc var39 (O_node var30)))))) (and (and (and (and (and (and (and (= var23 (write var31 var32 (O_node (node nullAddr (|node::prev| (getnode (read var31 var32))))))) (= var22 var29)) (= var21 var28)) (= var20 var27)) (= var19 var26)) (= var18 var25)) (= var17 var24)) (= var16 var32))) (and (and (and (and (and (and (and (= var15 (write var23 var16 (O_node (node (|node::next| (getnode (read var23 var16))) nullAddr)))) (= var14 var22)) (= var13 var21)) (= var12 var20)) (= var11 var19)) (= var10 var18)) (= var9 var17)) (= var8 var16))) (and (and (and (and (and (and (and (= var7 (write var15 var8 (O_node (node var10 (|node::prev| (getnode (read var15 var8))))))) (= var6 var14)) (= var5 var13)) (= var4 var12)) (= var3 var11)) (= var2 var10)) (= var1 var9)) (= var0 var8)))))) (inv_main_22 var7 var0 var5 var4 var3 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Int) (var4 Int) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Int) (var10 Addr) (var11 Int) (var12 Int) (var13 Addr) (var14 Addr) (var15 Heap) (var16 Addr) (var17 Int) (var18 Addr) (var19 Int) (var20 Int) (var21 Addr) (var22 Addr) (var23 Heap) (var24 Int) (var25 Addr) (var26 Int) (var27 Int) (var28 Addr) (var29 Addr) (var30 node) (var31 Heap) (var32 Addr) (var33 Int) (var34 Addr) (var35 Int) (var36 Int) (var37 Addr) (var38 Addr) (var39 Heap)) (or (not (and (inv_main_22 var39 var38 var37 var36 var35 var34) (and (not (= var33 0)) (and (and (and (and (not (= var32 nullAddr)) (and (and (and (and (and (and (and (= var31 (newHeap (alloc var39 (O_node var30)))) (= var29 var38)) (= var28 var37)) (= var27 var36)) (= var26 var35)) (= var25 var34)) (= var24 5)) (= var32 (newAddr (alloc var39 (O_node var30)))))) (and (and (and (and (and (and (and (= var23 (write var31 var32 (O_node (node nullAddr (|node::prev| (getnode (read var31 var32))))))) (= var22 var29)) (= var21 var28)) (= var20 var27)) (= var19 var26)) (= var18 var25)) (= var17 var24)) (= var16 var32))) (and (and (and (and (and (and (and (= var15 (write var23 var16 (O_node (node (|node::next| (getnode (read var23 var16))) nullAddr)))) (= var14 var22)) (= var13 var21)) (= var12 var20)) (= var11 var19)) (= var10 var18)) (= var9 var17)) (= var8 var16))) (and (and (and (and (and (and (and (= var7 (write var15 var8 (O_node (node var10 (|node::prev| (getnode (read var15 var8))))))) (= var6 var14)) (= var5 var13)) (= var4 var12)) (= var3 var11)) (= var2 var10)) (= var1 var9)) (= var0 var8)))))) (inv_main_22 var7 var6 var5 var4 var3 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Heap)) (or (not (and (inv_main629_10_176 var12 var11 var10 var9 var8 var7) (and (and (and (and (and (and (and (= var6 var12) (= var5 var11)) (= var4 var10)) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var0 (|node::next| (getnode (read var12 var8))))) (and (not (= var8 nullAddr)) (not (= var7 var8)))))) (inv_main629_10_176 var6 var5 var4 var3 var0 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Heap)) (or (not (and (inv_main635_10_145 var12 var11 var10 var9 var8 var7) (and (and (and (and (and (and (and (and (= var6 var12) (= var5 var11)) (= var4 var10)) (= var3 var9)) (= var2 var10)) (= var1 var11)) (= var0 (|node::next| (getnode (read var12 var10))))) (and (not (= var11 nullAddr)) (not (= var10 nullAddr)))) (= var7 var8)))) (inv_main629_10_176 var6 var5 var4 var3 var0 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main654_5 var4 var3 var2 var1 var0) (and (= var3 nullAddr) (= var0 nullAddr)))) (inv_main633_22_199 var4 var3 var2 var1 var3 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main635_10 var5 var4 var3 var2 var1 var0) (and (= var1 nullAddr) (not (= var0 var1))))) (inv_main636_26 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Int) (var4 Int) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Int) (var10 Addr) (var11 Int) (var12 Int) (var13 Addr) (var14 Addr) (var15 Heap) (var16 Addr) (var17 Int) (var18 Addr) (var19 Int) (var20 Int) (var21 Addr) (var22 Addr) (var23 Heap) (var24 Int) (var25 Addr) (var26 Int) (var27 Int) (var28 Addr) (var29 Addr) (var30 node) (var31 Heap) (var32 Addr) (var33 Int) (var34 Addr) (var35 Int) (var36 Int) (var37 Addr) (var38 Addr) (var39 Heap)) (or (not (and (inv_main588_5 var39 var38 var37 var36 var35 var34) (and (= var33 0) (and (and (and (and (not (= var32 nullAddr)) (and (and (and (and (and (and (and (= var31 (newHeap (alloc var39 (O_node var30)))) (= var29 var38)) (= var28 var37)) (= var27 var36)) (= var26 var35)) (= var25 var34)) (= var24 5)) (= var32 (newAddr (alloc var39 (O_node var30)))))) (and (and (and (and (and (and (and (= var23 (write var31 var32 (O_node (node nullAddr (|node::prev| (getnode (read var31 var32))))))) (= var22 var29)) (= var21 var28)) (= var20 var27)) (= var19 var26)) (= var18 var25)) (= var17 var24)) (= var16 var32))) (and (and (and (and (and (and (and (= var15 (write var23 var16 (O_node (node (|node::next| (getnode (read var23 var16))) nullAddr)))) (= var14 var22)) (= var13 var21)) (= var12 var20)) (= var11 var19)) (= var10 var18)) (= var9 var17)) (= var8 var16))) (and (and (and (and (and (and (and (= var7 (write var15 var8 (O_node (node var10 (|node::prev| (getnode (read var15 var8))))))) (= var6 var14)) (= var5 var13)) (= var4 var12)) (= var3 var11)) (= var2 var10)) (= var1 var9)) (= var0 var8)))))) (inv_main_7 var7 var6 var0 var4 var3 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Int) (var4 Int) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Int) (var10 Addr) (var11 Int) (var12 Int) (var13 Addr) (var14 Addr) (var15 Heap) (var16 Addr) (var17 Int) (var18 Addr) (var19 Int) (var20 Int) (var21 Addr) (var22 Addr) (var23 Heap) (var24 Int) (var25 Addr) (var26 Int) (var27 Int) (var28 Addr) (var29 Addr) (var30 node) (var31 Heap) (var32 Addr) (var33 Int) (var34 Addr) (var35 Int) (var36 Int) (var37 Addr) (var38 Addr) (var39 Heap)) (or (not (and (inv_main_7 var39 var38 var37 var36 var35 var34) (and (not (= var33 0)) (and (and (and (and (not (= var32 nullAddr)) (and (and (and (and (and (and (and (= var31 (newHeap (alloc var39 (O_node var30)))) (= var29 var38)) (= var28 var37)) (= var27 var36)) (= var26 var35)) (= var25 var34)) (= var24 5)) (= var32 (newAddr (alloc var39 (O_node var30)))))) (and (and (and (and (and (and (and (= var23 (write var31 var32 (O_node (node nullAddr (|node::prev| (getnode (read var31 var32))))))) (= var22 var29)) (= var21 var28)) (= var20 var27)) (= var19 var26)) (= var18 var25)) (= var17 var24)) (= var16 var32))) (and (and (and (and (and (and (and (= var15 (write var23 var16 (O_node (node (|node::next| (getnode (read var23 var16))) nullAddr)))) (= var14 var22)) (= var13 var21)) (= var12 var20)) (= var11 var19)) (= var10 var18)) (= var9 var17)) (= var8 var16))) (and (and (and (and (and (and (and (= var7 (write var15 var8 (O_node (node var10 (|node::prev| (getnode (read var15 var8))))))) (= var6 var14)) (= var5 var13)) (= var4 var12)) (= var3 var11)) (= var2 var10)) (= var1 var9)) (= var0 var8)))))) (inv_main_7 var7 var6 var5 var4 var3 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Heap)) (or (not (and (inv_main603_10 var16 var15 var14 var13 var12) (and (and (not (= var11 nullAddr)) (and (and (and (and (and (= var10 var16) (= var9 var15)) (= var8 var14)) (= var7 var13)) (= var6 var12)) (= var11 (|node::next| (getnode (read var16 var12)))))) (and (and (and (and (and (= var5 (write var10 var11 (O_node (node (|node::next| (getnode (read var10 var11))) var6)))) (= var4 var9)) (= var3 var8)) (= var2 var7)) (= var1 var6)) (= var0 var11))))) (inv_main603_10 var5 var4 var3 var2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main629_10 var5 var4 var3 var2 var1 var0) (and (= (|node::prev| (getnode (read var5 var3))) nullAddr) (and (= (|node::prev| (getnode (read var5 var4))) nullAddr) (= var0 var1))))) (inv_main603_10 var5 var4 var3 var2 var2))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Int) (var4 Int) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Int) (var10 Addr) (var11 Int) (var12 Int) (var13 Addr) (var14 Addr) (var15 Heap) (var16 Addr) (var17 Int) (var18 Addr) (var19 Int) (var20 Int) (var21 Addr) (var22 Addr) (var23 Heap) (var24 Int) (var25 Addr) (var26 Int) (var27 Int) (var28 Addr) (var29 Addr) (var30 node) (var31 Heap) (var32 Addr) (var33 Int) (var34 Addr) (var35 Int) (var36 Int) (var37 Addr) (var38 Addr) (var39 Heap)) (or (not (and (inv_main588_5 var39 var38 var37 var36 var35 var34) (and (not (= var33 0)) (and (and (and (and (not (= var32 nullAddr)) (and (and (and (and (and (and (and (= var31 (newHeap (alloc var39 (O_node var30)))) (= var29 var38)) (= var28 var37)) (= var27 var36)) (= var26 var35)) (= var25 var34)) (= var24 5)) (= var32 (newAddr (alloc var39 (O_node var30)))))) (and (and (and (and (and (and (and (= var23 (write var31 var32 (O_node (node nullAddr (|node::prev| (getnode (read var31 var32))))))) (= var22 var29)) (= var21 var28)) (= var20 var27)) (= var19 var26)) (= var18 var25)) (= var17 var24)) (= var16 var32))) (and (and (and (and (and (and (and (= var15 (write var23 var16 (O_node (node (|node::next| (getnode (read var23 var16))) nullAddr)))) (= var14 var22)) (= var13 var21)) (= var12 var20)) (= var11 var19)) (= var10 var18)) (= var9 var17)) (= var8 var16))) (and (and (and (and (and (and (and (= var7 (write var15 var8 (O_node (node var10 (|node::prev| (getnode (read var15 var8))))))) (= var6 var14)) (= var5 var13)) (= var4 var12)) (= var3 var11)) (= var2 var10)) (= var1 var9)) (= var0 var8)))))) (inv_main588_5 var7 var6 var5 var4 var3 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main641_5 var5 var4 var3) (and (and (= var2 1) (= var1 2)) (= var0 nullAddr)))) (inv_main588_5 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main603_10 var10 var9 var8 var7 var6) (and (and (= var5 nullAddr) (not (= var4 nullAddr))) (and (= var3 nullAddr) (and (and (and (and (and (= var2 var10) (= var4 var9)) (= var5 var8)) (= var1 var7)) (= var0 var6)) (= var3 (|node::next| (getnode (read var10 var6))))))))) (inv_main628_22_87 var2 var4 var5 var1 var4 var5))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main635_10_145 var5 var4 var3 var2 var1 var0) (and (and (= var4 nullAddr) (not (= var3 nullAddr))) (= var0 var1)))) (inv_main628_22_172 var5 var4 var3 var2 var3 var4))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main629_10_91 var5 var4 var3 var2 var1 var0) (and (= var3 nullAddr) (= var0 var1)))) (inv_main633_22 var5 var4 var3 var2 var3 var4))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Heap)) (or (not (and (inv_main629_10 var12 var11 var10 var9 var8 var7) (and (and (and (and (and (and (and (= var6 var12) (= var5 var11)) (= var4 var10)) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var0 (|node::next| (getnode (read var12 var8))))) (and (not (= var8 nullAddr)) (not (= var7 var8)))))) (inv_main629_10 var6 var5 var4 var3 var0 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Addr) (var5 Int) (var6 Addr) (var7 Int) (var8 Int) (var9 Addr) (var10 Addr) (var11 Heap) (var12 Addr) (var13 Int) (var14 Addr) (var15 Int) (var16 Int) (var17 Addr) (var18 Addr) (var19 Heap) (var20 Int) (var21 Addr) (var22 Int) (var23 Int) (var24 Addr) (var25 Addr) (var26 node) (var27 Heap) (var28 Addr) (var29 Int) (var30 Addr) (var31 Addr) (var32 Addr) (var33 Addr) (var34 Addr) (var35 Addr) (var36 Addr) (var37 Addr) (var38 Addr) (var39 Heap) (var40 Heap) (var41 Addr) (var42 Int) (var43 Int) (var44 Addr) (var45 Addr) (var46 Heap)) (or (not (and (inv_main_22 var46 var45 var44 var43 var42 var41) (and (and (and (and (and (and (and (and (= var40 var39) (= var38 var37)) (= var36 var35)) (= var34 var33)) (= var32 var37)) (= var31 var35)) (= var30 (|node::next| (getnode (read var39 var37))))) (and (not (= var35 nullAddr)) (not (= var37 nullAddr)))) (and (= var29 0) (and (and (and (and (not (= var28 nullAddr)) (and (and (and (and (and (and (and (= var27 (newHeap (alloc var46 (O_node var26)))) (= var25 var45)) (= var24 var44)) (= var23 var43)) (= var22 var42)) (= var21 var41)) (= var20 5)) (= var28 (newAddr (alloc var46 (O_node var26)))))) (and (and (and (and (and (and (and (= var19 (write var27 var28 (O_node (node nullAddr (|node::prev| (getnode (read var27 var28))))))) (= var18 var25)) (= var17 var24)) (= var16 var23)) (= var15 var22)) (= var14 var21)) (= var13 var20)) (= var12 var28))) (and (and (and (and (and (and (and (= var11 (write var19 var12 (O_node (node (|node::next| (getnode (read var19 var12))) nullAddr)))) (= var10 var18)) (= var9 var17)) (= var8 var16)) (= var7 var15)) (= var6 var14)) (= var5 var13)) (= var4 var12))) (and (and (and (and (and (and (and (= var39 (write var11 var4 (O_node (node var6 (|node::prev| (getnode (read var11 var4))))))) (= var37 var10)) (= var35 var9)) (= var3 var8)) (= var2 var7)) (= var1 var6)) (= var0 var5)) (= var33 var4))))))) (inv_main629_10 var40 var38 var36 var34 var30 var31))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main629_10 var5 var4 var3 var2 var1 var0) (and (= var1 nullAddr) (not (= var0 var1))))) (inv_main630_26 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main629_10_176 var5 var4 var3 var2 var1 var0) (and (= var1 nullAddr) (not (= var0 var1))))) (inv_main630_26_183 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Heap) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Heap)) (or (not (and (inv_main654_5 var16 var15 var14 var13 var12) (and (and (and (and (and (and (and (= var11 var16) (= var10 var15)) (= var9 var14)) (= var8 var13)) (= var7 var12)) (= var6 (|node::next| (getnode (read var16 var12))))) (and (and (and (and (and (= var5 (write var11 var7 (O_node (node nullAddr (|node::prev| (getnode (read var11 var7))))))) (= var4 var10)) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var0 var6))) (not (= var12 nullAddr))))) (inv_main654_5 var5 var4 var3 var2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main629_10_176 var5 var4 var3 var2 var1 var0) (= var0 var1))) (inv_main654_5 var5 var4 var3 var2 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Heap)) (or (not (and (inv_main635_10 var12 var11 var10 var9 var8 var7) (and (and (and (and (and (and (and (= var6 var12) (= var5 var11)) (= var4 var10)) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var0 (|node::prev| (getnode (read var12 var8))))) (and (not (= var8 nullAddr)) (not (= var7 var8)))))) (inv_main635_10 var6 var5 var4 var3 var0 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Heap)) (or (not (and (inv_main629_10_91 var12 var11 var10 var9 var8 var7) (and (and (and (and (and (and (and (and (= var6 var12) (= var5 var11)) (= var4 var10)) (= var3 var9)) (= var2 var10)) (= var1 var11)) (= var0 (|node::prev| (getnode (read var12 var10))))) (and (not (= var11 nullAddr)) (not (= var10 nullAddr)))) (= var7 var8)))) (inv_main635_10 var6 var5 var4 var3 var0 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main635_10_211 var5 var4 var3 var2 var1 var0) (and (= var1 nullAddr) (not (= var0 var1))))) (inv_main636_26_218 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (not (inv_main627_22 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (not (inv_main628_22 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (not (inv_main630_26 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (inv_main644_28 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (inv_main645_28 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (not (inv_main627_22_79 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (not (inv_main628_22_87 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (not (inv_main630_26_98 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (not (inv_main633_22 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (not (inv_main634_22 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (not (inv_main636_26 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (not (inv_main633_22_133 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (not (inv_main634_22_141 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (not (inv_main636_26_152 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (not (inv_main627_22_164 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (not (inv_main628_22_172 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (not (inv_main630_26_183 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (not (inv_main633_22_199 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (not (inv_main634_22_207 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (not (inv_main636_26_218 var5 var4 var3 var2 var1 var0))))
(check-sat)
