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

(declare-datatypes ((HeapObject 0) (TreeNode 0))
                   (((O_Int (getInt Int)) (O_UInt (getUInt Int)) (O_Addr (getAddr Addr)) (O_AddrRange (getAddrRange AddrRange)) (O_TreeNode (getTreeNode TreeNode)) (defObj))
                   ((TreeNode (|TreeNode::left| Addr) (|TreeNode::right| Addr)))))
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
(declare-fun inv_main (Heap Addr Addr) Bool)
(declare-fun inv_main529_2 (Heap) Bool)
(declare-fun inv_main529_2_1 (Heap Addr Addr) Bool)
(declare-fun inv_main534_10 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main536_5 (Heap Addr Addr) Bool)
(declare-fun inv_main538_5 (Heap Addr Addr) Bool)
(declare-fun inv_main541_4 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main546_4 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main556_10 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main559_5 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main561_5 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main563_13 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main565_5 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main567_5 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main_12 (Heap Addr Addr) Bool)
(declare-fun inv_main_16 (Heap Addr Addr) Bool)
(declare-fun inv_main_17 (Heap Addr Addr) Bool)
(declare-fun inv_main_2 (Heap Addr Addr) Bool)
(declare-fun inv_main_21 (Heap Addr Addr) Bool)
(declare-fun inv_main_22 (Heap Addr Addr) Bool)
(declare-fun inv_main_27 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main_32 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main_5 (Heap Addr Addr) Bool)
(declare-fun inv_main_6 (Heap Addr Addr) Bool)
(assert (forall ((var0 Heap)) (or (not (= var0 emptyHeap)) (inv_main529_2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main556_10 var4 var3 var2 var1 var0) (not (= var0 nullAddr)))) (inv_main_32 var4 var3 var2 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main556_10 var9 var8 var7 var6 var5) (and (not (= var4 0)) (and (and (= var5 nullAddr) (is-O_TreeNode (read var9 var7))) (and (and (and (and (= var3 var9) (= var2 var8)) (= var1 var7)) (= var0 var6)) (= var4 (|TreeNode::right| (getTreeNode (read var9 var7))))))))) (inv_main_32 var3 var2 var1 var1))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main541_4 var4 var3 var2 var1) (and (and (is-O_TreeNode (read var4 var2)) (is-O_TreeNode (read var4 var2))) (= var0 (write var4 var2 (O_TreeNode (TreeNode var1 (|TreeNode::right| (getTreeNode (read var4 var2)))))))))) (inv_main_16 var0 var3 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main559_5 var8 var7 var6 var5) (and (is-O_TreeNode (read var8 var6)) (and (and (and (and (= var4 var8) (= var3 var7)) (= var2 var6)) (= var1 var5)) (= var0 (|TreeNode::left| (getTreeNode (read var8 var6)))))))) (inv_main_27 var4 var3 var0 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main561_5 var8 var7 var6 var5) (and (is-O_TreeNode (read var8 var6)) (and (and (and (and (= var4 var8) (= var3 var7)) (= var2 var6)) (= var1 var5)) (= var0 (|TreeNode::right| (getTreeNode (read var8 var6)))))))) (inv_main_27 var4 var3 var0 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main_2 var10 var9 var8) (and (and (and (not (= var7 nullAddr)) (and (and (and (= var6 var5) (= var4 var7)) (= var3 var2)) (= var1 nullAddr))) (= var0 0)) (and (and (= var5 var10) (= var7 var9)) (= var2 nullAddr))))) (inv_main_27 var6 var4 var4 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap) (var10 Heap) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Heap)) (or (not (and (inv_main565_5 var15 var14 var13 var12) (and (and (and (and (not (= var11 nullAddr)) (and (and (and (= var10 var9) (= var8 var11)) (= var7 var6)) (= var5 nullAddr))) (and (and (and (= var9 (write var4 var3 defObj)) (= var11 var2)) (= var6 var3)) (= var1 var0))) (and (is-O_TreeNode (read var15 var12)) (is-O_TreeNode (read var15 var12)))) (and (and (and (= var4 (write var15 var12 (O_TreeNode (TreeNode nullAddr (|TreeNode::right| (getTreeNode (read var15 var12))))))) (= var2 var14)) (= var3 var13)) (= var0 var12))))) (inv_main_27 var10 var8 var8 var5))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap) (var10 Heap) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Heap)) (or (not (and (inv_main567_5 var15 var14 var13 var12) (and (and (and (and (not (= var11 nullAddr)) (and (and (and (= var10 var9) (= var8 var11)) (= var7 var6)) (= var5 nullAddr))) (and (and (and (= var9 (write var4 var3 defObj)) (= var11 var2)) (= var6 var3)) (= var1 var0))) (and (is-O_TreeNode (read var15 var12)) (is-O_TreeNode (read var15 var12)))) (and (and (and (= var4 (write var15 var12 (O_TreeNode (TreeNode (|TreeNode::left| (getTreeNode (read var15 var12))) nullAddr)))) (= var2 var14)) (= var3 var13)) (= var0 var12))))) (inv_main_27 var10 var8 var8 var5))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Heap) (var15 Heap) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Heap)) (or (not (and (inv_main556_10 var21 var20 var19 var18 var17) (and (and (and (and (not (= var16 nullAddr)) (and (and (and (= var15 var14) (= var13 var16)) (= var12 var11)) (= var10 nullAddr))) (and (and (and (= var14 (write var9 var8 defObj)) (= var16 var7)) (= var11 var8)) (= var6 var5))) (and (= var4 nullAddr) (and (= var3 0) (and (and (= var17 nullAddr) (is-O_TreeNode (read var21 var19))) (and (and (and (and (= var2 var21) (= var1 var20)) (= var0 var19)) (= var4 var18)) (= var3 (|TreeNode::right| (getTreeNode (read var21 var19))))))))) (and (and (and (= var9 var2) (= var7 nullAddr)) (= var8 var0)) (= var5 var4))))) (inv_main_27 var15 var13 var13 var10))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Int) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main534_10 var8 var7 var6 var5) (and (not (= var4 0)) (and (not (= var3 0)) (and (and (not (= var5 nullAddr)) (is-O_TreeNode (read var8 var6))) (and (and (and (= var2 var8) (= var1 var7)) (= var0 var6)) (= var3 (|TreeNode::right| (getTreeNode (read var8 var6)))))))))) (inv_main536_5 var2 var1 var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main546_4 var4 var3 var2 var1) (and (and (is-O_TreeNode (read var4 var2)) (is-O_TreeNode (read var4 var2))) (= var0 (write var4 var2 (O_TreeNode (TreeNode (|TreeNode::left| (getTreeNode (read var4 var2))) var1))))))) (inv_main_21 var0 var3 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main_32 var3 var2 var1 var0) (and (is-O_TreeNode (read var3 var1)) (not (= (|TreeNode::left| (getTreeNode (read var3 var1))) nullAddr))))) (inv_main559_5 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 TreeNode) (var3 Heap) (var4 Heap)) (or (not (and (inv_main529_2 var4) (and (= var3 (newHeap (alloc var4 (O_TreeNode var2)))) (= var1 (newAddr (alloc var4 (O_TreeNode var2))))))) (inv_main529_2_1 var3 var1 var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main var3 var2 var1) (and (and (is-O_TreeNode (read var3 var2)) (is-O_TreeNode (read var3 var2))) (= var0 (write var3 var2 (O_TreeNode (TreeNode (|TreeNode::left| (getTreeNode (read var3 var2))) nullAddr))))))) (inv_main_2 var0 var2 var1))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main_22 var3 var2 var1) (and (and (and (is-O_TreeNode (read var3 var1)) (is-O_TreeNode (read var3 (|TreeNode::right| (getTreeNode (read var3 var1)))))) (is-O_TreeNode (read var3 (|TreeNode::right| (getTreeNode (read var3 var1)))))) (= var0 (write var3 (|TreeNode::right| (getTreeNode (read var3 var1))) (O_TreeNode (TreeNode (|TreeNode::left| (getTreeNode (read var3 (|TreeNode::right| (getTreeNode (read var3 var1)))))) nullAddr))))))) (inv_main_2 var0 var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Int) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main_12 var6 var5 var4) (and (and (= var3 0) (is-O_TreeNode (read var6 var4))) (and (and (and (= var2 var6) (= var1 var5)) (= var0 var4)) (or (and (= (|TreeNode::right| (getTreeNode (read var6 var4))) nullAddr) (= var3 1)) (and (not (= (|TreeNode::right| (getTreeNode (read var6 var4))) nullAddr)) (= var3 0))))))) (inv_main_2 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Int) (var4 Int) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main_12 var7 var6 var5) (and (= var4 0) (and (and (not (= var3 0)) (is-O_TreeNode (read var7 var5))) (and (and (and (= var2 var7) (= var1 var6)) (= var0 var5)) (or (and (= (|TreeNode::right| (getTreeNode (read var7 var5))) nullAddr) (= var3 1)) (and (not (= (|TreeNode::right| (getTreeNode (read var7 var5))) nullAddr)) (= var3 0)))))))) (inv_main_2 var2 var1 var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main_21 var3 var2 var1) (and (and (and (is-O_TreeNode (read var3 var1)) (is-O_TreeNode (read var3 (|TreeNode::right| (getTreeNode (read var3 var1)))))) (is-O_TreeNode (read var3 (|TreeNode::right| (getTreeNode (read var3 var1)))))) (= var0 (write var3 (|TreeNode::right| (getTreeNode (read var3 var1))) (O_TreeNode (TreeNode nullAddr (|TreeNode::right| (getTreeNode (read var3 (|TreeNode::right| (getTreeNode (read var3 var1))))))))))))) (inv_main_22 var0 var2 var1))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main_16 var3 var2 var1) (and (and (and (is-O_TreeNode (read var3 var1)) (is-O_TreeNode (read var3 (|TreeNode::left| (getTreeNode (read var3 var1)))))) (is-O_TreeNode (read var3 (|TreeNode::left| (getTreeNode (read var3 var1)))))) (= var0 (write var3 (|TreeNode::left| (getTreeNode (read var3 var1))) (O_TreeNode (TreeNode nullAddr (|TreeNode::right| (getTreeNode (read var3 (|TreeNode::left| (getTreeNode (read var3 var1))))))))))))) (inv_main_17 var0 var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main536_5 var6 var5 var4) (and (is-O_TreeNode (read var6 var4)) (and (and (and (= var3 var6) (= var2 var5)) (= var1 var4)) (= var0 (|TreeNode::left| (getTreeNode (read var6 var4)))))))) (inv_main_5 var3 var2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main538_5 var6 var5 var4) (and (is-O_TreeNode (read var6 var4)) (and (and (and (= var3 var6) (= var2 var5)) (= var1 var4)) (= var0 (|TreeNode::right| (getTreeNode (read var6 var4)))))))) (inv_main_5 var3 var2 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main_2 var3 var2 var1) (not (= var0 0)))) (inv_main_5 var3 var2 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main556_10 var9 var8 var7 var6 var5) (and (not (= var4 nullAddr)) (and (= var3 0) (and (and (= var5 nullAddr) (is-O_TreeNode (read var9 var7))) (and (and (and (and (= var2 var9) (= var1 var8)) (= var0 var7)) (= var4 var6)) (= var3 (|TreeNode::right| (getTreeNode (read var9 var7)))))))))) (inv_main563_13 var2 var1 var0 var4))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main_17 var3 var2 var1) (and (and (and (is-O_TreeNode (read var3 var1)) (is-O_TreeNode (read var3 (|TreeNode::left| (getTreeNode (read var3 var1)))))) (is-O_TreeNode (read var3 (|TreeNode::left| (getTreeNode (read var3 var1)))))) (= var0 (write var3 (|TreeNode::left| (getTreeNode (read var3 var1))) (O_TreeNode (TreeNode (|TreeNode::left| (getTreeNode (read var3 (|TreeNode::left| (getTreeNode (read var3 var1)))))) nullAddr))))))) (inv_main_12 var0 var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Int) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main_6 var6 var5 var4) (and (and (= var3 0) (is-O_TreeNode (read var6 var4))) (and (and (and (= var2 var6) (= var1 var5)) (= var0 var4)) (or (and (= (|TreeNode::left| (getTreeNode (read var6 var4))) nullAddr) (= var3 1)) (and (not (= (|TreeNode::left| (getTreeNode (read var6 var4))) nullAddr)) (= var3 0))))))) (inv_main_12 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Int) (var4 Int) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main_6 var7 var6 var5) (and (= var4 0) (and (and (not (= var3 0)) (is-O_TreeNode (read var7 var5))) (and (and (and (= var2 var7) (= var1 var6)) (= var0 var5)) (or (and (= (|TreeNode::left| (getTreeNode (read var7 var5))) nullAddr) (= var3 1)) (and (not (= (|TreeNode::left| (getTreeNode (read var7 var5))) nullAddr)) (= var3 0)))))))) (inv_main_12 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main563_13 var3 var2 var1 var0) (and (is-O_TreeNode (read var3 var0)) (= var1 (|TreeNode::left| (getTreeNode (read var3 var0))))))) (inv_main565_5 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main_32 var3 var2 var1 var0) (and (is-O_TreeNode (read var3 var1)) (= (|TreeNode::left| (getTreeNode (read var3 var1))) nullAddr)))) (inv_main561_5 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Int) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main534_10 var8 var7 var6 var5) (and (= var4 0) (and (not (= var3 0)) (and (and (not (= var5 nullAddr)) (is-O_TreeNode (read var8 var6))) (and (and (and (= var2 var8) (= var1 var7)) (= var0 var6)) (= var3 (|TreeNode::right| (getTreeNode (read var8 var6)))))))))) (inv_main538_5 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main563_13 var3 var2 var1 var0) (and (is-O_TreeNode (read var3 var0)) (not (= var1 (|TreeNode::left| (getTreeNode (read var3 var0)))))))) (inv_main567_5 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 TreeNode) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Int) (var7 Int) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main_6 var10 var9 var8) (and (and (and (not (= var7 0)) (and (and (not (= var6 0)) (is-O_TreeNode (read var10 var8))) (and (and (and (= var5 var10) (= var4 var9)) (= var3 var8)) (or (and (= (|TreeNode::left| (getTreeNode (read var10 var8))) nullAddr) (= var6 1)) (and (not (= (|TreeNode::left| (getTreeNode (read var10 var8))) nullAddr)) (= var6 0)))))) (= var2 (newHeap (alloc var5 (O_TreeNode var1))))) (= var0 (newAddr (alloc var5 (O_TreeNode var1))))))) (inv_main541_4 var2 var4 var3 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main_5 var3 var2 var1) (and (is-O_TreeNode (read var3 var1)) (= var0 (|TreeNode::left| (getTreeNode (read var3 var1))))))) (inv_main534_10 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main_27 var4 var3 var2 var1) (and (is-O_TreeNode (read var4 var2)) (= var0 (|TreeNode::left| (getTreeNode (read var4 var2))))))) (inv_main556_10 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main529_2_1 var3 var2 var1) (and (and (is-O_TreeNode (read var3 var2)) (is-O_TreeNode (read var3 var2))) (= var0 (write var3 var2 (O_TreeNode (TreeNode nullAddr (|TreeNode::right| (getTreeNode (read var3 var2)))))))))) (inv_main var0 var2 var1))))
(assert (forall ((var0 Addr) (var1 TreeNode) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Int) (var7 Int) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main_12 var10 var9 var8) (and (and (and (not (= var7 0)) (and (and (not (= var6 0)) (is-O_TreeNode (read var10 var8))) (and (and (and (= var5 var10) (= var4 var9)) (= var3 var8)) (or (and (= (|TreeNode::right| (getTreeNode (read var10 var8))) nullAddr) (= var6 1)) (and (not (= (|TreeNode::right| (getTreeNode (read var10 var8))) nullAddr)) (= var6 0)))))) (= var2 (newHeap (alloc var5 (O_TreeNode var1))))) (= var0 (newAddr (alloc var5 (O_TreeNode var1))))))) (inv_main546_4 var2 var4 var3 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main534_10 var3 var2 var1 var0) (= var0 nullAddr))) (inv_main_6 var3 var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main534_10 var7 var6 var5 var4) (and (= var3 0) (and (and (not (= var4 nullAddr)) (is-O_TreeNode (read var7 var5))) (and (and (and (= var2 var7) (= var1 var6)) (= var0 var5)) (= var3 (|TreeNode::right| (getTreeNode (read var7 var5))))))))) (inv_main_6 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main529_2_1 var2 var1 var0) (not (is-O_TreeNode (read var2 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main529_2_1 var2 var1 var0) (and (is-O_TreeNode (read var2 var1)) (not (is-O_TreeNode (read var2 var1))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main var2 var1 var0) (not (is-O_TreeNode (read var2 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main var2 var1 var0) (and (is-O_TreeNode (read var2 var1)) (not (is-O_TreeNode (read var2 var1))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_5 var2 var1 var0) (not (is-O_TreeNode (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main534_10 var3 var2 var1 var0) (and (not (= var0 nullAddr)) (not (is-O_TreeNode (read var3 var1))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main536_5 var2 var1 var0) (not (is-O_TreeNode (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main538_5 var2 var1 var0) (not (is-O_TreeNode (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_6 var2 var1 var0) (not (is-O_TreeNode (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main541_4 var3 var2 var1 var0) (not (is-O_TreeNode (read var3 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main541_4 var3 var2 var1 var0) (and (is-O_TreeNode (read var3 var1)) (not (is-O_TreeNode (read var3 var1))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_16 var2 var1 var0) (not (is-O_TreeNode (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_16 var2 var1 var0) (and (is-O_TreeNode (read var2 var0)) (not (is-O_TreeNode (read var2 (|TreeNode::left| (getTreeNode (read var2 var0)))))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_16 var2 var1 var0) (and (and (is-O_TreeNode (read var2 var0)) (is-O_TreeNode (read var2 (|TreeNode::left| (getTreeNode (read var2 var0)))))) (not (is-O_TreeNode (read var2 (|TreeNode::left| (getTreeNode (read var2 var0)))))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_17 var2 var1 var0) (not (is-O_TreeNode (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_17 var2 var1 var0) (and (is-O_TreeNode (read var2 var0)) (not (is-O_TreeNode (read var2 (|TreeNode::left| (getTreeNode (read var2 var0)))))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_17 var2 var1 var0) (and (and (is-O_TreeNode (read var2 var0)) (is-O_TreeNode (read var2 (|TreeNode::left| (getTreeNode (read var2 var0)))))) (not (is-O_TreeNode (read var2 (|TreeNode::left| (getTreeNode (read var2 var0)))))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_12 var2 var1 var0) (not (is-O_TreeNode (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main546_4 var3 var2 var1 var0) (not (is-O_TreeNode (read var3 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main546_4 var3 var2 var1 var0) (and (is-O_TreeNode (read var3 var1)) (not (is-O_TreeNode (read var3 var1))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_21 var2 var1 var0) (not (is-O_TreeNode (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_21 var2 var1 var0) (and (is-O_TreeNode (read var2 var0)) (not (is-O_TreeNode (read var2 (|TreeNode::right| (getTreeNode (read var2 var0)))))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_21 var2 var1 var0) (and (and (is-O_TreeNode (read var2 var0)) (is-O_TreeNode (read var2 (|TreeNode::right| (getTreeNode (read var2 var0)))))) (not (is-O_TreeNode (read var2 (|TreeNode::right| (getTreeNode (read var2 var0)))))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_22 var2 var1 var0) (not (is-O_TreeNode (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_22 var2 var1 var0) (and (is-O_TreeNode (read var2 var0)) (not (is-O_TreeNode (read var2 (|TreeNode::right| (getTreeNode (read var2 var0)))))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main_22 var2 var1 var0) (and (and (is-O_TreeNode (read var2 var0)) (is-O_TreeNode (read var2 (|TreeNode::right| (getTreeNode (read var2 var0)))))) (not (is-O_TreeNode (read var2 (|TreeNode::right| (getTreeNode (read var2 var0)))))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_27 var3 var2 var1 var0) (not (is-O_TreeNode (read var3 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main556_10 var4 var3 var2 var1 var0) (and (= var0 nullAddr) (not (is-O_TreeNode (read var4 var2))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_32 var3 var2 var1 var0) (not (is-O_TreeNode (read var3 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main559_5 var3 var2 var1 var0) (not (is-O_TreeNode (read var3 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main561_5 var3 var2 var1 var0) (not (is-O_TreeNode (read var3 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main563_13 var3 var2 var1 var0) (not (is-O_TreeNode (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main565_5 var3 var2 var1 var0) (not (is-O_TreeNode (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main565_5 var3 var2 var1 var0) (and (is-O_TreeNode (read var3 var0)) (not (is-O_TreeNode (read var3 var0))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main567_5 var3 var2 var1 var0) (not (is-O_TreeNode (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main567_5 var3 var2 var1 var0) (and (is-O_TreeNode (read var3 var0)) (not (is-O_TreeNode (read var3 var0))))))))
(check-sat)
