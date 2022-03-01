(set-logic HORN)
(set-info :source |
    Benchmark: C_VC
    Output by Princess (http://www.philipp.ruemmer.org/princess.shtml)
|)
(set-info :status sat)
(declare-heap Heap Addr HeapObject
 defObj
 ((HeapObject 0) (TreeNode 0) (StackItem 0)) (
  (
   (O_Int (getInt Int))
   (O_UInt (getUInt Int))
   (O_Addr (getAddr Addr))
   (O_TreeNode (getTreeNode TreeNode))
   (O_StackItem (getStackItem StackItem))
   (defObj)
  )
  (
   (TreeNode (left Addr) (right Addr) (parent Addr))
  )
  (
   (StackItem (next Addr) (node Addr))
  )
))
(declare-fun inv_main12 (Heap Addr Addr) Bool)
(declare-fun inv_main13 (Heap Addr Addr) Bool)
(declare-fun inv_main15 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main18 (Heap Addr Addr) Bool)
(declare-fun inv_main19 (Heap Addr Addr) Bool)
(declare-fun inv_main23 (Heap Addr Addr) Bool)
(declare-fun inv_main29 (Heap Addr Addr) Bool)
(declare-fun inv_main30 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main31 (Heap Addr Addr) Bool)
(declare-fun inv_main32 (Heap Addr Addr) Bool)
(declare-fun inv_main38 (Heap Addr Addr) Bool)
(declare-fun inv_main39 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main4 (Heap) Bool)
(declare-fun inv_main40 (Heap Addr Addr) Bool)
(declare-fun inv_main41 (Heap Addr Addr) Bool)
(declare-fun inv_main43 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main44 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main48 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main49 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main5 (Heap Addr Addr) Bool)
(declare-fun inv_main53 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main54 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main57 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main59 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main6 (Heap Addr Addr) Bool)
(declare-fun inv_main61 (Heap Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main65 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main67 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main69 (Heap Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main7 (Heap Addr Addr) Bool)
(declare-fun inv_main8 (Heap Addr Addr) Bool)
(assert (forall ((var0 Heap)) (or (not (= var0 emptyHeap)) (inv_main4 var0))))
(assert (forall ((var0 Addr) (var1 StackItem) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Int) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main8 var8 var7 var6) (and (= var5 0) (and (and (= var4 var8) (= var3 var7)) (= var2 nullAddr))))) (inv_main43 (newHeap (alloc var4 (O_StackItem var1))) var3 var2 (newAddr (alloc var4 (O_StackItem var1))) var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main59 var4 var3 var2 var1 var0) (is-O_TreeNode (read var4 var2)))) (inv_main61 var4 var3 var2 var1 var0 (left (getTreeNode (read var4 var2)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main49 var10 var9 var8 var7 var6) (and (is-O_StackItem (read var10 var6)) (and (and (and (and (and (= var5 var10) (= var4 var9)) (= var3 var8)) (= var2 var7)) (= var1 var6)) (= var0 (node (getStackItem (read var10 var6)))))))) (inv_main53 (write var5 var1 defObj) var4 var0 var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main43 var4 var3 var2 var1 var0) (is-O_StackItem (read var4 var1)))) (inv_main44 (write var4 var1 (O_StackItem (StackItem nullAddr (node (getStackItem (read var4 var1)))))) var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (and (inv_main31 var2 var1 var0) (and (is-O_TreeNode (read var2 var0)) (is-O_TreeNode (read var2 (left (getTreeNode (read var2 var0)))))))) (inv_main32 (write var2 (left (getTreeNode (read var2 var0))) (O_TreeNode (TreeNode (left (getTreeNode (read var2 (left (getTreeNode (read var2 var0)))))) nullAddr (parent (getTreeNode (read var2 (left (getTreeNode (read var2 var0))))))))) var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (and (inv_main38 var2 var1 var0) (and (is-O_TreeNode (read var2 var0)) (is-O_TreeNode (read var2 (right (getTreeNode (read var2 var0)))))))) (inv_main40 (write var2 (right (getTreeNode (read var2 var0))) (O_TreeNode (TreeNode nullAddr (right (getTreeNode (read var2 (right (getTreeNode (read var2 var0)))))) (parent (getTreeNode (read var2 (right (getTreeNode (read var2 var0))))))))) var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Int) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main15 var8 var7 var6 var5) (and (= var4 0) (and (not (= var3 0)) (and (and (not (= var5 nullAddr)) (is-O_TreeNode (read var8 var6))) (and (and (and (= var2 var8) (= var1 var7)) (= var0 var6)) (= var3 (right (getTreeNode (read var8 var6)))))))))) (inv_main19 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (and (inv_main5 var2 var1 var0) (is-O_TreeNode (read var2 var1)))) (inv_main6 (write var2 var1 (O_TreeNode (TreeNode nullAddr (right (getTreeNode (read var2 var1))) (parent (getTreeNode (read var2 var1)))))) var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main65 var4 var3 var2 var1 var0) (is-O_StackItem (read var4 var0)))) (inv_main67 (write var4 var0 (O_StackItem (StackItem var1 (node (getStackItem (read var4 var0)))))) var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (and (inv_main7 var2 var1 var0) (is-O_TreeNode (read var2 var1)))) (inv_main8 (write var2 var1 (O_TreeNode (TreeNode (left (getTreeNode (read var2 var1))) (right (getTreeNode (read var2 var1))) nullAddr))) var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (and (inv_main41 var2 var1 var0) (and (is-O_TreeNode (read var2 var0)) (is-O_TreeNode (read var2 (right (getTreeNode (read var2 var0)))))))) (inv_main8 (write var2 (right (getTreeNode (read var2 var0))) (O_TreeNode (TreeNode (left (getTreeNode (read var2 (right (getTreeNode (read var2 var0)))))) (right (getTreeNode (read var2 (right (getTreeNode (read var2 var0)))))) var0))) var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Int) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main23 var6 var5 var4) (and (and (= var3 0) (is-O_TreeNode (read var6 var4))) (and (and (and (= var2 var6) (= var1 var5)) (= var0 var4)) (or (and (= (right (getTreeNode (read var6 var4))) nullAddr) (= var3 1)) (and (not (= (right (getTreeNode (read var6 var4))) nullAddr)) (= var3 0))))))) (inv_main8 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Int) (var4 Int) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main23 var7 var6 var5) (and (= var4 0) (and (and (not (= var3 0)) (is-O_TreeNode (read var7 var5))) (and (and (and (= var2 var7) (= var1 var6)) (= var0 var5)) (or (and (= (right (getTreeNode (read var7 var5))) nullAddr) (= var3 1)) (and (not (= (right (getTreeNode (read var7 var5))) nullAddr)) (= var3 0)))))))) (inv_main8 var2 var1 var0))))
(assert (forall ((var0 TreeNode) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Int) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main23 var8 var7 var6) (and (not (= var5 0)) (and (and (not (= var4 0)) (is-O_TreeNode (read var8 var6))) (and (and (and (= var3 var8) (= var2 var7)) (= var1 var6)) (or (and (= (right (getTreeNode (read var8 var6))) nullAddr) (= var4 1)) (and (not (= (right (getTreeNode (read var8 var6))) nullAddr)) (= var4 0)))))))) (inv_main39 (newHeap (alloc var3 (O_TreeNode var0))) var2 var1 (newAddr (alloc var3 (O_TreeNode var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (and (inv_main6 var2 var1 var0) (is-O_TreeNode (read var2 var1)))) (inv_main7 (write var2 var1 (O_TreeNode (TreeNode (left (getTreeNode (read var2 var1))) nullAddr (parent (getTreeNode (read var2 var1)))))) var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main30 var3 var2 var1 var0) (is-O_TreeNode (read var3 var1)))) (inv_main29 (write var3 var1 (O_TreeNode (TreeNode var0 (right (getTreeNode (read var3 var1))) (parent (getTreeNode (read var3 var1)))))) var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main18 var6 var5 var4) (and (is-O_TreeNode (read var6 var4)) (and (and (and (= var3 var6) (= var2 var5)) (= var1 var4)) (= var0 (left (getTreeNode (read var6 var4)))))))) (inv_main12 var3 var2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main19 var6 var5 var4) (and (is-O_TreeNode (read var6 var4)) (and (and (and (= var3 var6) (= var2 var5)) (= var1 var4)) (= var0 (right (getTreeNode (read var6 var4)))))))) (inv_main12 var3 var2 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main8 var3 var2 var1) (not (= var0 0)))) (inv_main12 var3 var2 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main39 var3 var2 var1 var0) (is-O_TreeNode (read var3 var1)))) (inv_main38 (write var3 var1 (O_TreeNode (TreeNode (left (getTreeNode (read var3 var1))) var0 (parent (getTreeNode (read var3 var1)))))) var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main48 var10 var9 var8 var7 var6) (and (is-O_StackItem (read var10 var7)) (and (and (and (and (and (= var5 var10) (= var4 var9)) (= var3 var8)) (= var2 var7)) (= var1 var6)) (= var0 (next (getStackItem (read var10 var7)))))))) (inv_main49 var5 var4 var3 var0 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main67 var4 var3 var2 var1 var0) (is-O_TreeNode (read var4 var2)))) (inv_main69 var4 var3 var2 var1 var0 (right (getTreeNode (read var4 var2)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main53 var4 var3 var2 var1 var0) (and (is-O_TreeNode (read var4 var2)) (= (left (getTreeNode (read var4 var2))) nullAddr)))) (inv_main54 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main61 var10 var9 var8 var7 var6 var5) (and (is-O_StackItem (read var10 var6)) (and (and (and (and (= var4 (write var10 var6 (O_StackItem (StackItem (next (getStackItem (read var10 var6))) var5)))) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var0 var6))))) (inv_main54 var4 var3 var2 var0 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main57 var4 var3 var2 var1 var0) (is-O_StackItem (read var4 var0)))) (inv_main59 (write var4 var0 (O_StackItem (StackItem var1 (node (getStackItem (read var4 var0)))))) var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (and (inv_main12 var2 var1 var0) (is-O_TreeNode (read var2 var0)))) (inv_main15 var2 var1 var0 (left (getTreeNode (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main44 var9 var8 var7 var6 var5) (and (and (not (= var4 nullAddr)) (is-O_StackItem (read var9 var6))) (and (and (and (and (= var3 (write var9 var6 (O_StackItem (StackItem (next (getStackItem (read var9 var6))) var8)))) (= var2 var8)) (= var1 var7)) (= var4 var6)) (= var0 var5))))) (inv_main48 var3 var2 var1 var4 var4))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main54 var9 var8 var7 var6 var5) (and (and (not (= var4 nullAddr)) (and (and (and (and (= var3 (write var9 var7 defObj)) (= var2 var8)) (= var1 var7)) (= var4 var6)) (= var0 var5))) (and (is-O_TreeNode (read var9 var7)) (= (right (getTreeNode (read var9 var7))) nullAddr))))) (inv_main48 var3 var2 var1 var4 var4))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Heap)) (or (not (and (inv_main69 var15 var14 var13 var12 var11 var10) (and (and (not (= var9 nullAddr)) (and (and (and (and (= var8 (write var7 var6 defObj)) (= var5 var4)) (= var3 var6)) (= var9 var2)) (= var1 var2))) (and (is-O_StackItem (read var15 var11)) (and (and (and (and (= var7 (write var15 var11 (O_StackItem (StackItem (next (getStackItem (read var15 var11))) var10)))) (= var4 var14)) (= var6 var13)) (= var0 var12)) (= var2 var11)))))) (inv_main48 var8 var5 var3 var9 var9))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 StackItem) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Heap)) (or (not (and (inv_main54 var11 var10 var9 var8 var7) (and (and (and (and (and (and (= var6 (newHeap (alloc var11 (O_StackItem var5)))) (= var4 var10)) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var0 (newAddr (alloc var11 (O_StackItem var5))))) (and (is-O_TreeNode (read var11 var9)) (not (= (right (getTreeNode (read var11 var9))) nullAddr)))))) (inv_main65 var6 var4 var3 var2 var0))))
(assert (forall ((var0 TreeNode) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Int) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main13 var8 var7 var6) (and (not (= var5 0)) (and (and (not (= var4 0)) (is-O_TreeNode (read var8 var6))) (and (and (and (= var3 var8) (= var2 var7)) (= var1 var6)) (or (and (= (left (getTreeNode (read var8 var6))) nullAddr) (= var4 1)) (and (not (= (left (getTreeNode (read var8 var6))) nullAddr)) (= var4 0)))))))) (inv_main30 (newHeap (alloc var3 (O_TreeNode var0))) var2 var1 (newAddr (alloc var3 (O_TreeNode var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (and (inv_main29 var2 var1 var0) (and (is-O_TreeNode (read var2 var0)) (is-O_TreeNode (read var2 (left (getTreeNode (read var2 var0)))))))) (inv_main31 (write var2 (left (getTreeNode (read var2 var0))) (O_TreeNode (TreeNode nullAddr (right (getTreeNode (read var2 (left (getTreeNode (read var2 var0)))))) (parent (getTreeNode (read var2 (left (getTreeNode (read var2 var0))))))))) var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Int) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main15 var8 var7 var6 var5) (and (not (= var4 0)) (and (not (= var3 0)) (and (and (not (= var5 nullAddr)) (is-O_TreeNode (read var8 var6))) (and (and (and (= var2 var8) (= var1 var7)) (= var0 var6)) (= var3 (right (getTreeNode (read var8 var6)))))))))) (inv_main18 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main15 var3 var2 var1 var0) (= var0 nullAddr))) (inv_main13 var3 var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main15 var7 var6 var5 var4) (and (= var3 0) (and (and (not (= var4 nullAddr)) (is-O_TreeNode (read var7 var5))) (and (and (and (= var2 var7) (= var1 var6)) (= var0 var5)) (= var3 (right (getTreeNode (read var7 var5))))))))) (inv_main13 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (and (inv_main40 var2 var1 var0) (and (is-O_TreeNode (read var2 var0)) (is-O_TreeNode (read var2 (right (getTreeNode (read var2 var0)))))))) (inv_main41 (write var2 (right (getTreeNode (read var2 var0))) (O_TreeNode (TreeNode (left (getTreeNode (read var2 (right (getTreeNode (read var2 var0)))))) nullAddr (parent (getTreeNode (read var2 (right (getTreeNode (read var2 var0))))))))) var1 var0))))
(assert (forall ((var0 Addr) (var1 TreeNode) (var2 Heap)) (or (not (inv_main4 var2)) (inv_main5 (newHeap (alloc var2 (O_TreeNode var1))) (newAddr (alloc var2 (O_TreeNode var1))) var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 StackItem) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Heap)) (or (not (and (inv_main53 var11 var10 var9 var8 var7) (and (and (and (and (and (and (= var6 (newHeap (alloc var11 (O_StackItem var5)))) (= var4 var10)) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var0 (newAddr (alloc var11 (O_StackItem var5))))) (and (is-O_TreeNode (read var11 var9)) (not (= (left (getTreeNode (read var11 var9))) nullAddr)))))) (inv_main57 var6 var4 var3 var2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (and (inv_main32 var2 var1 var0) (and (is-O_TreeNode (read var2 var0)) (is-O_TreeNode (read var2 (left (getTreeNode (read var2 var0)))))))) (inv_main23 (write var2 (left (getTreeNode (read var2 var0))) (O_TreeNode (TreeNode (left (getTreeNode (read var2 (left (getTreeNode (read var2 var0)))))) (right (getTreeNode (read var2 (left (getTreeNode (read var2 var0)))))) var0))) var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Int) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main13 var6 var5 var4) (and (and (= var3 0) (is-O_TreeNode (read var6 var4))) (and (and (and (= var2 var6) (= var1 var5)) (= var0 var4)) (or (and (= (left (getTreeNode (read var6 var4))) nullAddr) (= var3 1)) (and (not (= (left (getTreeNode (read var6 var4))) nullAddr)) (= var3 0))))))) (inv_main23 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Int) (var4 Int) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main13 var7 var6 var5) (and (= var4 0) (and (and (not (= var3 0)) (is-O_TreeNode (read var7 var5))) (and (and (and (= var2 var7) (= var1 var6)) (= var0 var5)) (or (and (= (left (getTreeNode (read var7 var5))) nullAddr) (= var3 1)) (and (not (= (left (getTreeNode (read var7 var5))) nullAddr)) (= var3 0)))))))) (inv_main23 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main5 var2 var1 var0) (not (is-O_TreeNode (read var2 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main6 var2 var1 var0) (not (is-O_TreeNode (read var2 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main7 var2 var1 var0) (not (is-O_TreeNode (read var2 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main12 var2 var1 var0) (not (is-O_TreeNode (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main15 var3 var2 var1 var0) (and (not (= var0 nullAddr)) (not (is-O_TreeNode (read var3 var1))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main18 var2 var1 var0) (not (is-O_TreeNode (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main19 var2 var1 var0) (not (is-O_TreeNode (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main13 var2 var1 var0) (not (is-O_TreeNode (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main30 var3 var2 var1 var0) (not (is-O_TreeNode (read var3 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main29 var2 var1 var0) (not (is-O_TreeNode (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main29 var2 var1 var0) (and (is-O_TreeNode (read var2 var0)) (not (is-O_TreeNode (read var2 (left (getTreeNode (read var2 var0)))))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main31 var2 var1 var0) (not (is-O_TreeNode (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main31 var2 var1 var0) (and (is-O_TreeNode (read var2 var0)) (not (is-O_TreeNode (read var2 (left (getTreeNode (read var2 var0)))))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main32 var2 var1 var0) (not (is-O_TreeNode (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main32 var2 var1 var0) (and (is-O_TreeNode (read var2 var0)) (not (is-O_TreeNode (read var2 (left (getTreeNode (read var2 var0)))))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main23 var2 var1 var0) (not (is-O_TreeNode (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main39 var3 var2 var1 var0) (not (is-O_TreeNode (read var3 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main38 var2 var1 var0) (not (is-O_TreeNode (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main38 var2 var1 var0) (and (is-O_TreeNode (read var2 var0)) (not (is-O_TreeNode (read var2 (right (getTreeNode (read var2 var0)))))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main40 var2 var1 var0) (not (is-O_TreeNode (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main40 var2 var1 var0) (and (is-O_TreeNode (read var2 var0)) (not (is-O_TreeNode (read var2 (right (getTreeNode (read var2 var0)))))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main41 var2 var1 var0) (not (is-O_TreeNode (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main41 var2 var1 var0) (and (is-O_TreeNode (read var2 var0)) (not (is-O_TreeNode (read var2 (right (getTreeNode (read var2 var0)))))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main43 var4 var3 var2 var1 var0) (not (is-O_StackItem (read var4 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main44 var4 var3 var2 var1 var0) (not (is-O_StackItem (read var4 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main48 var4 var3 var2 var1 var0) (not (is-O_StackItem (read var4 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main49 var4 var3 var2 var1 var0) (not (is-O_StackItem (read var4 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main53 var4 var3 var2 var1 var0) (not (is-O_TreeNode (read var4 var2)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main57 var4 var3 var2 var1 var0) (not (is-O_StackItem (read var4 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main59 var4 var3 var2 var1 var0) (not (is-O_TreeNode (read var4 var2)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (not (and (inv_main61 var5 var4 var3 var2 var1 var0) (not (is-O_StackItem (read var5 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main54 var4 var3 var2 var1 var0) (not (is-O_TreeNode (read var4 var2)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main65 var4 var3 var2 var1 var0) (not (is-O_StackItem (read var4 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main67 var4 var3 var2 var1 var0) (not (is-O_TreeNode (read var4 var2)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (not (and (inv_main69 var5 var4 var3 var2 var1 var0) (not (is-O_StackItem (read var5 var1)))))))
(check-sat)
