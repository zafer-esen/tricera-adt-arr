(set-logic HORN)
(set-info :source |
    Benchmark: C_VC
    Output by Princess (http://www.philipp.ruemmer.org/princess.shtml)
|)
(set-info :status sat)
(declare-heap Heap Addr HeapObject
 defObj
 ((HeapObject 0) (TreeNode 0)) (
  (
   (O_Int (getInt Int))
   (O_Addr (getAddr Addr))
   (O_TreeNode (getTreeNode TreeNode))
   (defObj)
  )
  (
   (TreeNode (left Addr) (right Addr))
  )
))
(declare-fun inv_main10 (Heap Addr Addr) Bool)
(declare-fun inv_main11 (Heap Addr Addr) Bool)
(declare-fun inv_main13 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main16 (Heap Addr Addr) Bool)
(declare-fun inv_main17 (Heap Addr Addr) Bool)
(declare-fun inv_main21 (Heap Addr Addr) Bool)
(declare-fun inv_main27 (Heap Addr Addr) Bool)
(declare-fun inv_main28 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main29 (Heap Addr Addr) Bool)
(declare-fun inv_main3 (Heap) Bool)
(declare-fun inv_main35 (Heap Addr Addr) Bool)
(declare-fun inv_main36 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main37 (Heap Addr Addr) Bool)
(declare-fun inv_main4 (Heap Addr Addr) Bool)
(declare-fun inv_main43 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main46 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main49 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main5 (Heap Addr Addr) Bool)
(declare-fun inv_main50 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main51 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main55 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main57 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main58 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main6 (Heap Addr Addr) Bool)
(assert (forall ((var0 Heap)) (or (not (= var0 emptyHeap)) (inv_main3 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (inv_main35 var2 var1 var0)) (inv_main37 (write var2 (right (getTreeNode (read var2 var0))) (O_TreeNode (TreeNode nullAddr (right (getTreeNode (read var2 (right (getTreeNode (read var2 var0))))))))) var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (inv_main5 var2 var1 var0)) (inv_main6 (write var2 var1 (O_TreeNode (TreeNode (left (getTreeNode (read var2 var1))) nullAddr))) var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (inv_main37 var2 var1 var0)) (inv_main6 (write var2 (right (getTreeNode (read var2 var0))) (O_TreeNode (TreeNode (left (getTreeNode (read var2 (right (getTreeNode (read var2 var0)))))) nullAddr))) var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Heap)) (or (not (and (inv_main21 var5 var4 var3) (and (= var2 0) (and (and (and (= var6 var5) (= var0 var4)) (= var1 var3)) (or (and (= (right (getTreeNode (read var5 var3))) nullAddr) (= var2 1)) (and (not (= (right (getTreeNode (read var5 var3))) nullAddr)) (= var2 0))))))) (inv_main6 var6 var0 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Int) (var6 Addr) (var7 Heap)) (or (not (and (inv_main21 var4 var3 var2) (and (= var0 0) (and (not (= var5 0)) (and (and (and (= var7 var4) (= var1 var3)) (= var6 var2)) (or (and (= (right (getTreeNode (read var4 var2))) nullAddr) (= var5 1)) (and (not (= (right (getTreeNode (read var4 var2))) nullAddr)) (= var5 0)))))))) (inv_main6 var7 var1 var6))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (inv_main10 var2 var1 var0)) (inv_main13 var2 var1 var0 (left (getTreeNode (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr)) (or (not (and (inv_main50 var3 var2 var1 var0) (and (and (and (and (= var4 var3) (= var8 var2)) (= var6 var1)) (= var5 var0)) (= var7 (left (getTreeNode (read var3 var1))))))) (inv_main43 var4 var8 var7 var5))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Addr)) (or (not (and (inv_main51 var4 var3 var2 var0) (and (and (and (and (= var6 var4) (= var7 var3)) (= var1 var2)) (= var8 var0)) (= var5 (right (getTreeNode (read var4 var2))))))) (inv_main43 var6 var7 var5 var8))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Heap) (var10 Heap)) (or (not (and (inv_main6 var7 var6 var5) (and (and (and (not (= var8 nullAddr)) (and (and (and (= var10 var9) (= var1 var8)) (= var0 var4)) (= var3 nullAddr))) (= var2 0)) (and (and (= var9 var7) (= var8 var6)) (= var4 nullAddr))))) (inv_main43 var10 var1 var1 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Heap) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Heap) (var15 Addr)) (or (not (and (inv_main57 var3 var9 var10 var1) (and (and (and (not (= var0 nullAddr)) (and (and (and (= var14 var2) (= var11 var0)) (= var13 var6)) (= var15 nullAddr))) (and (and (and (= var2 (write var5 var7 defObj)) (= var0 var12)) (= var6 var7)) (= var4 var8))) (and (and (and (= var5 (write var3 var1 (O_TreeNode (TreeNode nullAddr (right (getTreeNode (read var3 var1))))))) (= var12 var9)) (= var7 var10)) (= var8 var1))))) (inv_main43 var14 var11 var11 var15))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Heap) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr)) (or (not (and (inv_main58 var4 var11 var12 var0) (and (and (and (not (= var7 nullAddr)) (and (and (and (= var3 var5) (= var13 var7)) (= var8 var1)) (= var2 nullAddr))) (and (and (and (= var5 (write var10 var15 defObj)) (= var7 var6)) (= var1 var15)) (= var9 var14))) (and (and (and (= var10 (write var4 var0 (O_TreeNode (TreeNode (left (getTreeNode (read var4 var0))) nullAddr)))) (= var6 var11)) (= var15 var12)) (= var14 var0))))) (inv_main43 var3 var13 var13 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Heap) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Heap) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Heap) (var21 Addr)) (or (not (and (inv_main46 var3 var17 var18 var0 var12) (and (and (and (and (not (= var14 nullAddr)) (and (and (and (= var4 var16) (= var10 var14)) (= var11 var1)) (= var21 nullAddr))) (and (and (and (= var16 (write var20 var15 defObj)) (= var14 var9)) (= var1 var15)) (= var2 var7))) (and (= var19 nullAddr) (and (= var8 0) (and (= var12 nullAddr) (and (and (and (and (= var5 var3) (= var6 var17)) (= var13 var18)) (= var19 var0)) (= var8 (right (getTreeNode (read var3 var18))))))))) (and (and (and (= var20 var5) (= var9 nullAddr)) (= var15 var13)) (= var7 var19))))) (inv_main43 var4 var10 var10 var21))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (inv_main4 var2 var1 var0)) (inv_main5 (write var2 var1 (O_TreeNode (TreeNode nullAddr (right (getTreeNode (read var2 var1)))))) var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main55 var3 var2 var1 var0) (not (= var1 (left (getTreeNode (read var3 var0))))))) (inv_main58 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr)) (or (not (inv_main28 var2 var1 var0 var3)) (inv_main27 (write var2 var0 (O_TreeNode (TreeNode var3 (right (getTreeNode (read var2 var0)))))) var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (inv_main29 var2 var1 var0)) (inv_main21 (write var2 (left (getTreeNode (read var2 var0))) (O_TreeNode (TreeNode (left (getTreeNode (read var2 (left (getTreeNode (read var2 var0)))))) nullAddr))) var1 var0))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr)) (or (not (and (inv_main11 var5 var4 var3) (and (= var1 0) (and (and (and (= var0 var5) (= var2 var4)) (= var6 var3)) (or (and (= (left (getTreeNode (read var5 var3))) nullAddr) (= var1 1)) (and (not (= (left (getTreeNode (read var5 var3))) nullAddr)) (= var1 0))))))) (inv_main21 var0 var2 var6))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main11 var7 var6 var5) (and (= var1 0) (and (not (= var2 0)) (and (and (and (= var3 var7) (= var0 var6)) (= var4 var5)) (or (and (= (left (getTreeNode (read var7 var5))) nullAddr) (= var2 1)) (and (not (= (left (getTreeNode (read var7 var5))) nullAddr)) (= var2 0)))))))) (inv_main21 var3 var0 var4))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main49 var3 var2 var1 var0) (= (left (getTreeNode (read var3 var1))) nullAddr))) (inv_main51 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main49 var3 var2 var1 var0) (not (= (left (getTreeNode (read var3 var1))) nullAddr)))) (inv_main50 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main13 var3 var2 var1 var0) (= var0 nullAddr))) (inv_main11 var3 var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Addr)) (or (not (and (inv_main13 var6 var5 var4 var0) (and (= var7 0) (and (not (= var0 nullAddr)) (and (and (and (= var2 var6) (= var1 var5)) (= var3 var4)) (= var7 (right (getTreeNode (read var6 var4))))))))) (inv_main11 var2 var1 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (inv_main43 var3 var2 var1 var0)) (inv_main46 var3 var2 var1 var0 (left (getTreeNode (read var3 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Addr)) (or (not (and (inv_main46 var5 var4 var3 var2 var0) (and (not (= var6 nullAddr)) (and (= var9 0) (and (= var0 nullAddr) (and (and (and (and (= var7 var5) (= var8 var4)) (= var1 var3)) (= var6 var2)) (= var9 (right (getTreeNode (read var5 var3)))))))))) (inv_main55 var7 var8 var1 var6))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Int) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Addr)) (or (not (and (inv_main13 var7 var6 var5 var0) (and (not (= var3 0)) (and (not (= var8 0)) (and (not (= var0 nullAddr)) (and (and (and (= var2 var7) (= var1 var6)) (= var4 var5)) (= var8 (right (getTreeNode (read var7 var5)))))))))) (inv_main16 var2 var1 var4))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main55 var3 var2 var1 var0) (= var1 (left (getTreeNode (read var3 var0)))))) (inv_main57 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 TreeNode) (var6 Int) (var7 Addr) (var8 Heap)) (or (not (and (inv_main21 var4 var3 var2) (and (not (= var0 0)) (and (not (= var6 0)) (and (and (and (= var8 var4) (= var1 var3)) (= var7 var2)) (or (and (= (right (getTreeNode (read var4 var2))) nullAddr) (= var6 1)) (and (not (= (right (getTreeNode (read var4 var2))) nullAddr)) (= var6 0)))))))) (inv_main36 (newHeap (alloc var8 (O_TreeNode var5))) var1 var7 (newAddr (alloc var8 (O_TreeNode var5)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (inv_main36 var3 var2 var1 var0)) (inv_main35 (write var3 var1 (O_TreeNode (TreeNode (left (getTreeNode (read var3 var1))) var0))) var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main46 var4 var3 var2 var1 var0) (not (= var0 nullAddr)))) (inv_main49 var4 var3 var2 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Addr)) (or (not (and (inv_main46 var5 var4 var3 var2 var0) (and (not (= var9 0)) (and (= var0 nullAddr) (and (and (and (and (= var7 var5) (= var8 var4)) (= var1 var3)) (= var6 var2)) (= var9 (right (getTreeNode (read var5 var3))))))))) (inv_main49 var7 var8 var1 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (inv_main27 var2 var1 var0)) (inv_main29 (write var2 (left (getTreeNode (read var2 var0))) (O_TreeNode (TreeNode nullAddr (right (getTreeNode (read var2 (left (getTreeNode (read var2 var0))))))))) var1 var0))))
(assert (forall ((var0 Addr) (var1 TreeNode) (var2 Int) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Int)) (or (not (and (inv_main11 var7 var6 var5) (and (not (= var8 0)) (and (not (= var2 0)) (and (and (and (= var3 var7) (= var0 var6)) (= var4 var5)) (or (and (= (left (getTreeNode (read var7 var5))) nullAddr) (= var2 1)) (and (not (= (left (getTreeNode (read var7 var5))) nullAddr)) (= var2 0)))))))) (inv_main28 (newHeap (alloc var3 (O_TreeNode var1))) var0 var4 (newAddr (alloc var3 (O_TreeNode var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Int) (var8 Addr)) (or (not (and (inv_main13 var6 var5 var4 var0) (and (= var7 0) (and (not (= var8 0)) (and (not (= var0 nullAddr)) (and (and (and (= var2 var6) (= var1 var5)) (= var3 var4)) (= var8 (right (getTreeNode (read var6 var4)))))))))) (inv_main17 var2 var1 var3))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr)) (or (not (and (inv_main16 var4 var3 var2) (and (and (and (= var0 var4) (= var1 var3)) (= var6 var2)) (= var5 (left (getTreeNode (read var4 var2))))))) (inv_main10 var0 var1 var5))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr)) (or (not (and (inv_main17 var4 var3 var2) (and (and (and (= var0 var4) (= var1 var3)) (= var6 var2)) (= var5 (right (getTreeNode (read var4 var2))))))) (inv_main10 var0 var1 var5))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main6 var3 var2 var1) (not (= var0 0)))) (inv_main10 var3 var2 var2))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 TreeNode)) (or (not (inv_main3 var1)) (inv_main4 (newHeap (alloc var1 (O_TreeNode var2))) (newAddr (alloc var1 (O_TreeNode var2))) var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main4 var2 var1 var0) (not (is-O_TreeNode (read var2 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main5 var2 var1 var0) (not (is-O_TreeNode (read var2 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main10 var2 var1 var0) (not (is-O_TreeNode (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main13 var3 var2 var1 var0) (and (not (= var0 nullAddr)) (not (is-O_TreeNode (read var3 var1))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main16 var2 var1 var0) (not (is-O_TreeNode (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main17 var2 var1 var0) (not (is-O_TreeNode (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main11 var2 var1 var0) (not (is-O_TreeNode (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr)) (not (and (inv_main28 var2 var1 var0 var3) (not (is-O_TreeNode (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main27 var2 var1 var0) (not (is-O_TreeNode (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main27 var2 var1 var0) (not (is-O_TreeNode (read var2 (left (getTreeNode (read var2 var0))))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main29 var2 var1 var0) (not (is-O_TreeNode (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main29 var2 var1 var0) (not (is-O_TreeNode (read var2 (left (getTreeNode (read var2 var0))))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main21 var2 var1 var0) (not (is-O_TreeNode (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main36 var3 var2 var1 var0) (not (is-O_TreeNode (read var3 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main35 var2 var1 var0) (not (is-O_TreeNode (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main35 var2 var1 var0) (not (is-O_TreeNode (read var2 (right (getTreeNode (read var2 var0))))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main37 var2 var1 var0) (not (is-O_TreeNode (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main37 var2 var1 var0) (not (is-O_TreeNode (read var2 (right (getTreeNode (read var2 var0))))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main43 var3 var2 var1 var0) (not (is-O_TreeNode (read var3 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main46 var4 var3 var2 var1 var0) (and (= var0 nullAddr) (not (is-O_TreeNode (read var4 var2))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main49 var3 var2 var1 var0) (not (is-O_TreeNode (read var3 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main50 var3 var2 var1 var0) (not (is-O_TreeNode (read var3 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main51 var3 var2 var1 var0) (not (is-O_TreeNode (read var3 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main55 var3 var2 var1 var0) (not (is-O_TreeNode (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main57 var3 var2 var1 var0) (not (is-O_TreeNode (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main58 var3 var2 var1 var0) (not (is-O_TreeNode (read var3 var0)))))))
(check-sat)