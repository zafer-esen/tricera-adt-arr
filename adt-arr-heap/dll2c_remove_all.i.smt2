(set-logic HORN)
(set-info :source |
    Benchmark: C_VC
    Output by Princess (http://www.philipp.ruemmer.org/princess.shtml)
|)
(set-info :status sat)
(declare-heap Heap Addr HeapObject
 defObj
 ((HeapObject 0) (node 0)) (
  (
   (O_Int (getInt Int))
   (O_Addr (getAddr Addr))
   (O_node (getnode node))
   (defObj)
  )
  (
   (node (next Addr) (prev Addr) (data Int))
  )
))
(declare-fun inv_main12 (Heap Int Int Int Int Int Addr) Bool)
(declare-fun inv_main15 (Heap Int Int Int Int Int Addr Int) Bool)
(declare-fun inv_main18 (Heap Int Int Int Int Int Addr) Bool)
(declare-fun inv_main19 (Heap Int Int Int Int Int Addr) Bool)
(declare-fun inv_main22 (Heap Int Int Int Int Addr Addr) Bool)
(declare-fun inv_main23 (Heap Int Int Int Int Addr Addr) Bool)
(declare-fun inv_main29 (Heap Int Int Int Int Addr Addr Int Addr) Bool)
(declare-fun inv_main32 (Heap Int Int Int Int Addr Addr Int Addr Int) Bool)
(declare-fun inv_main35 (Heap Int Int Int Int Addr Addr Int Addr) Bool)
(declare-fun inv_main36 (Heap Int Int Int Int Addr Addr Int Addr) Bool)
(declare-fun inv_main38 (Heap Int Int Int Int Addr Addr Addr) Bool)
(declare-fun inv_main4 (Heap Int Int) Bool)
(declare-fun inv_main41 (Heap Int Int Int Int Addr Addr Addr) Bool)
(declare-fun inv_main44 (Heap Int Int Int Int Addr Addr) Bool)
(declare-fun inv_main47 (Heap Int Int Addr Int) Bool)
(declare-fun inv_main51 (Heap Int Int Addr Int Int) Bool)
(declare-fun inv_main56 (Heap Int Int Addr Int Int Addr) Bool)
(declare-fun inv_main58 (Heap Int Int Addr Int Int Addr Addr) Bool)
(declare-fun inv_main59 (Heap Int Int Addr Int Int Addr Addr) Bool)
(declare-fun inv_main65 (Heap Int Int Addr Int) Bool)
(assert (forall ((var0 Heap)) (or (not (= var0 emptyHeap)) (inv_main4 var0 2 1))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Heap) (var4 Int) (var5 Int) (var6 Int)) (or (not (inv_main56 var3 var4 var6 var0 var1 var5 var2)) (inv_main58 var3 var4 var6 var0 var1 var5 var2 (prev (getnode (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Int) (var4 Addr) (var5 Int) (var6 Int)) (or (not (inv_main23 var1 var2 var3 var6 var5 var4 var0)) (inv_main44 (write var1 var0 (O_node (node var4 (prev (getnode (read var1 var0))) (data (getnode (read var1 var0)))))) var2 var3 var6 var5 var4 var0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 node) (var4 Int) (var5 Heap) (var6 Int) (var7 Int) (var8 Addr) (var9 Int) (var10 Int) (var11 Int) (var12 Addr) (var13 Addr) (var14 Int) (var15 Int) (var16 Int)) (or (not (and (inv_main22 var5 var14 var16 var10 var9 var8 var2) (and (and (not (= nullAddr var13)) (and (and (and (and (and (and (and (and (= var1 (newHeap (alloc var5 (O_node var3)))) (= var11 var14)) (= var6 var16)) (= var7 var10)) (= var4 var9)) (= var12 var8)) (= var0 var2)) (= var15 var9)) (= var13 (newAddr (alloc var5 (O_node var3)))))) (<= 0 (+ (+ var10 (- 1)) (- 1)))))) (inv_main29 var1 var11 var6 var7 var4 var12 var0 var15 var13))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Int) (var6 Int) (var7 Int)) (or (not (inv_main58 var4 var5 var7 var0 var1 var6 var3 var2)) (inv_main59 (write var4 var3 (O_node (node (next (getnode (read var4 var3))) var2 (data (getnode (read var4 var3)))))) var5 var7 var0 var1 var6 var3 var2))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Int) (var4 Int) (var5 Heap) (var6 Int) (var7 Int) (var8 Addr) (var9 Int) (var10 Heap) (var11 Int) (var12 Addr)) (or (not (and (inv_main51 var5 var7 var11 var0 var3 var9) (and (not (= var8 var12)) (and (and (and (and (and (and (= var10 var5) (= var1 var7)) (= var6 var11)) (= var12 var0)) (= var4 var3)) (= var2 var9)) (= var8 (next (getnode (read var5 var0)))))))) (inv_main56 var10 var1 var6 var12 var4 var2 var8))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Int)) (or (not (inv_main12 var1 var2 var4 var6 var5 var3 var0)) (inv_main18 (write var1 var0 (O_node (node nullAddr (prev (getnode (read var1 var0))) (data (getnode (read var1 var0)))))) var2 var4 var6 var5 var3 var0))))
(assert (forall ((var0 Int) (var1 Heap) (var2 Int) (var3 Addr) (var4 Int) (var5 Addr) (var6 Int) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Int) (var11 Addr) (var12 Int) (var13 Addr) (var14 Heap) (var15 Int) (var16 Addr) (var17 Addr) (var18 Int) (var19 Int) (var20 Addr) (var21 Int) (var22 Int) (var23 Int)) (or (not (and (inv_main59 var7 var19 var23 var13 var4 var12 var17 var5) (and (and (and (and (and (and (and (and (= var14 (write var7 var5 (O_node (node var17 (prev (getnode (read var7 var5))) (data (getnode (read var7 var5))))))) (= var21 var19)) (= var18 var23)) (= var3 var13)) (= var0 var4)) (= var22 var12)) (= var11 var17)) (= var8 var5)) (and (and (and (and (and (and (and (= var1 (write var14 var3 defObj)) (= var10 var21)) (= var15 var18)) (= var20 var3)) (= var2 var0)) (= var6 var22)) (= var9 var11)) (= var16 var8))))) (inv_main47 var1 var10 var15 var9 (+ var2 1)))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Int) (var4 Heap) (var5 Addr) (var6 Int) (var7 Addr) (var8 Heap) (var9 Int) (var10 Int) (var11 Int) (var12 Int) (var13 Int) (var14 Addr) (var15 Int) (var16 Int) (var17 Addr) (var18 Int) (var19 Heap) (var20 Int) (var21 Int) (var22 Int) (var23 Addr) (var24 Int) (var25 Int)) (or (not (and (inv_main51 var8 var22 var25 var14 var3 var11) (and (and (and (= var5 var23) (and (and (and (and (and (and (= var19 var8) (= var15 var22)) (= var21 var25)) (= var23 var14)) (= var16 var3)) (= var0 var11)) (= var5 (next (getnode (read var8 var14)))))) (and (and (and (and (and (and (= var4 (write var19 var23 defObj)) (= var10 var15)) (= var20 var21)) (= var7 var23)) (= var12 var16)) (= var24 var0)) (= var17 var5))) (and (and (and (and (and (= var2 var4) (= var18 var10)) (= var9 var20)) (= var1 nullAddr)) (= var6 var12)) (= var13 var24))))) (inv_main47 var2 var18 var9 var1 (+ var6 1)))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Heap) (var5 Heap) (var6 Addr) (var7 Int) (var8 Int) (var9 Addr) (var10 Int) (var11 Int) (var12 Addr) (var13 Int)) (or (not (and (inv_main44 var4 var11 var13 var8 var7 var6 var3) (and (and (and (and (and (and (= var5 (write var4 var6 (O_node (node (next (getnode (read var4 var6))) var3 (data (getnode (read var4 var6))))))) (= var0 var11)) (= var1 var13)) (= var10 var8)) (= var2 var7)) (= var12 var6)) (= var9 var3)))) (inv_main47 var5 var0 var1 var12 0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Int) (var7 Addr) (var8 Int) (var9 Int) (var10 Int) (var11 Addr) (var12 Int) (var13 Heap) (var14 Int) (var15 Int)) (or (not (and (inv_main41 var4 var14 var15 var9 var8 var7 var3 var5) (and (and (and (and (and (and (and (= var13 (write var4 var7 (O_node (node (next (getnode (read var4 var7))) var5 (data (getnode (read var4 var7))))))) (= var10 var14)) (= var0 var15)) (= var12 var9)) (= var6 var8)) (= var11 var7)) (= var2 var3)) (= var1 var5)))) (inv_main22 var13 var10 var0 (+ var12 (- 1)) var6 var1 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Int) (var8 Int) (var9 Int) (var10 Addr) (var11 Int) (var12 Int) (var13 Int) (var14 Addr) (var15 Int)) (or (not (and (inv_main38 var3 var13 var15 var8 var7 var6 var1 var4) (and (= var0 nullAddr) (and (and (and (and (and (and (and (= var5 (write var3 var4 (O_node (node var6 (prev (getnode (read var3 var4))) (data (getnode (read var3 var4))))))) (= var9 var13)) (= var12 var15)) (= var2 var8)) (= var11 var7)) (= var0 var6)) (= var14 var1)) (= var10 var4))))) (inv_main22 var5 var9 var12 (+ var2 (- 1)) var11 var10 var14))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Heap) (var4 Int) (var5 Int) (var6 Int) (var7 Int) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Int) (var12 Int) (var13 Int)) (or (not (and (inv_main19 var3 var12 var13 var6 var5 var4 var9) (and (and (and (and (and (and (= var8 (write var3 var9 (O_node (node (next (getnode (read var3 var9))) (prev (getnode (read var3 var9))) var4)))) (= var7 var12)) (= var11 var13)) (= var0 var6)) (= var1 var5)) (= var2 var4)) (= var10 var9)))) (inv_main22 var8 var7 var11 var0 var1 var10 var10))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Int)) (or (not (inv_main18 var1 var2 var4 var6 var5 var3 var0)) (inv_main19 (write var1 var0 (O_node (node (next (getnode (read var1 var0))) nullAddr (data (getnode (read var1 var0)))))) var2 var4 var6 var5 var3 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Heap) (var3 Int) (var4 Int)) (or (not (and (inv_main47 var2 var3 var4 var0 var1) (<= 0 (+ (+ var3 (* (- 1) var1)) (- 1))))) (inv_main51 var2 var3 var4 var0 var1 3))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Addr) (var4 Heap) (var5 Int) (var6 Int) (var7 Addr) (var8 Int) (var9 Int)) (or (not (inv_main32 var4 var5 var6 var9 var8 var7 var3 var2 var0 var1)) (inv_main32 var4 var5 var6 var9 var8 var7 var3 var2 var0 var1))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap) (var6 Addr) (var7 Int) (var8 Int) (var9 Addr) (var10 node) (var11 Int) (var12 Int) (var13 Addr) (var14 Int) (var15 Heap) (var16 Int)) (or (not (and (inv_main22 var5 var12 var14 var8 var7 var6 var3) (and (and (= nullAddr var2) (and (and (and (and (and (and (and (and (= var15 (newHeap (alloc var5 (O_node var10)))) (= var4 var12)) (= var16 var14)) (= var0 var8)) (= var1 var7)) (= var13 var6)) (= var9 var3)) (= var11 var7)) (= var2 (newAddr (alloc var5 (O_node var10)))))) (<= 0 (+ (+ var8 (- 1)) (- 1)))))) (inv_main32 var15 var4 var16 var0 var1 var13 var9 var11 var2 1))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Int) (var4 Addr) (var5 Int) (var6 Int)) (or (not (and (inv_main22 var1 var2 var3 var6 var5 var4 var0) (not (<= 0 (+ (+ var6 (- 1)) (- 1)))))) (inv_main23 var1 var2 var3 var6 var5 var4 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Int) (var9 Int) (var10 Addr) (var11 Int) (var12 Int) (var13 Int) (var14 Int) (var15 Addr) (var16 Int) (var17 Int)) (or (not (and (inv_main36 var4 var16 var17 var9 var8 var7 var2 var12 var10) (and (and (and (and (and (and (and (and (= var6 (write var4 var10 (O_node (node (next (getnode (read var4 var10))) (prev (getnode (read var4 var10))) var12)))) (= var14 var16)) (= var11 var17)) (= var13 var9)) (= var0 var8)) (= var1 var7)) (= var15 var2)) (= var3 var12)) (= var5 var10)))) (inv_main38 var6 var14 var11 var13 var0 var1 var15 var5))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Int)) (or (not (inv_main15 var2 var3 var5 var7 var6 var4 var1 var0)) (inv_main15 var2 var3 var5 var7 var6 var4 var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Heap) (var4 Heap) (var5 Int) (var6 node) (var7 Int) (var8 Addr) (var9 Int) (var10 Int)) (or (not (and (inv_main4 var4 var5 var9) (and (= nullAddr var8) (and (and (and (and (and (and (= var3 (newHeap (alloc var4 (O_node var6)))) (= var0 var5)) (= var10 var9)) (= var2 var5)) (= var1 var9)) (= var7 var9)) (= var8 (newAddr (alloc var4 (O_node var6)))))))) (inv_main15 var3 var0 var10 var2 var1 var7 var8 1))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Heap) (var4 Int) (var5 Int) (var6 Addr) (var7 Int) (var8 Int)) (or (not (inv_main35 var3 var4 var5 var8 var7 var6 var2 var1 var0)) (inv_main36 (write var3 var0 (O_node (node (next (getnode (read var3 var0))) nullAddr (data (getnode (read var3 var0)))))) var4 var5 var8 var7 var6 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Heap) (var3 Int) (var4 Int)) (or (not (and (inv_main47 var2 var3 var4 var0 var1) (and (not (= nullAddr var0)) (not (<= 0 (+ (+ var3 (* (- 1) var1)) (- 1))))))) (inv_main65 var2 var3 var4 var0 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap) (var5 Addr) (var6 Int) (var7 Int) (var8 Addr) (var9 Int) (var10 Int) (var11 Addr) (var12 Addr) (var13 Int) (var14 Heap) (var15 Int)) (or (not (and (inv_main38 var4 var13 var15 var10 var9 var8 var2 var5) (and (not (= var11 nullAddr)) (and (and (and (and (and (and (and (= var14 (write var4 var5 (O_node (node var8 (prev (getnode (read var4 var5))) (data (getnode (read var4 var5))))))) (= var0 var13)) (= var3 var15)) (= var7 var10)) (= var6 var9)) (= var11 var8)) (= var12 var2)) (= var1 var5))))) (inv_main41 var14 var0 var3 var7 var6 var11 var12 var1))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Heap) (var4 Int) (var5 Int) (var6 Int) (var7 Int) (var8 Int) (var9 node) (var10 Int)) (or (not (and (inv_main4 var3 var6 var10) (and (not (= nullAddr var0)) (and (and (and (and (and (and (= var1 (newHeap (alloc var3 (O_node var9)))) (= var5 var6)) (= var8 var10)) (= var4 var6)) (= var2 var10)) (= var7 var10)) (= var0 (newAddr (alloc var3 (O_node var9)))))))) (inv_main12 var1 var5 var8 var4 var2 var7 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Heap) (var4 Int) (var5 Int) (var6 Addr) (var7 Int) (var8 Int)) (or (not (inv_main29 var3 var4 var5 var8 var7 var6 var2 var1 var0)) (inv_main35 (write var3 var0 (O_node (node nullAddr (prev (getnode (read var3 var0))) (data (getnode (read var3 var0)))))) var4 var5 var8 var7 var6 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Int)) (not (and (inv_main12 var1 var2 var4 var6 var5 var3 var0) (not (is-O_node (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Int)) (not (and (inv_main18 var1 var2 var4 var6 var5 var3 var0) (not (is-O_node (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Int)) (not (and (inv_main19 var1 var2 var4 var6 var5 var3 var0) (not (is-O_node (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Heap) (var4 Int) (var5 Int) (var6 Addr) (var7 Int) (var8 Int)) (not (and (inv_main29 var3 var4 var5 var8 var7 var6 var2 var1 var0) (not (is-O_node (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Heap) (var4 Int) (var5 Int) (var6 Addr) (var7 Int) (var8 Int)) (not (and (inv_main35 var3 var4 var5 var8 var7 var6 var2 var1 var0) (not (is-O_node (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Heap) (var4 Int) (var5 Int) (var6 Addr) (var7 Int) (var8 Int)) (not (and (inv_main36 var3 var4 var5 var8 var7 var6 var2 var1 var0) (not (is-O_node (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Int) (var4 Int) (var5 Addr) (var6 Int) (var7 Int)) (not (and (inv_main38 var1 var3 var4 var7 var6 var5 var0 var2) (not (is-O_node (read var1 var2)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Int) (var4 Int) (var5 Addr) (var6 Int) (var7 Int)) (not (and (inv_main41 var1 var3 var4 var7 var6 var5 var0 var2) (not (is-O_node (read var1 var5)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Int) (var4 Addr) (var5 Int) (var6 Int)) (not (and (inv_main23 var1 var2 var3 var6 var5 var4 var0) (not (is-O_node (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Int) (var4 Addr) (var5 Int) (var6 Int)) (not (and (inv_main44 var1 var2 var3 var6 var5 var4 var0) (not (is-O_node (read var1 var4)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Heap) (var3 Int) (var4 Int) (var5 Int)) (not (and (inv_main51 var2 var3 var5 var0 var1 var4) (not (is-O_node (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Heap) (var4 Int) (var5 Int) (var6 Int)) (not (and (inv_main56 var3 var4 var6 var0 var1 var5 var2) (not (is-O_node (read var3 var0)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Int) (var6 Int) (var7 Int)) (not (and (inv_main58 var4 var5 var7 var0 var1 var6 var3 var2) (not (is-O_node (read var4 var3)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Int) (var6 Int) (var7 Int)) (not (and (inv_main59 var4 var5 var7 var0 var1 var6 var3 var2) (not (is-O_node (read var4 var2)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Heap) (var3 Int) (var4 Int)) (not (inv_main65 var2 var3 var4 var0 var1))))
(check-sat)
