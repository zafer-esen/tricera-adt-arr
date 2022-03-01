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
   (O_UInt (getUInt Int))
   (O_Addr (getAddr Addr))
   (O_node (getnode node))
   (defObj)
  )
  (
   (node (data Int) (next Addr) (prev Addr))
  )
))
(declare-fun inv_main12 (Heap Int Int Int Int Addr Addr) Bool)
(declare-fun inv_main15 (Heap Int Int Int Int Addr Addr Int) Bool)
(declare-fun inv_main18 (Heap Int Int Int Int Addr Addr) Bool)
(declare-fun inv_main19 (Heap Int Int Int Int Addr Addr) Bool)
(declare-fun inv_main22 (Heap Int Int Int Int Addr Addr) Bool)
(declare-fun inv_main35 (Heap Int Int Addr Int Int Int Int Addr) Bool)
(declare-fun inv_main38 (Heap Int Int Addr Int Int Int Int Addr Int) Bool)
(declare-fun inv_main4 (Heap Int Int) Bool)
(declare-fun inv_main41 (Heap Int Int Addr Int Int Int Int Addr) Bool)
(declare-fun inv_main42 (Heap Int Int Addr Int Int Int Int Addr) Bool)
(declare-fun inv_main44 (Heap Int Int Addr Int Int Int Addr) Bool)
(declare-fun inv_main47 (Heap Int Int Addr Int Int Int Addr) Bool)
(declare-fun inv_main49 (Heap Int Int Addr Int Addr) Bool)
(declare-fun inv_main50 (Heap Int Int Addr Int Addr) Bool)
(declare-fun inv_main55 (Heap Int Int Addr Int Addr Int) Bool)
(declare-fun inv_main57 (Heap Int Int Addr Int Addr Int) Bool)
(declare-fun inv_main58 (Heap Int Int Addr Int Addr Int Addr) Bool)
(declare-fun inv_main70 (Heap Int Int Addr Int Addr Int Addr) Bool)
(declare-fun inv_main73 (Heap Int Int Addr Int Addr Int) Bool)
(declare-fun inv_main8 (Heap Int Int Int Int Addr) Bool)
(assert (forall ((var0 Heap)) (or (not (= var0 emptyHeap)) (inv_main4 var0 2 1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Addr) (var7 Int) (var8 Int) (var9 Heap)) (or (not (inv_main38 var9 var8 var7 var6 var5 var4 var3 var2 var1 var0)) (inv_main38 var9 var8 var7 var6 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Int) (var4 Addr) (var5 Int) (var6 Int) (var7 node) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Int) (var12 Int) (var13 Int) (var14 Int) (var15 Heap)) (or (not (and (inv_main8 var15 var14 var13 var12 var11 var10) (and (and (= nullAddr var9) (and (and (and (and (and (and (and (and (= var8 (newHeap (alloc var15 (O_node var7)))) (= var6 var14)) (= var5 var13)) (= var4 var10)) (= var3 5)) (= var2 3)) (= var1 5)) (= var0 5)) (= var9 (newAddr (alloc var15 (O_node var7)))))) (not (<= 0 (+ var12 (- 1))))))) (inv_main38 var8 var6 var5 var4 var3 var2 var1 var0 var9 1))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Int) (var10 Int) (var11 Int) (var12 Addr) (var13 Int) (var14 Int) (var15 Heap)) (or (not (and (inv_main44 var15 var14 var13 var12 var11 var10 var9 var8) (and (and (not (= var7 nullAddr)) (is-O_node (read var15 var8))) (and (and (and (and (and (and (and (= var6 (write var15 var8 (O_node (node (data (getnode (read var15 var8))) var12 (prev (getnode (read var15 var8))))))) (= var5 var14)) (= var4 var13)) (= var7 var12)) (= var3 var11)) (= var2 var10)) (= var1 var9)) (= var0 var8))))) (inv_main47 var6 var5 var4 var7 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Int) (var4 Int) (var5 Heap)) (or (not (and (inv_main49 var5 var4 var3 var2 var1 var0) (and (is-O_node (read var5 var0)) (= var1 (data (getnode (read var5 var0))))))) (inv_main50 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Int) (var4 Int) (var5 Addr) (var6 Int) (var7 Int) (var8 Heap)) (or (not (and (inv_main35 var8 var7 var6 var5 var4 var3 var2 var1 var0) (is-O_node (read var8 var0)))) (inv_main41 (write var8 var0 (O_node (node (data (getnode (read var8 var0))) nullAddr (prev (getnode (read var8 var0)))))) var7 var6 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Heap)) (or (not (inv_main15 var7 var6 var5 var4 var3 var2 var1 var0)) (inv_main15 var7 var6 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Int) (var4 Int) (var5 node) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Int) (var10 Int) (var11 Int) (var12 Int) (var13 Heap)) (or (not (and (inv_main8 var13 var12 var11 var10 var9 var8) (and (and (= nullAddr var7) (and (and (and (and (and (and (= var6 (newHeap (alloc var13 (O_node var5)))) (= var4 var12)) (= var3 var11)) (= var2 var10)) (= var1 var9)) (= var0 var8)) (= var7 (newAddr (alloc var13 (O_node var5)))))) (<= 0 (+ var10 (- 1)))))) (inv_main15 var6 var4 var3 var2 var1 var0 var7 1))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Int) (var4 Int) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Int) (var10 Int) (var11 Int) (var12 Int) (var13 Heap)) (or (not (and (inv_main19 var13 var12 var11 var10 var9 var8 var7) (and (and (not (= var6 nullAddr)) (is-O_node (read var13 var7))) (and (and (and (and (and (and (= var5 (write var13 var7 (O_node (node (data (getnode (read var13 var7))) (next (getnode (read var13 var7))) nullAddr)))) (= var4 var12)) (= var3 var11)) (= var2 var10)) (= var1 var9)) (= var6 var8)) (= var0 var7))))) (inv_main22 var5 var4 var3 var2 var1 var6 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Heap)) (or (not (and (inv_main12 var6 var5 var4 var3 var2 var1 var0) (is-O_node (read var6 var0)))) (inv_main18 (write var6 var0 (O_node (node var2 (next (getnode (read var6 var0))) (prev (getnode (read var6 var0)))))) var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Heap)) (or (not (and (inv_main18 var6 var5 var4 var3 var2 var1 var0) (is-O_node (read var6 var0)))) (inv_main19 (write var6 var0 (O_node (node (data (getnode (read var6 var0))) var1 (prev (getnode (read var6 var0)))))) var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Addr) (var4 Int) (var5 Int) (var6 Heap)) (or (not (and (inv_main55 var6 var5 var4 var3 var2 var1 var0) (not (= var1 nullAddr)))) (inv_main57 var6 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Int) (var4 Addr) (var5 Int) (var6 Int) (var7 Heap) (var8 Addr) (var9 Int) (var10 Int) (var11 Int) (var12 Addr) (var13 Int) (var14 Int) (var15 Heap)) (or (not (and (inv_main47 var15 var14 var13 var12 var11 var10 var9 var8) (and (is-O_node (read var15 var12)) (and (and (and (and (and (and (and (= var7 (write var15 var12 (O_node (node (data (getnode (read var15 var12))) (next (getnode (read var15 var12))) var8)))) (= var6 var14)) (= var5 var13)) (= var4 var12)) (= var3 var11)) (= var2 var10)) (= var1 var9)) (= var0 var8))))) (inv_main49 var7 var6 var5 var0 var3 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Int) (var10 Int) (var11 Int) (var12 Addr) (var13 Int) (var14 Int) (var15 Heap)) (or (not (and (inv_main44 var15 var14 var13 var12 var11 var10 var9 var8) (and (and (= var7 nullAddr) (is-O_node (read var15 var8))) (and (and (and (and (and (and (and (= var6 (write var15 var8 (O_node (node (data (getnode (read var15 var8))) var12 (prev (getnode (read var15 var8))))))) (= var5 var14)) (= var4 var13)) (= var7 var12)) (= var3 var11)) (= var2 var10)) (= var1 var9)) (= var0 var8))))) (inv_main49 var6 var5 var4 var0 var3 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Int) (var4 Addr) (var5 Int) (var6 Int) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Int) (var11 Addr) (var12 Int) (var13 Addr) (var14 Int) (var15 Int) (var16 Heap) (var17 Addr) (var18 Addr) (var19 Int) (var20 Addr) (var21 Int) (var22 Addr) (var23 Int) (var24 Int) (var25 Heap)) (or (not (and (inv_main70 var25 var24 var23 var22 var21 var20 var19 var18) (and (not (= var17 nullAddr)) (and (and (is-O_node (read var25 var18)) (and (and (and (and (and (and (and (and (= var16 var25) (= var15 var24)) (= var14 var23)) (= var13 var22)) (= var12 var21)) (= var11 var20)) (= var10 var19)) (= var9 var18)) (= var8 (next (getnode (read var25 var18)))))) (and (and (and (and (and (and (and (and (= var7 (write var16 var9 defObj)) (= var6 var15)) (= var5 var14)) (= var4 var13)) (= var3 var12)) (= var2 var11)) (= var1 var10)) (= var0 var9)) (= var17 var8)))))) (inv_main70 var7 var6 var5 var4 var3 var2 var1 var17))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Addr) (var4 Int) (var5 Int) (var6 Heap)) (or (not (and (inv_main55 var6 var5 var4 var3 var2 var1 var0) (and (not (= var3 nullAddr)) (and (= var0 (+ 1 var5)) (= var1 nullAddr))))) (inv_main70 var6 var5 var4 var3 var2 var1 var0 var3))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Int) (var4 Int) (var5 Addr) (var6 Int) (var7 Int) (var8 Heap) (var9 Addr) (var10 Int) (var11 Int) (var12 Int) (var13 Int) (var14 Addr) (var15 Int) (var16 Int) (var17 Heap)) (or (not (and (inv_main42 var17 var16 var15 var14 var13 var12 var11 var10 var9) (and (is-O_node (read var17 var9)) (and (and (and (and (and (and (and (and (= var8 (write var17 var9 (O_node (node var10 (next (getnode (read var17 var9))) (prev (getnode (read var17 var9))))))) (= var7 var16)) (= var6 var15)) (= var5 var14)) (= var4 var13)) (= var3 var12)) (= var2 var11)) (= var1 var10)) (= var0 var9))))) (inv_main44 var8 var7 var6 var5 var4 var3 var2 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Int) (var4 Addr) (var5 Int) (var6 Int) (var7 Heap)) (or (not (and (inv_main58 var7 var6 var5 var4 var3 var2 var1 var0) (and (is-O_node (read var7 var2)) (= var5 (data (getnode (read var7 var2))))))) (inv_main55 var7 var6 var5 var4 var3 var0 (+ var1 1)))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Int) (var5 Int) (var6 Heap) (var7 Addr) (var8 Int) (var9 Addr) (var10 Int) (var11 Int) (var12 Heap)) (or (not (and (inv_main50 var12 var11 var10 var9 var8 var7) (and (is-O_node (read var12 var7)) (and (and (and (and (and (and (= var6 var12) (= var5 var11)) (= var4 var10)) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var0 (next (getnode (read var12 var7)))))))) (inv_main55 var6 var5 var4 var3 var2 var0 1))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Int) (var4 Int) (var5 Addr) (var6 Int) (var7 Int) (var8 Heap)) (or (not (and (inv_main41 var8 var7 var6 var5 var4 var3 var2 var1 var0) (is-O_node (read var8 var0)))) (inv_main42 (write var8 var0 (O_node (node (data (getnode (read var8 var0))) (next (getnode (read var8 var0))) nullAddr))) var7 var6 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Addr) (var4 Int) (var5 Int) (var6 Heap)) (or (not (and (inv_main57 var6 var5 var4 var3 var2 var1 var0) (is-O_node (read var6 var1)))) (inv_main58 var6 var5 var4 var3 var2 var1 var0 (next (getnode (read var6 var1)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Int) (var4 Int) (var5 node) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Int) (var10 Int) (var11 Int) (var12 Int) (var13 Heap)) (or (not (and (inv_main8 var13 var12 var11 var10 var9 var8) (and (and (not (= nullAddr var7)) (and (and (and (and (and (and (= var6 (newHeap (alloc var13 (O_node var5)))) (= var4 var12)) (= var3 var11)) (= var2 var10)) (= var1 var9)) (= var0 var8)) (= var7 (newAddr (alloc var13 (O_node var5)))))) (<= 0 (+ var10 (- 1)))))) (inv_main12 var6 var4 var3 var2 var1 var0 var7))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Int) (var10 Int) (var11 Int) (var12 Int) (var13 Heap)) (or (not (and (inv_main22 var13 var12 var11 var10 var9 var8 var7) (and (is-O_node (read var13 var8)) (and (and (and (and (and (and (= var6 (write var13 var8 (O_node (node (data (getnode (read var13 var8))) (next (getnode (read var13 var8))) var7)))) (= var5 var12)) (= var4 var11)) (= var3 var10)) (= var2 var9)) (= var1 var8)) (= var0 var7))))) (inv_main8 var6 var5 var4 (+ var3 (- 1)) var2 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Int) (var4 Int) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Int) (var10 Int) (var11 Int) (var12 Int) (var13 Heap)) (or (not (and (inv_main19 var13 var12 var11 var10 var9 var8 var7) (and (and (= var6 nullAddr) (is-O_node (read var13 var7))) (and (and (and (and (and (and (= var5 (write var13 var7 (O_node (node (data (getnode (read var13 var7))) (next (getnode (read var13 var7))) nullAddr)))) (= var4 var12)) (= var3 var11)) (= var2 var10)) (= var1 var9)) (= var6 var8)) (= var0 var7))))) (inv_main8 var5 var4 var3 (+ var2 (- 1)) var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Heap)) (or (not (inv_main4 var2 var1 var0)) (inv_main8 var2 var1 var0 var1 var0 nullAddr))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Int) (var4 Addr) (var5 Int) (var6 Int) (var7 Heap)) (or (not (and (inv_main58 var7 var6 var5 var4 var3 var2 var1 var0) (and (is-O_node (read var7 var2)) (not (= var5 (data (getnode (read var7 var2)))))))) (inv_main73 var7 var6 var5 var4 var3 var2 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Addr) (var4 Int) (var5 Int) (var6 Heap)) (or (not (and (inv_main55 var6 var5 var4 var3 var2 var1 var0) (and (not (= var0 (+ 1 var5))) (= var1 nullAddr)))) (inv_main73 var6 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Addr) (var4 Int) (var5 Int) (var6 Heap)) (or (not (and (inv_main49 var6 var5 var4 var3 var2 var1) (and (is-O_node (read var6 var1)) (not (= var2 (data (getnode (read var6 var1)))))))) (inv_main73 var6 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Int) (var4 Addr) (var5 Int) (var6 Int) (var7 node) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Int) (var12 Int) (var13 Int) (var14 Int) (var15 Heap)) (or (not (and (inv_main8 var15 var14 var13 var12 var11 var10) (and (and (not (= nullAddr var9)) (and (and (and (and (and (and (and (and (= var8 (newHeap (alloc var15 (O_node var7)))) (= var6 var14)) (= var5 var13)) (= var4 var10)) (= var3 5)) (= var2 3)) (= var1 5)) (= var0 5)) (= var9 (newAddr (alloc var15 (O_node var7)))))) (not (<= 0 (+ var12 (- 1))))))) (inv_main35 var8 var6 var5 var4 var3 var2 var1 var0 var9))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Heap)) (not (and (inv_main12 var6 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var6 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Heap)) (not (and (inv_main18 var6 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var6 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Heap)) (not (and (inv_main19 var6 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var6 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Heap)) (not (and (inv_main22 var6 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var6 var1)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Int) (var4 Int) (var5 Addr) (var6 Int) (var7 Int) (var8 Heap)) (not (and (inv_main35 var8 var7 var6 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var8 var0)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Int) (var4 Int) (var5 Addr) (var6 Int) (var7 Int) (var8 Heap)) (not (and (inv_main41 var8 var7 var6 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var8 var0)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Int) (var4 Int) (var5 Addr) (var6 Int) (var7 Int) (var8 Heap)) (not (and (inv_main42 var8 var7 var6 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var8 var0)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Int) (var4 Addr) (var5 Int) (var6 Int) (var7 Heap)) (not (and (inv_main44 var7 var6 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var7 var0)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Int) (var4 Addr) (var5 Int) (var6 Int) (var7 Heap)) (not (and (inv_main47 var7 var6 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var7 var4)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Int) (var4 Int) (var5 Heap)) (not (and (inv_main49 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var5 var0)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Int) (var4 Int) (var5 Heap)) (not (and (inv_main50 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var5 var0)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Addr) (var4 Int) (var5 Int) (var6 Heap)) (not (and (inv_main57 var6 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var6 var1)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Int) (var4 Addr) (var5 Int) (var6 Int) (var7 Heap)) (not (and (inv_main58 var7 var6 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var7 var2)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Int) (var4 Addr) (var5 Int) (var6 Int) (var7 Heap)) (not (and (inv_main70 var7 var6 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var7 var0)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Addr) (var4 Int) (var5 Int) (var6 Heap)) (not (inv_main73 var6 var5 var4 var3 var2 var1 var0))))
(check-sat)
