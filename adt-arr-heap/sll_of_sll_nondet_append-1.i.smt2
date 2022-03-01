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
   (node (next Addr) (inner Addr))
  )
))
(declare-fun inv_main11 (Heap Int Int Int Int Addr) Bool)
(declare-fun inv_main26 (Heap Int Int Int Int Addr Int Int Int Addr Int) Bool)
(declare-fun inv_main29 (Heap Int Int Int Int Addr Int Int Int Addr) Bool)
(declare-fun inv_main31 (Heap Int Int Int Int Addr Int Int Int Addr Addr) Bool)
(declare-fun inv_main33 (Heap Int Int Int Int Addr Int Int Int Addr Int Addr) Bool)
(declare-fun inv_main37 (Heap Int Int Int Int Addr Int Int Int Addr Int Addr Addr) Bool)
(declare-fun inv_main40 (Heap Int Int Int Int Addr Int Int Int Addr Int Addr Addr Int) Bool)
(declare-fun inv_main46 (Heap Int Int Int Int Addr Int Int Addr) Bool)
(declare-fun inv_main49 (Heap Int Int Int Int Addr Int Int Addr Addr) Bool)
(declare-fun inv_main5 (Heap Int Int Int Int) Bool)
(declare-fun inv_main51 (Heap Int Int Int Int Addr Int Int Addr Addr) Bool)
(declare-fun inv_main52 (Heap Int Int Int Int Addr Int Int Addr Addr) Bool)
(declare-fun inv_main56 (Heap Int Int Int Int Addr Addr) Bool)
(declare-fun inv_main62 (Heap Int Int Int Int Addr Addr) Bool)
(declare-fun inv_main69 (Heap Int Int Int Int Addr Addr Addr Int) Bool)
(declare-fun inv_main72 (Heap Int Int Int Int Addr Addr Int) Bool)
(declare-fun inv_main8 (Heap Int Int Int Int Addr) Bool)
(declare-fun inv_main84 (Heap Int Int Int Int Addr Addr Addr) Bool)
(declare-fun inv_main85 (Heap Int Int Int Int Addr Addr Addr Addr) Bool)
(declare-fun inv_main88 (Heap Int Int Int Int Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main92 (Heap Int Int Int Int Addr Addr) Bool)
(assert (forall ((var0 Int) (var1 Int) (var2 Heap)) (or (not (= var2 emptyHeap)) (inv_main5 var2 3 5 var1 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Int) (var4 Addr) (var5 Int) (var6 Int) (var7 Int) (var8 Int) (var9 Heap) (var10 Addr) (var11 Int) (var12 Int) (var13 Int) (var14 Addr) (var15 Int) (var16 Int) (var17 Int) (var18 Int) (var19 Heap)) (or (not (and (inv_main29 var19 var18 var17 var16 var15 var14 var13 var12 var11 var10) (and (is-O_node (read var19 var10)) (and (and (and (and (and (and (and (and (and (= var9 (write var19 var10 (O_node (node nullAddr (inner (getnode (read var19 var10))))))) (= var8 var18)) (= var7 var17)) (= var6 var16)) (= var5 var15)) (= var4 var14)) (= var3 var13)) (= var2 var12)) (= var1 var11)) (= var0 var10))))) (inv_main46 var9 var8 var7 var6 var5 var4 var3 var2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Int) (var5 Int) (var6 Int) (var7 Addr) (var8 Int) (var9 Int) (var10 Int) (var11 Int) (var12 Heap) (var13 Addr) (var14 Addr) (var15 Int) (var16 Addr) (var17 Int) (var18 Int) (var19 Int) (var20 Addr) (var21 Int) (var22 Int) (var23 Int) (var24 Int) (var25 Heap)) (or (not (and (inv_main37 var25 var24 var23 var22 var21 var20 var19 var18 var17 var16 var15 var14 var13) (and (is-O_node (read var25 var13)) (and (and (and (and (and (and (and (and (and (and (and (and (= var12 (write var25 var13 (O_node (node var14 (inner (getnode (read var25 var13))))))) (= var11 var24)) (= var10 var23)) (= var9 var22)) (= var8 var21)) (= var7 var20)) (= var6 var19)) (= var5 var18)) (= var4 var17)) (= var3 var16)) (= var2 var15)) (= var1 var14)) (= var0 var13))))) (inv_main33 var12 var11 var10 var9 var8 var7 var6 var5 var4 var3 (+ var2 (- 1)) var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Int) (var4 Addr) (var5 Int) (var6 Int) (var7 Int) (var8 Int) (var9 node) (var10 Heap) (var11 Addr) (var12 Addr) (var13 Int) (var14 Int) (var15 Int) (var16 Int) (var17 Heap)) (or (not (and (inv_main11 var17 var16 var15 var14 var13 var12) (and (and (not (= nullAddr var11)) (and (and (and (and (and (and (and (and (and (= var10 (newHeap (alloc var17 (O_node var9)))) (= var8 var16)) (= var7 var15)) (= var6 var14)) (= var5 var13)) (= var4 var12)) (= var3 5)) (= var2 var14)) (= var1 var14)) (= var11 (newAddr (alloc var17 (O_node var9)))))) (and (not (= var0 0)) (<= 0 (+ (+ 10 (* (- 1) var13)) (- 1))))))) (inv_main33 var10 var8 var7 var6 var5 var4 var3 var2 var1 var11 var1 nullAddr))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Addr) (var6 Int) (var7 Int) (var8 Int) (var9 Int) (var10 Heap)) (or (not (inv_main26 var10 var9 var8 var7 var6 var5 var4 var3 var2 var1 var0)) (inv_main26 var10 var9 var8 var7 var6 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Int) (var4 Addr) (var5 Int) (var6 Int) (var7 Int) (var8 Int) (var9 node) (var10 Heap) (var11 Addr) (var12 Addr) (var13 Int) (var14 Int) (var15 Int) (var16 Int) (var17 Heap)) (or (not (and (inv_main11 var17 var16 var15 var14 var13 var12) (and (and (= nullAddr var11) (and (and (and (and (and (and (and (and (and (= var10 (newHeap (alloc var17 (O_node var9)))) (= var8 var16)) (= var7 var15)) (= var6 var14)) (= var5 var13)) (= var4 var12)) (= var3 5)) (= var2 var14)) (= var1 var14)) (= var11 (newAddr (alloc var17 (O_node var9)))))) (and (not (= var0 0)) (<= 0 (+ (+ 10 (* (- 1) var13)) (- 1))))))) (inv_main26 var10 var8 var7 var6 var5 var4 var3 var2 var1 var11 1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Int) (var8 Int) (var9 Int) (var10 Int) (var11 Int) (var12 Int) (var13 Int) (var14 Int) (var15 Addr) (var16 Heap) (var17 Heap) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Int) (var25 Int) (var26 Int) (var27 Int) (var28 Heap)) (or (not (and (inv_main85 var28 var27 var26 var25 var24 var23 var22 var21 var20) (and (not (= var19 nullAddr)) (and (and (and (= var18 nullAddr) (and (and (and (and (and (and (and (and (and (= var17 (write var16 var15 defObj)) (= var14 var13)) (= var12 var11)) (= var10 var9)) (= var8 var7)) (= var6 var5)) (= var4 var3)) (= var2 var15)) (= var19 var1)) (= var0 var18))) (is-O_node (read var28 var21))) (and (and (and (and (and (and (and (and (and (= var16 var28) (= var13 var27)) (= var11 var26)) (= var9 var25)) (= var7 var24)) (= var5 var23)) (= var3 var22)) (= var15 var21)) (= var1 var20)) (= var18 (inner (getnode (read var28 var21))))))))) (inv_main84 var17 var14 var12 var10 var8 var6 var4 var19))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Int) (var8 Int) (var9 Int) (var10 Int) (var11 Heap) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Int) (var20 Int) (var21 Int) (var22 Int) (var23 Int) (var24 Int) (var25 Int) (var26 Int) (var27 Addr) (var28 Heap) (var29 Heap) (var30 Addr) (var31 Addr) (var32 Addr) (var33 Addr) (var34 Addr) (var35 Addr) (var36 Addr) (var37 Int) (var38 Int) (var39 Int) (var40 Int) (var41 Heap)) (or (not (and (inv_main88 var41 var40 var39 var38 var37 var36 var35 var34 var33 var32) (and (not (= var31 nullAddr)) (and (and (= var30 nullAddr) (and (and (and (and (and (and (and (and (and (= var29 (write var28 var27 defObj)) (= var26 var25)) (= var24 var23)) (= var22 var21)) (= var20 var19)) (= var18 var17)) (= var16 var15)) (= var14 var27)) (= var31 var13)) (= var12 var30))) (and (and (is-O_node (read var41 var32)) (and (and (and (and (and (and (and (and (and (and (= var11 var41) (= var10 var40)) (= var9 var39)) (= var8 var38)) (= var7 var37)) (= var6 var36)) (= var5 var35)) (= var4 var34)) (= var3 var33)) (= var2 var32)) (= var1 (next (getnode (read var41 var32)))))) (and (and (and (and (and (and (and (and (and (and (= var28 (write var11 var2 defObj)) (= var25 var10)) (= var23 var9)) (= var21 var8)) (= var19 var7)) (= var17 var6)) (= var15 var5)) (= var27 var4)) (= var13 var3)) (= var0 var2)) (= var30 var1))))))) (inv_main84 var29 var26 var24 var22 var20 var18 var16 var31))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Heap)) (or (not (and (inv_main56 var6 var5 var4 var3 var2 var1 var0) (and (not (= var1 nullAddr)) (= nullAddr var0)))) (inv_main84 var6 var5 var4 var3 var2 var1 var0 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Heap) (var6 Addr) (var7 Int) (var8 Int) (var9 Int) (var10 Int) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Int) (var15 Int) (var16 Int) (var17 Int) (var18 Heap)) (or (not (and (inv_main69 var18 var17 var16 var15 var14 var13 var12 var11 var10) (and (or (not (= (+ var9 1) var8)) (not (<= 0 (+ (+ var7 (* (- 1) var9)) (- 1))))) (and (or (not (= 3 var9)) (not (= 5 var8))) (and (not (= var9 var8)) (and (= var6 nullAddr) (and (is-O_node (read var18 var11)) (and (and (and (and (and (and (and (and (and (= var5 var18) (= var4 var17)) (= var7 var16)) (= var9 var15)) (= var3 var14)) (= var2 var13)) (= var1 var12)) (= var0 var11)) (= var8 var10)) (= var6 (next (getnode (read var18 var11)))))))))))) (inv_main92 var5 var4 var7 var9 var3 var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Heap) (var5 Addr) (var6 Int) (var7 Int) (var8 Addr) (var9 Addr) (var10 Int) (var11 Int) (var12 Int) (var13 Int) (var14 Heap)) (or (not (and (inv_main62 var14 var13 var12 var11 var10 var9 var8) (and (or (not (= (+ var7 1) 0)) (not (<= 0 (+ (+ var6 (* (- 1) var7)) (- 1))))) (and (not (= var7 0)) (and (and (= var5 nullAddr) (is-O_node (read var14 var8))) (and (and (and (and (and (and (and (= var4 var14) (= var3 var13)) (= var6 var12)) (= var7 var11)) (= var2 var10)) (= var1 var9)) (= var0 var8)) (= var5 (inner (getnode (read var14 var8)))))))))) (inv_main92 var4 var3 var6 var7 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Heap)) (or (not (and (inv_main56 var6 var5 var4 var3 var2 var1 var0) (and (<= 0 (+ (+ var3 (* (- 1) var4)) (- 1))) (not (= nullAddr var0))))) (inv_main92 var6 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Addr) (var5 Int) (var6 Int) (var7 Int) (var8 Int) (var9 Heap)) (or (not (and (inv_main49 var9 var8 var7 var6 var5 var4 var3 var2 var1 var0) (and (is-O_node (read var9 var0)) (not (= (next (getnode (read var9 var0))) nullAddr))))) (inv_main52 var9 var8 var7 var6 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Heap) (var7 Addr) (var8 Int) (var9 Int) (var10 Int) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Int) (var15 Int) (var16 Int) (var17 Int) (var18 Heap)) (or (not (and (inv_main69 var18 var17 var16 var15 var14 var13 var12 var11 var10) (and (= var9 var8) (and (= var7 nullAddr) (and (is-O_node (read var18 var11)) (and (and (and (and (and (and (and (and (and (= var6 var18) (= var5 var17)) (= var4 var16)) (= var9 var15)) (= var3 var14)) (= var2 var13)) (= var1 var12)) (= var0 var11)) (= var8 var10)) (= var7 (next (getnode (read var18 var11)))))))))) (inv_main72 var6 var5 var4 var9 var3 var2 var1 var8))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Heap) (var6 Addr) (var7 Int) (var8 Addr) (var9 Addr) (var10 Int) (var11 Int) (var12 Int) (var13 Int) (var14 Heap)) (or (not (and (inv_main62 var14 var13 var12 var11 var10 var9 var8) (and (= var7 0) (and (and (= var6 nullAddr) (is-O_node (read var14 var8))) (and (and (and (and (and (and (and (= var5 var14) (= var4 var13)) (= var3 var12)) (= var7 var11)) (= var2 var10)) (= var1 var9)) (= var0 var8)) (= var6 (inner (getnode (read var14 var8))))))))) (inv_main72 var5 var4 var3 var7 var2 var1 var0 0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Int) (var4 Int) (var5 Heap)) (or (not (and (inv_main8 var5 var4 var3 var2 var1 var0) (<= 0 (+ var3 (* (- 1) var2))))) (inv_main11 var5 var4 var3 var2 0 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Int) (var11 Int) (var12 Addr) (var13 Int) (var14 Int) (var15 Int) (var16 Int) (var17 Heap)) (or (not (and (inv_main51 var17 var16 var15 var14 var13 var12 var11 var10 var9 var8) (and (is-O_node (read var17 var8)) (and (and (and (and (and (and (and (= var7 (write var17 var8 (O_node (node var9 (inner (getnode (read var17 var8))))))) (= var6 var16)) (= var5 var15)) (= var4 var14)) (= var3 var13)) (= var2 var12)) (= var1 var11)) (= var0 var10))))) (inv_main11 var7 var6 var5 var4 (+ var3 1) var2))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Int) (var11 Int) (var12 Addr) (var13 Int) (var14 Int) (var15 Int) (var16 Int) (var17 Heap)) (or (not (and (inv_main46 var17 var16 var15 var14 var13 var12 var11 var10 var9) (and (and (= nullAddr var8) (is-O_node (read var17 var9))) (and (and (and (and (and (and (and (and (= var7 (write var17 var9 (O_node (node nullAddr (inner (getnode (read var17 var9))))))) (= var6 var16)) (= var5 var15)) (= var4 var14)) (= var3 var13)) (= var8 var12)) (= var2 var11)) (= var1 var10)) (= var0 var9))))) (inv_main11 var7 var6 var5 var4 (+ var3 1) var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Int) (var6 Int) (var7 Int) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Int) (var15 Int) (var16 Int) (var17 Int) (var18 Heap)) (or (not (and (inv_main85 var18 var17 var16 var15 var14 var13 var12 var11 var10) (and (and (not (= var9 nullAddr)) (is-O_node (read var18 var11))) (and (and (and (and (and (and (and (and (and (= var8 var18) (= var7 var17)) (= var6 var16)) (= var5 var15)) (= var4 var14)) (= var3 var13)) (= var2 var12)) (= var1 var11)) (= var0 var10)) (= var9 (inner (getnode (read var18 var11)))))))) (inv_main88 var8 var7 var6 var5 var4 var3 var2 var1 var0 var9))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Int) (var6 Int) (var7 Int) (var8 Int) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Int) (var17 Int) (var18 Int) (var19 Int) (var20 Heap) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Addr) (var25 Addr) (var26 Addr) (var27 Int) (var28 Int) (var29 Int) (var30 Int) (var31 Heap)) (or (not (and (inv_main88 var31 var30 var29 var28 var27 var26 var25 var24 var23 var22) (and (not (= var21 nullAddr)) (and (and (is-O_node (read var31 var22)) (and (and (and (and (and (and (and (and (and (and (= var20 var31) (= var19 var30)) (= var18 var29)) (= var17 var28)) (= var16 var27)) (= var15 var26)) (= var14 var25)) (= var13 var24)) (= var12 var23)) (= var11 var22)) (= var10 (next (getnode (read var31 var22)))))) (and (and (and (and (and (and (and (and (and (and (= var9 (write var20 var11 defObj)) (= var8 var19)) (= var7 var18)) (= var6 var17)) (= var5 var16)) (= var4 var15)) (= var3 var14)) (= var2 var13)) (= var1 var12)) (= var0 var11)) (= var21 var10)))))) (inv_main88 var9 var8 var7 var6 var5 var4 var3 var2 var1 var21))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Addr) (var7 Int) (var8 Int) (var9 Int) (var10 Int) (var11 node) (var12 Heap) (var13 Addr) (var14 Addr) (var15 Int) (var16 Addr) (var17 Int) (var18 Int) (var19 Int) (var20 Addr) (var21 Int) (var22 Int) (var23 Int) (var24 Int) (var25 Heap)) (or (not (and (inv_main33 var25 var24 var23 var22 var21 var20 var19 var18 var17 var16 var15 var14) (and (and (not (= nullAddr var13)) (and (and (and (and (and (and (and (and (and (and (and (and (= var12 (newHeap (alloc var25 (O_node var11)))) (= var10 var24)) (= var9 var23)) (= var8 var22)) (= var7 var21)) (= var6 var20)) (= var5 var19)) (= var4 var18)) (= var3 var17)) (= var2 var16)) (= var1 var15)) (= var0 var14)) (= var13 (newAddr (alloc var25 (O_node var11)))))) (<= 0 (+ var15 (- 1)))))) (inv_main37 var12 var10 var9 var8 var7 var6 var5 var4 var3 var2 var1 var0 var13))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Heap)) (or (not (and (inv_main84 var7 var6 var5 var4 var3 var2 var1 var0) (is-O_node (read var7 var0)))) (inv_main85 var7 var6 var5 var4 var3 var2 var1 var0 (next (getnode (read var7 var0)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Addr) (var7 Int) (var8 Int) (var9 Int) (var10 Int) (var11 Heap)) (or (not (and (inv_main33 var11 var10 var9 var8 var7 var6 var5 var4 var3 var2 var1 var0) (not (<= 0 (+ var1 (- 1)))))) (inv_main31 var11 var10 var9 var8 var7 var6 var5 var4 var3 var2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Addr) (var6 Int) (var7 Int) (var8 Int) (var9 Int) (var10 Heap) (var11 Addr) (var12 Addr) (var13 Int) (var14 Int) (var15 Addr) (var16 Int) (var17 Int) (var18 Int) (var19 Int) (var20 Heap)) (or (not (and (inv_main52 var20 var19 var18 var17 var16 var15 var14 var13 var12 var11) (and (is-O_node (read var20 var11)) (and (and (and (and (and (and (and (and (and (and (= var10 var20) (= var9 var19)) (= var8 var18)) (= var7 var17)) (= var6 var16)) (= var5 var15)) (= var4 var14)) (= var3 var13)) (= var2 var12)) (= var1 var11)) (= var0 (next (getnode (read var20 var11)))))))) (inv_main49 var10 var9 var8 var7 var6 var5 var4 var3 var2 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Int) (var11 Int) (var12 Addr) (var13 Int) (var14 Int) (var15 Int) (var16 Int) (var17 Heap)) (or (not (and (inv_main46 var17 var16 var15 var14 var13 var12 var11 var10 var9) (and (and (not (= nullAddr var8)) (is-O_node (read var17 var9))) (and (and (and (and (and (and (and (and (= var7 (write var17 var9 (O_node (node nullAddr (inner (getnode (read var17 var9))))))) (= var6 var16)) (= var5 var15)) (= var4 var14)) (= var3 var13)) (= var8 var12)) (= var2 var11)) (= var1 var10)) (= var0 var9))))) (inv_main49 var7 var6 var5 var4 var3 var8 var2 var1 var0 var8))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Int) (var4 Int) (var5 Heap) (var6 Int) (var7 Int) (var8 Int) (var9 Int) (var10 Heap)) (or (not (and (inv_main5 var10 var9 var8 var7 var6) (and (and (and (and (and (= var5 var10) (= var4 var9)) (= var3 var8)) (= var2 var7)) (= var1 var6)) (= var0 nullAddr)))) (inv_main8 var5 var4 var3 var4 var1 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Int) (var4 Int) (var5 Heap)) (or (not (and (inv_main11 var5 var4 var3 var2 var1 var0) (not (<= 0 (+ (+ 10 (* (- 1) var1)) (- 1)))))) (inv_main8 var5 var4 var3 (+ var2 1) var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Heap)) (or (not (and (inv_main11 var6 var5 var4 var3 var2 var1) (and (= var0 0) (<= 0 (+ (+ 10 (* (- 1) var2)) (- 1)))))) (inv_main8 var6 var5 var4 (+ var3 1) var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Addr) (var6 Int) (var7 Int) (var8 Int) (var9 Int) (var10 Heap)) (or (not (and (inv_main31 var10 var9 var8 var7 var6 var5 var4 var3 var2 var1 var0) (is-O_node (read var10 var1)))) (inv_main29 (write var10 var1 (O_node (node (next (getnode (read var10 var1))) var0))) var9 var8 var7 var6 var5 var4 var3 var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Heap) (var7 Addr) (var8 Int) (var9 Int) (var10 Int) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Int) (var15 Int) (var16 Int) (var17 Int) (var18 Heap)) (or (not (and (inv_main69 var18 var17 var16 var15 var14 var13 var12 var11 var10) (and (and (= 3 var9) (= 5 var8)) (and (not (= var9 var8)) (and (= var7 nullAddr) (and (is-O_node (read var18 var11)) (and (and (and (and (and (and (and (and (and (= var6 var18) (= var5 var17)) (= var4 var16)) (= var9 var15)) (= var3 var14)) (= var2 var13)) (= var1 var12)) (= var0 var11)) (= var8 var10)) (= var7 (next (getnode (read var18 var11))))))))))) (inv_main56 var6 var5 var4 (+ (+ var9 1) 1) var3 var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Heap) (var6 Addr) (var7 Int) (var8 Int) (var9 Int) (var10 Int) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Int) (var15 Int) (var16 Int) (var17 Int) (var18 Heap)) (or (not (and (inv_main69 var18 var17 var16 var15 var14 var13 var12 var11 var10) (and (and (= (+ var9 1) var8) (<= 0 (+ (+ var7 (* (- 1) var9)) (- 1)))) (and (or (not (= 3 var9)) (not (= 5 var8))) (and (not (= var9 var8)) (and (= var6 nullAddr) (and (is-O_node (read var18 var11)) (and (and (and (and (and (and (and (and (and (= var5 var18) (= var4 var17)) (= var7 var16)) (= var9 var15)) (= var3 var14)) (= var2 var13)) (= var1 var12)) (= var0 var11)) (= var8 var10)) (= var6 (next (getnode (read var18 var11)))))))))))) (inv_main56 var5 var4 var7 (+ var9 1) var3 var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Heap) (var5 Addr) (var6 Int) (var7 Int) (var8 Addr) (var9 Addr) (var10 Int) (var11 Int) (var12 Int) (var13 Int) (var14 Heap)) (or (not (and (inv_main62 var14 var13 var12 var11 var10 var9 var8) (and (and (= (+ var7 1) 0) (<= 0 (+ (+ var6 (* (- 1) var7)) (- 1)))) (and (not (= var7 0)) (and (and (= var5 nullAddr) (is-O_node (read var14 var8))) (and (and (and (and (and (and (and (= var4 var14) (= var3 var13)) (= var6 var12)) (= var7 var11)) (= var2 var10)) (= var1 var9)) (= var0 var8)) (= var5 (inner (getnode (read var14 var8)))))))))) (inv_main56 var4 var3 var6 (+ var7 1) var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Heap) (var8 Addr) (var9 Int) (var10 Addr) (var11 Addr) (var12 Int) (var13 Int) (var14 Int) (var15 Int) (var16 Heap)) (or (not (and (inv_main72 var16 var15 var14 var13 var12 var11 var10 var9) (and (= var8 nullAddr) (and (is-O_node (read var16 var10)) (and (and (and (and (and (and (and (and (= var7 var16) (= var6 var15)) (= var5 var14)) (= var4 var13)) (= var3 var12)) (= var2 var11)) (= var1 var10)) (= var0 var9)) (= var8 (next (getnode (read var16 var10))))))))) (inv_main56 var7 var6 var5 (+ var4 1) var3 var2 var8))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Heap)) (or (not (and (inv_main56 var6 var5 var4 var3 var2 var1 var0) (and (= var0 nullAddr) (and (not (<= 0 (+ (+ var3 (* (- 1) var4)) (- 1)))) (not (= nullAddr var0)))))) (inv_main56 var6 var5 var4 (+ var3 1) var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Int) (var4 Int) (var5 Heap)) (or (not (and (inv_main8 var5 var4 var3 var2 var1 var0) (not (<= 0 (+ var3 (* (- 1) var2)))))) (inv_main56 var5 var4 var3 var4 var1 var0 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Addr) (var5 Int) (var6 Int) (var7 Int) (var8 Int) (var9 Heap)) (or (not (and (inv_main49 var9 var8 var7 var6 var5 var4 var3 var2 var1 var0) (and (is-O_node (read var9 var0)) (= (next (getnode (read var9 var0))) nullAddr)))) (inv_main51 var9 var8 var7 var6 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Addr) (var5 Int) (var6 Int) (var7 Int) (var8 Addr) (var9 Int) (var10 Int) (var11 Int) (var12 Int) (var13 Heap)) (or (not (inv_main40 var13 var12 var11 var10 var9 var8 var7 var6 var5 var4 var3 var2 var1 var0)) (inv_main40 var13 var12 var11 var10 var9 var8 var7 var6 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Addr) (var7 Int) (var8 Int) (var9 Int) (var10 Int) (var11 node) (var12 Heap) (var13 Addr) (var14 Addr) (var15 Int) (var16 Addr) (var17 Int) (var18 Int) (var19 Int) (var20 Addr) (var21 Int) (var22 Int) (var23 Int) (var24 Int) (var25 Heap)) (or (not (and (inv_main33 var25 var24 var23 var22 var21 var20 var19 var18 var17 var16 var15 var14) (and (and (= nullAddr var13) (and (and (and (and (and (and (and (and (and (and (and (and (= var12 (newHeap (alloc var25 (O_node var11)))) (= var10 var24)) (= var9 var23)) (= var8 var22)) (= var7 var21)) (= var6 var20)) (= var5 var19)) (= var4 var18)) (= var3 var17)) (= var2 var16)) (= var1 var15)) (= var0 var14)) (= var13 (newAddr (alloc var25 (O_node var11)))))) (<= 0 (+ var15 (- 1)))))) (inv_main40 var12 var10 var9 var8 var7 var6 var5 var4 var3 var2 var1 var0 var13 1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Heap) (var8 Addr) (var9 Int) (var10 Addr) (var11 Addr) (var12 Int) (var13 Int) (var14 Int) (var15 Int) (var16 Heap)) (or (not (and (inv_main72 var16 var15 var14 var13 var12 var11 var10 var9) (and (not (= var8 nullAddr)) (and (is-O_node (read var16 var10)) (and (and (and (and (and (and (and (and (= var7 var16) (= var6 var15)) (= var5 var14)) (= var4 var13)) (= var3 var12)) (= var2 var11)) (= var1 var10)) (= var0 var9)) (= var8 (next (getnode (read var16 var10))))))))) (inv_main62 var7 var6 var5 var4 var3 var2 var8))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Heap)) (or (not (and (inv_main56 var6 var5 var4 var3 var2 var1 var0) (and (not (= var0 nullAddr)) (and (not (<= 0 (+ (+ var3 (* (- 1) var4)) (- 1)))) (not (= nullAddr var0)))))) (inv_main62 var6 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Int) (var6 Int) (var7 Int) (var8 Heap) (var9 Addr) (var10 Int) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Int) (var15 Int) (var16 Int) (var17 Int) (var18 Heap)) (or (not (and (inv_main69 var18 var17 var16 var15 var14 var13 var12 var11 var10) (and (not (= var9 nullAddr)) (and (is-O_node (read var18 var11)) (and (and (and (and (and (and (and (and (and (= var8 var18) (= var7 var17)) (= var6 var16)) (= var5 var15)) (= var4 var14)) (= var3 var13)) (= var2 var12)) (= var1 var11)) (= var0 var10)) (= var9 (next (getnode (read var18 var11))))))))) (inv_main69 var8 var7 var6 var5 var4 var3 var2 var9 (+ var0 1)))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Int) (var11 Int) (var12 Int) (var13 Int) (var14 Heap)) (or (not (and (inv_main62 var14 var13 var12 var11 var10 var9 var8) (and (and (not (= var7 nullAddr)) (is-O_node (read var14 var8))) (and (and (and (and (and (and (and (= var6 var14) (= var5 var13)) (= var4 var12)) (= var3 var11)) (= var2 var10)) (= var1 var9)) (= var0 var8)) (= var7 (inner (getnode (read var14 var8)))))))) (inv_main69 var6 var5 var4 var3 var2 var1 var0 var7 1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Int) (var5 Int) (var6 Int) (var7 Addr) (var8 Int) (var9 Int) (var10 Int) (var11 Int) (var12 Heap)) (not (and (inv_main37 var12 var11 var10 var9 var8 var7 var6 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var12 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Addr) (var6 Int) (var7 Int) (var8 Int) (var9 Int) (var10 Heap)) (not (and (inv_main31 var10 var9 var8 var7 var6 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var10 var1)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Int) (var4 Addr) (var5 Int) (var6 Int) (var7 Int) (var8 Int) (var9 Heap)) (not (and (inv_main29 var9 var8 var7 var6 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var9 var0)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Addr) (var4 Int) (var5 Int) (var6 Int) (var7 Int) (var8 Heap)) (not (and (inv_main46 var8 var7 var6 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var8 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Addr) (var5 Int) (var6 Int) (var7 Int) (var8 Int) (var9 Heap)) (not (and (inv_main49 var9 var8 var7 var6 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var9 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Addr) (var5 Int) (var6 Int) (var7 Int) (var8 Int) (var9 Heap)) (not (and (inv_main52 var9 var8 var7 var6 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var9 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Addr) (var5 Int) (var6 Int) (var7 Int) (var8 Int) (var9 Heap)) (not (and (inv_main51 var9 var8 var7 var6 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var9 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Heap)) (not (and (inv_main62 var6 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var6 var0)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Int) (var6 Int) (var7 Int) (var8 Heap)) (not (and (inv_main69 var8 var7 var6 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var8 var1)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Heap)) (not (and (inv_main72 var7 var6 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var7 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Heap)) (not (and (inv_main84 var7 var6 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var7 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Int) (var6 Int) (var7 Int) (var8 Heap)) (not (and (inv_main85 var8 var7 var6 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var8 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Int) (var6 Int) (var7 Int) (var8 Int) (var9 Heap)) (not (and (inv_main88 var9 var8 var7 var6 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var9 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Heap)) (not (inv_main92 var6 var5 var4 var3 var2 var1 var0))))
(check-sat)
