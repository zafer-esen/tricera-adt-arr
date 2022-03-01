(set-logic HORN)
(set-info :source |
    Benchmark: C_VC
    Output by Princess (http://www.philipp.ruemmer.org/princess.shtml)
|)
(set-info :status unsat)
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
   (node (h Int) (n Addr))
  )
))
(declare-fun inv_main16 (Heap Int Addr Addr Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main17 (Heap Int Addr Addr Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main21 (Heap Int Addr Addr Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main22 (Heap Int Addr Addr Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main27 (Heap Int Addr Addr Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main3 (Heap Int) Bool)
(declare-fun inv_main30 (Heap Int Addr Addr Addr Addr Addr Addr Addr Int) Bool)
(declare-fun inv_main33 (Heap Int Addr Addr Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main35 (Heap Int Addr Addr Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main43 (Heap Int Addr Addr Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main47 (Heap Int Addr Addr Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main50 (Heap Int Addr Addr Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main51 (Heap Int Addr Addr Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main58 (Heap Int Addr Addr Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main59 (Heap Int Addr Addr Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main66 (Heap Int Addr Addr Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main67 (Heap Int Addr Addr Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main72 (Heap Int Addr Addr Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main8 (Heap Int Addr Int) Bool)
(assert (forall ((var0 Heap)) (or (not (= var0 emptyHeap)) (inv_main3 var0 1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Int) (var8 Heap) (var9 Int) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Int) (var18 Heap)) (or (not (and (inv_main43 var18 var17 var16 var15 var14 var13 var12 var11 var10) (and (and (not (= var9 3)) (is-O_node (read var18 var10))) (and (and (and (and (and (and (and (and (and (= var8 var18) (= var7 var17)) (= var6 var16)) (= var5 var15)) (= var4 var14)) (= var3 var13)) (= var2 var12)) (= var1 var11)) (= var0 var10)) (= var9 (h (getnode (read var18 var10)))))))) (inv_main47 var8 var7 var6 var0 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Int) (var8 Heap)) (or (not (and (inv_main27 var8 var7 var6 var5 var4 var3 var2 var1 var0) (is-O_node (read var8 var0)))) (inv_main33 (write var8 var0 (O_node (node (h (getnode (read var8 var0))) var5))) var7 var6 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Int) (var8 Heap) (var9 Int) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Int) (var18 Heap)) (or (not (and (inv_main58 var18 var17 var16 var15 var14 var13 var12 var11 var10) (and (and (not (= var9 2)) (is-O_node (read var18 var10))) (and (and (and (and (and (and (and (and (and (= var8 var18) (= var7 var17)) (= var6 var16)) (= var5 var15)) (= var4 var14)) (= var3 var13)) (= var2 var12)) (= var1 var11)) (= var0 var10)) (= var9 (h (getnode (read var18 var10)))))))) (inv_main72 var8 var7 var6 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Int) (var8 Heap) (var9 Int) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Int) (var18 Heap)) (or (not (and (inv_main66 var18 var17 var16 var15 var14 var13 var12 var11 var10) (and (and (not (= var9 1)) (is-O_node (read var18 var10))) (and (and (and (and (and (and (and (and (and (= var8 var18) (= var7 var17)) (= var6 var16)) (= var5 var15)) (= var4 var14)) (= var3 var13)) (= var2 var12)) (= var1 var11)) (= var0 var10)) (= var9 (h (getnode (read var18 var10)))))))) (inv_main72 var8 var7 var6 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Int) (var9 Heap)) (or (not (and (inv_main16 var9 var8 var7 var6 var5 var4 var3 var2 var1) (= var0 0))) (inv_main17 var9 var8 var7 var6 var5 var4 var3 var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Int) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Int) (var18 Heap)) (or (not (and (inv_main33 var18 var17 var16 var15 var14 var13 var12 var11 var10) (and (is-O_node (read var18 var10)) (and (and (and (and (and (and (and (and (and (= var9 var18) (= var8 var17)) (= var7 var16)) (= var6 var15)) (= var5 var14)) (= var4 var13)) (= var3 var12)) (= var2 var11)) (= var1 var10)) (= var0 (n (getnode (read var18 var10)))))))) (inv_main16 var9 var8 var7 var6 var5 var4 var3 var2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Int) (var6 node) (var7 Heap) (var8 Addr) (var9 Int) (var10 Heap)) (or (not (and (inv_main3 var10 var9) (and (not (= var8 nullAddr)) (and (and (= var7 (newHeap (alloc var10 (O_node var6)))) (= var5 var9)) (= var8 (newAddr (alloc var10 (O_node var6)))))))) (inv_main16 var7 var5 var8 var4 var3 var2 var1 var0 var8))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Heap)) (or (not (inv_main8 var3 var2 var1 var0)) (inv_main8 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 node) (var2 Heap) (var3 Addr) (var4 Int) (var5 Heap)) (or (not (and (inv_main3 var5 var4) (and (= var3 nullAddr) (and (and (= var2 (newHeap (alloc var5 (O_node var1)))) (= var0 var4)) (= var3 (newAddr (alloc var5 (O_node var1)))))))) (inv_main8 var2 var0 var3 1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Int) (var9 Heap)) (or (not (inv_main30 var9 var8 var7 var6 var5 var4 var3 var2 var1 var0)) (inv_main30 var9 var8 var7 var6 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Int) (var16 node) (var17 Heap) (var18 Heap) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Addr) (var25 Addr) (var26 Addr) (var27 Int) (var28 Heap)) (or (not (and (inv_main21 var28 var27 var26 var25 var24 var23 var22 var21 var20) (and (and (= var19 nullAddr) (and (and (and (and (and (and (and (and (and (= var18 (newHeap (alloc var17 (O_node var16)))) (= var15 0)) (= var14 var13)) (= var12 var11)) (= var10 var9)) (= var8 var7)) (= var6 var5)) (= var4 var3)) (= var2 var1)) (= var19 (newAddr (alloc var17 (O_node var16)))))) (and (is-O_node (read var28 var20)) (and (and (and (and (and (and (and (and (= var17 (write var28 var20 (O_node (node 1 (n (getnode (read var28 var20))))))) (= var0 var27)) (= var13 var26)) (= var11 var25)) (= var9 var24)) (= var7 var23)) (= var5 var22)) (= var3 var21)) (= var1 var20)))))) (inv_main30 var18 var15 var14 var19 var10 var8 var6 var4 var2 1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Int) (var16 node) (var17 Heap) (var18 Heap) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Addr) (var25 Addr) (var26 Addr) (var27 Int) (var28 Heap)) (or (not (and (inv_main22 var28 var27 var26 var25 var24 var23 var22 var21 var20) (and (and (= var19 nullAddr) (and (and (and (and (and (and (and (and (and (= var18 (newHeap (alloc var17 (O_node var16)))) (= var15 1)) (= var14 var13)) (= var12 var11)) (= var10 var9)) (= var8 var7)) (= var6 var5)) (= var4 var3)) (= var2 var1)) (= var19 (newAddr (alloc var17 (O_node var16)))))) (and (is-O_node (read var28 var20)) (and (and (and (and (and (and (and (and (= var17 (write var28 var20 (O_node (node 2 (n (getnode (read var28 var20))))))) (= var0 var27)) (= var13 var26)) (= var11 var25)) (= var9 var24)) (= var7 var23)) (= var5 var22)) (= var3 var21)) (= var1 var20)))))) (inv_main30 var18 var15 var14 var19 var10 var8 var6 var4 var2 1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Int) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Int) (var18 Heap)) (or (not (and (inv_main59 var18 var17 var16 var15 var14 var13 var12 var11 var10) (and (not (= var9 nullAddr)) (and (is-O_node (read var18 var10)) (and (and (and (and (and (and (and (and (and (= var8 var18) (= var7 var17)) (= var6 var16)) (= var5 var15)) (= var4 var14)) (= var3 var13)) (= var2 var12)) (= var1 var11)) (= var0 var10)) (= var9 (n (getnode (read var18 var10))))))))) (inv_main58 var8 var7 var6 var5 var4 var3 var2 var1 var9))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Int) (var7 Heap) (var8 Int) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Int) (var18 Heap)) (or (not (and (inv_main43 var18 var17 var16 var15 var14 var13 var12 var11 var10) (and (not (= var9 nullAddr)) (and (and (= var8 3) (is-O_node (read var18 var10))) (and (and (and (and (and (and (and (and (and (= var7 var18) (= var6 var17)) (= var5 var16)) (= var4 var15)) (= var9 var14)) (= var3 var13)) (= var2 var12)) (= var1 var11)) (= var0 var10)) (= var8 (h (getnode (read var18 var10))))))))) (inv_main58 var7 var6 var5 var4 var9 var3 var2 var1 var9))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Int) (var9 Heap)) (or (not (and (inv_main16 var9 var8 var7 var6 var5 var4 var3 var2 var1) (and (= var8 0) (not (= var0 0))))) (inv_main22 var9 var8 var7 var6 var5 var4 var3 var2 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Int) (var16 node) (var17 Heap) (var18 Heap) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Addr) (var25 Addr) (var26 Addr) (var27 Int) (var28 Heap)) (or (not (and (inv_main21 var28 var27 var26 var25 var24 var23 var22 var21 var20) (and (and (not (= var19 nullAddr)) (and (and (and (and (and (and (and (and (and (= var18 (newHeap (alloc var17 (O_node var16)))) (= var15 0)) (= var14 var13)) (= var12 var11)) (= var10 var9)) (= var8 var7)) (= var6 var5)) (= var4 var3)) (= var2 var1)) (= var19 (newAddr (alloc var17 (O_node var16)))))) (and (is-O_node (read var28 var20)) (and (and (and (and (and (and (and (and (= var17 (write var28 var20 (O_node (node 1 (n (getnode (read var28 var20))))))) (= var0 var27)) (= var13 var26)) (= var11 var25)) (= var9 var24)) (= var7 var23)) (= var5 var22)) (= var3 var21)) (= var1 var20)))))) (inv_main27 var18 var15 var14 var19 var10 var8 var6 var4 var2))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Int) (var16 node) (var17 Heap) (var18 Heap) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Addr) (var25 Addr) (var26 Addr) (var27 Int) (var28 Heap)) (or (not (and (inv_main22 var28 var27 var26 var25 var24 var23 var22 var21 var20) (and (and (not (= var19 nullAddr)) (and (and (and (and (and (and (and (and (and (= var18 (newHeap (alloc var17 (O_node var16)))) (= var15 1)) (= var14 var13)) (= var12 var11)) (= var10 var9)) (= var8 var7)) (= var6 var5)) (= var4 var3)) (= var2 var1)) (= var19 (newAddr (alloc var17 (O_node var16)))))) (and (is-O_node (read var28 var20)) (and (and (and (and (and (and (and (and (= var17 (write var28 var20 (O_node (node 2 (n (getnode (read var28 var20))))))) (= var0 var27)) (= var13 var26)) (= var11 var25)) (= var9 var24)) (= var7 var23)) (= var5 var22)) (= var3 var21)) (= var1 var20)))))) (inv_main27 var18 var15 var14 var19 var10 var8 var6 var4 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap) (var9 Int) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Int) (var18 Heap)) (or (not (and (inv_main47 var18 var17 var16 var15 var14 var13 var12 var11 var10) (and (not (= var9 0)) (and (is-O_node (read var18 var10)) (and (and (and (and (and (and (and (and (and (= var8 var18) (= var9 var17)) (= var7 var16)) (= var6 var15)) (= var5 var14)) (= var4 var13)) (= var3 var12)) (= var2 var11)) (= var1 var10)) (= var0 (n (getnode (read var18 var10))))))))) (inv_main50 var8 var9 var7 var6 var5 var4 var3 var2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Int) (var8 Heap)) (or (not (and (inv_main17 var8 var7 var6 var5 var4 var3 var2 var1 var0) (is-O_node (read var8 var0)))) (inv_main35 (write var8 var0 (O_node (node 3 (n (getnode (read var8 var0)))))) var7 var6 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Int) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Int) (var18 Heap)) (or (not (and (inv_main67 var18 var17 var16 var15 var14 var13 var12 var11 var10) (and (not (= var9 nullAddr)) (and (is-O_node (read var18 var10)) (and (and (and (and (and (and (and (and (and (= var8 var18) (= var7 var17)) (= var6 var16)) (= var5 var15)) (= var4 var14)) (= var3 var13)) (= var2 var12)) (= var1 var11)) (= var0 var10)) (= var9 (n (getnode (read var18 var10))))))))) (inv_main66 var8 var7 var6 var5 var4 var3 var2 var1 var9))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Int) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Int) (var18 Heap)) (or (not (and (inv_main59 var18 var17 var16 var15 var14 var13 var12 var11 var10) (and (not (= var9 nullAddr)) (and (= var8 nullAddr) (and (is-O_node (read var18 var10)) (and (and (and (and (and (and (and (and (and (= var7 var18) (= var6 var17)) (= var5 var16)) (= var4 var15)) (= var3 var14)) (= var9 var13)) (= var2 var12)) (= var1 var11)) (= var0 var10)) (= var8 (n (getnode (read var18 var10)))))))))) (inv_main66 var7 var6 var5 var4 var3 var9 var2 var1 var9))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Int) (var6 Heap) (var7 Int) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Int) (var18 Heap)) (or (not (and (inv_main43 var18 var17 var16 var15 var14 var13 var12 var11 var10) (and (not (= var9 nullAddr)) (and (= var8 nullAddr) (and (and (= var7 3) (is-O_node (read var18 var10))) (and (and (and (and (and (and (and (and (and (= var6 var18) (= var5 var17)) (= var4 var16)) (= var3 var15)) (= var8 var14)) (= var9 var13)) (= var2 var12)) (= var1 var11)) (= var0 var10)) (= var7 (h (getnode (read var18 var10)))))))))) (inv_main66 var6 var5 var4 var3 var8 var9 var2 var1 var9))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Int) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Int) (var17 Heap) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Addr) (var25 Int) (var26 Heap) (var27 Int) (var28 Addr) (var29 Addr) (var30 Addr) (var31 Addr) (var32 Addr) (var33 Addr) (var34 Addr) (var35 Int) (var36 Heap)) (or (not (and (inv_main35 var36 var35 var34 var33 var32 var31 var30 var29 var28) (and (and (and (and (not (= var27 3)) (is-O_node (read var36 var34))) (and (and (and (and (and (and (and (and (and (= var26 var36) (= var25 var35)) (= var24 var34)) (= var23 var33)) (= var22 var32)) (= var21 var31)) (= var20 var30)) (= var19 var29)) (= var18 var28)) (= var27 (h (getnode (read var36 var34)))))) (and (and (and (and (and (and (and (and (= var17 var26) (= var16 1)) (= var15 var24)) (= var14 var23)) (= var13 nullAddr)) (= var12 var21)) (= var11 var20)) (= var10 var19)) (= var9 var18))) (and (and (and (and (and (and (and (and (= var8 var17) (= var7 var16)) (= var6 var15)) (= var5 var14)) (= var4 var13)) (= var3 nullAddr)) (= var2 var11)) (= var1 var10)) (= var0 var9))))) (inv_main43 var8 var7 var6 var5 var4 var3 var2 var1 var6))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Int) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Int) (var17 Heap)) (or (not (and (inv_main50 var17 var16 var15 var14 var13 var12 var11 var10 var9) (and (is-O_node (read var17 var14)) (and (and (and (and (and (and (and (and (= var8 (write var17 var14 (O_node (node (h (getnode (read var17 var14))) var13)))) (= var7 var16)) (= var6 var15)) (= var5 var14)) (= var4 var13)) (= var3 var12)) (= var2 var11)) (= var1 var10)) (= var0 var9))))) (inv_main43 var8 0 var6 var5 var5 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Int) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Int) (var17 Heap)) (or (not (and (inv_main51 var17 var16 var15 var14 var13 var12 var11 var10 var9) (and (is-O_node (read var17 var14)) (and (and (and (and (and (and (and (and (= var8 (write var17 var14 (O_node (node (h (getnode (read var17 var14))) var12)))) (= var7 var16)) (= var6 var15)) (= var5 var14)) (= var4 var13)) (= var3 var12)) (= var2 var11)) (= var1 var10)) (= var0 var9))))) (inv_main43 var8 1 var6 var5 var4 var5 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Int) (var9 Heap)) (or (not (and (inv_main16 var9 var8 var7 var6 var5 var4 var3 var2 var1) (and (not (= var8 0)) (not (= var0 0))))) (inv_main21 var9 var8 var7 var6 var5 var4 var3 var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Int) (var8 Heap) (var9 Int) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Int) (var18 Heap)) (or (not (and (inv_main66 var18 var17 var16 var15 var14 var13 var12 var11 var10) (and (and (= var9 1) (is-O_node (read var18 var10))) (and (and (and (and (and (and (and (and (and (= var8 var18) (= var7 var17)) (= var6 var16)) (= var5 var15)) (= var4 var14)) (= var3 var13)) (= var2 var12)) (= var1 var11)) (= var0 var10)) (= var9 (h (getnode (read var18 var10)))))))) (inv_main67 var8 var7 var6 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap) (var9 Int) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Int) (var18 Heap)) (or (not (and (inv_main47 var18 var17 var16 var15 var14 var13 var12 var11 var10) (and (= var9 0) (and (is-O_node (read var18 var10)) (and (and (and (and (and (and (and (and (and (= var8 var18) (= var9 var17)) (= var7 var16)) (= var6 var15)) (= var5 var14)) (= var4 var13)) (= var3 var12)) (= var2 var11)) (= var1 var10)) (= var0 (n (getnode (read var18 var10))))))))) (inv_main51 var8 var9 var7 var6 var5 var4 var3 var2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Int) (var8 Heap) (var9 Int) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Int) (var18 Heap)) (or (not (and (inv_main58 var18 var17 var16 var15 var14 var13 var12 var11 var10) (and (and (= var9 2) (is-O_node (read var18 var10))) (and (and (and (and (and (and (and (and (and (= var8 var18) (= var7 var17)) (= var6 var16)) (= var5 var15)) (= var4 var14)) (= var3 var13)) (= var2 var12)) (= var1 var11)) (= var0 var10)) (= var9 (h (getnode (read var18 var10)))))))) (inv_main59 var8 var7 var6 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Int) (var8 Heap)) (not (and (inv_main21 var8 var7 var6 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var8 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Int) (var8 Heap)) (not (and (inv_main22 var8 var7 var6 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var8 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Int) (var8 Heap)) (not (and (inv_main27 var8 var7 var6 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var8 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Int) (var8 Heap)) (not (and (inv_main33 var8 var7 var6 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var8 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Int) (var8 Heap)) (not (and (inv_main17 var8 var7 var6 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var8 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Int) (var8 Heap)) (not (and (inv_main35 var8 var7 var6 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var8 var6)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Int) (var8 Heap)) (not (and (inv_main43 var8 var7 var6 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var8 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Int) (var8 Heap)) (not (and (inv_main47 var8 var7 var6 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var8 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Int) (var8 Heap)) (not (and (inv_main50 var8 var7 var6 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var8 var5)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Int) (var8 Heap)) (not (and (inv_main51 var8 var7 var6 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var8 var5)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Int) (var8 Heap)) (not (and (inv_main58 var8 var7 var6 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var8 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Int) (var8 Heap)) (not (and (inv_main59 var8 var7 var6 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var8 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Int) (var8 Heap)) (not (and (inv_main66 var8 var7 var6 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var8 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Int) (var8 Heap)) (not (and (inv_main67 var8 var7 var6 var5 var4 var3 var2 var1 var0) (not (is-O_node (read var8 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Int) (var8 Heap)) (not (inv_main72 var8 var7 var6 var5 var4 var3 var2 var1 var0))))
(check-sat)
