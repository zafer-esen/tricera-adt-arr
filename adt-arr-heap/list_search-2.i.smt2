(set-logic HORN)
(set-info :source |
    Benchmark: C_VC
    Output by Princess (http://www.philipp.ruemmer.org/princess.shtml)
|)
(set-info :status sat)
(declare-heap Heap Addr HeapObject
 defObj
 ((HeapObject 0) (list 0)) (
  (
   (O_Int (getInt Int))
   (O_UInt (getUInt Int))
   (O_Addr (getAddr Addr))
   (O_list (getlist list))
   (defObj)
  )
  (
   (list (key Int) (next Addr))
  )
))
(declare-fun inv_main100 (Heap Int Addr Int Addr Addr) Bool)
(declare-fun inv_main13 (Heap Int Addr Int Addr Addr Addr Int) Bool)
(declare-fun inv_main14 (Heap Int Addr Int Addr Addr Addr Int) Bool)
(declare-fun inv_main16 (Heap Int Addr Int Addr Addr Addr Int) Bool)
(declare-fun inv_main18 (Heap Int Addr Int Addr Addr Addr Int Addr) Bool)
(declare-fun inv_main27 (Heap Int Addr Int Addr Addr Addr Int) Bool)
(declare-fun inv_main28 (Heap Int Addr Int Addr Addr Addr Int) Bool)
(declare-fun inv_main30 (Heap Int Addr Int Addr Addr Addr Int) Bool)
(declare-fun inv_main32 (Heap Int Addr Int Addr Addr Addr Int Addr) Bool)
(declare-fun inv_main41 (Heap Int Addr Int Addr Addr Addr Int) Bool)
(declare-fun inv_main42 (Heap Int Addr Int Addr Addr Addr Int) Bool)
(declare-fun inv_main44 (Heap Int Addr Int Addr Addr Addr Int) Bool)
(declare-fun inv_main46 (Heap Int Addr Int Addr Addr Addr Int Addr) Bool)
(declare-fun inv_main5 (Heap Int Addr Int Addr Addr) Bool)
(declare-fun inv_main55 (Heap Int Addr Int Addr Addr Addr Int) Bool)
(declare-fun inv_main56 (Heap Int Addr Int Addr Addr Addr Int) Bool)
(declare-fun inv_main58 (Heap Int Addr Int Addr Addr Addr Int) Bool)
(declare-fun inv_main60 (Heap Int Addr Int Addr Addr Addr Int Addr) Bool)
(declare-fun inv_main62 (Heap Int Addr Int Addr Addr) Bool)
(declare-fun inv_main65 (Heap Int Addr Int Addr Addr) Bool)
(declare-fun inv_main67 (Heap Int Addr Int Addr Addr) Bool)
(declare-fun inv_main71 (Heap Int Addr Int Addr Addr Addr Int) Bool)
(declare-fun inv_main74 (Heap Int Addr Int Addr Addr Addr Int) Bool)
(declare-fun inv_main86 (Heap Int Addr Int Addr Addr Addr Addr) Bool)
(declare-fun inv_main87 (Heap Int Addr Int Addr Addr Addr Addr) Bool)
(declare-fun inv_main88 (Heap Int Addr Int Addr Addr Addr Addr) Bool)
(declare-fun inv_main90 (Heap Int Addr Int Addr Addr Addr Addr) Bool)
(declare-fun inv_main95 (Heap Int Addr Int Addr Addr Addr Addr Addr) Bool)
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Int) (var4 Heap)) (or (not (and (and (= var4 emptyHeap) (= var3 0)) (= var2 nullAddr))) (inv_main5 var4 var3 var2 var1 0 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Addr) (var6 Int) (var7 Heap) (var8 Int) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Int) (var13 Addr) (var14 Int) (var15 Heap)) (or (not (and (inv_main28 var15 var14 var13 var12 var11 var10 var9 var8) (and (is-O_list (read var15 var9)) (and (and (and (and (and (and (and (= var7 (write var15 var9 (O_list (list var8 (next (getlist (read var15 var9))))))) (= var6 var14)) (= var5 var13)) (= var4 var12)) (= var3 var11)) (= var2 var10)) (= var1 var9)) (= var0 var8))))) (inv_main32 var7 var6 var5 var4 var3 var2 var1 var0 var5))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Int) (var10 Int) (var11 Addr) (var12 Int) (var13 Int) (var14 list) (var15 Heap) (var16 Heap) (var17 Addr) (var18 Int) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Int) (var23 Addr) (var24 Int) (var25 Heap)) (or (not (and (inv_main30 var25 var24 var23 var22 var21 var20 var19 var18) (and (and (not (= var17 nullAddr)) (and (and (and (and (and (and (and (and (= var16 (newHeap (alloc var15 (O_list var14)))) (= var13 var12)) (= var17 var11)) (= var10 var9)) (= var8 var7)) (= var6 var5)) (= var4 var7)) (= var3 1)) (= var2 (newAddr (alloc var15 (O_list var14)))))) (and (is-O_list (read var25 var19)) (and (and (and (and (and (and (and (= var15 (write var25 var19 (O_list (list (key (getlist (read var25 var19))) nullAddr)))) (= var12 var24)) (= var1 var23)) (= var9 var22)) (= var7 var21)) (= var5 var20)) (= var11 var19)) (= var0 var18)))))) (inv_main42 var16 var13 var17 var10 var8 var6 var2 var3))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Int) (var10 Int) (var11 Addr) (var12 Int) (var13 Int) (var14 list) (var15 Heap) (var16 Heap) (var17 Addr) (var18 Addr) (var19 Int) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Int) (var24 Addr) (var25 Int) (var26 Heap)) (or (not (and (inv_main32 var26 var25 var24 var23 var22 var21 var20 var19 var18) (and (and (not (= var17 nullAddr)) (and (and (and (and (and (and (and (and (= var16 (newHeap (alloc var15 (O_list var14)))) (= var13 var12)) (= var17 var11)) (= var10 var9)) (= var8 var7)) (= var6 var5)) (= var4 var7)) (= var3 1)) (= var2 (newAddr (alloc var15 (O_list var14)))))) (and (is-O_list (read var26 var20)) (and (and (and (and (and (and (and (= var15 (write var26 var20 (O_list (list (key (getlist (read var26 var20))) var18)))) (= var12 var25)) (= var1 var24)) (= var9 var23)) (= var7 var22)) (= var5 var21)) (= var11 var20)) (= var0 var19)))))) (inv_main42 var16 var13 var17 var10 var8 var6 var2 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Addr) (var5 Int) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Int) (var14 Addr) (var15 Int) (var16 Heap)) (or (not (and (inv_main87 var16 var15 var14 var13 var12 var11 var10 var9) (and (and (= var8 var7) (is-O_list (read var16 var9))) (and (and (and (and (and (and (and (and (= var6 var16) (= var5 var15)) (= var4 var14)) (= var3 var13)) (= var2 var12)) (= var1 var11)) (= var7 var10)) (= var0 var9)) (= var8 (next (getlist (read var16 var9)))))))) (inv_main86 var6 var5 var4 var3 var2 var1 var7 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Int) (var6 Addr) (var7 Int) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Int) (var14 Addr) (var15 Int) (var16 Heap)) (or (not (and (inv_main88 var16 var15 var14 var13 var12 var11 var10 var9) (and (is-O_list (read var16 var10)) (and (and (and (and (and (and (and (and (= var8 var16) (= var7 var15)) (= var6 var14)) (= var5 var13)) (= var4 var12)) (= var3 var11)) (= var2 var10)) (= var1 var9)) (= var0 (next (getlist (read var16 var10)))))))) (inv_main86 var8 var7 var0 var5 var4 var3 var2 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Int) (var10 Int) (var11 Addr) (var12 Int) (var13 Int) (var14 list) (var15 Heap) (var16 Heap) (var17 Addr) (var18 Int) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Int) (var23 Addr) (var24 Int) (var25 Heap)) (or (not (and (inv_main44 var25 var24 var23 var22 var21 var20 var19 var18) (and (and (not (= var17 nullAddr)) (and (and (and (and (and (and (and (and (= var16 (newHeap (alloc var15 (O_list var14)))) (= var13 var12)) (= var17 var11)) (= var10 var9)) (= var8 var7)) (= var6 var5)) (= var4 var7)) (= var3 3)) (= var2 (newAddr (alloc var15 (O_list var14)))))) (and (is-O_list (read var25 var19)) (and (and (and (and (and (and (and (= var15 (write var25 var19 (O_list (list (key (getlist (read var25 var19))) nullAddr)))) (= var12 var24)) (= var1 var23)) (= var9 var22)) (= var7 var21)) (= var5 var20)) (= var11 var19)) (= var0 var18)))))) (inv_main56 var16 var13 var17 var10 var8 var6 var2 var3))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Int) (var10 Int) (var11 Addr) (var12 Int) (var13 Int) (var14 list) (var15 Heap) (var16 Heap) (var17 Addr) (var18 Addr) (var19 Int) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Int) (var24 Addr) (var25 Int) (var26 Heap)) (or (not (and (inv_main46 var26 var25 var24 var23 var22 var21 var20 var19 var18) (and (and (not (= var17 nullAddr)) (and (and (and (and (and (and (and (and (= var16 (newHeap (alloc var15 (O_list var14)))) (= var13 var12)) (= var17 var11)) (= var10 var9)) (= var8 var7)) (= var6 var5)) (= var4 var7)) (= var3 3)) (= var2 (newAddr (alloc var15 (O_list var14)))))) (and (is-O_list (read var26 var20)) (and (and (and (and (and (and (and (= var15 (write var26 var20 (O_list (list (key (getlist (read var26 var20))) var18)))) (= var12 var25)) (= var1 var24)) (= var9 var23)) (= var7 var22)) (= var5 var21)) (= var11 var20)) (= var0 var19)))))) (inv_main56 var16 var13 var17 var10 var8 var6 var2 var3))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Int) (var6 Addr) (var7 Int) (var8 Heap) (var9 Int) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Int) (var14 Addr) (var15 Int) (var16 Heap)) (or (not (and (inv_main74 var16 var15 var14 var13 var12 var11 var10 var9) (and (is-O_list (read var16 var10)) (and (and (and (and (and (and (and (and (= var8 var16) (= var7 var15)) (= var6 var14)) (= var5 var13)) (= var4 var12)) (= var3 var11)) (= var2 var10)) (= var1 var9)) (= var0 (next (getlist (read var16 var10)))))))) (inv_main71 var8 var7 var6 var5 var4 var3 var0 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Int) (var5 Heap)) (or (not (and (inv_main62 var5 var4 var3 var2 var1 var0) (= var1 nullAddr))) (inv_main71 var5 var4 var3 var2 var1 var0 var3 2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Int) (var5 Heap)) (or (not (and (inv_main67 var5 var4 var3 var2 var1 var0) (and (= var3 var0) (is-O_list (read var5 var0))))) (inv_main88 var5 var4 var3 var2 var1 var0 var0 var3))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Addr) (var6 Int) (var7 Heap)) (or (not (and (inv_main41 var7 var6 var5 var4 var3 var2 var1 var0) (is-O_list (read var7 var1)))) (inv_main44 (write var7 var1 (O_list (list var0 (next (getlist (read var7 var1)))))) var6 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Addr) (var6 Int) (var7 Heap)) (or (not (and (inv_main71 var7 var6 var5 var4 var3 var2 var1 var0) (= var1 nullAddr))) (inv_main67 var7 var6 var5 var4 var3 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Addr) (var6 Int) (var7 Heap) (var8 Int) (var9 Int) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Int) (var14 Addr) (var15 Int) (var16 Heap) (var17 Int) (var18 Int) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Int) (var23 Addr) (var24 Int) (var25 Heap)) (or (not (and (inv_main71 var25 var24 var23 var22 var21 var20 var19 var18) (and (and (= var17 0) (and (and (not (= var19 nullAddr)) (is-O_list (read var25 var19))) (and (and (and (and (and (and (and (and (= var16 var25) (= var15 var24)) (= var14 var23)) (= var13 var22)) (= var12 var21)) (= var11 var20)) (= var10 var19)) (= var9 var18)) (= var8 (key (getlist (read var25 var19))))))) (and (and (and (and (and (and (and (and (= var7 var16) (= var6 var15)) (= var5 var14)) (= var4 var13)) (= var3 var12)) (= var2 var11)) (= var1 var10)) (= var0 var9)) (or (and (not (= var8 var9)) (= var17 1)) (and (= var8 var9) (= var17 0))))))) (inv_main67 var7 var6 var5 var4 var3 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Addr) (var6 Int) (var7 Heap) (var8 Int) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Int) (var13 Addr) (var14 Int) (var15 Heap)) (or (not (and (inv_main56 var15 var14 var13 var12 var11 var10 var9 var8) (and (is-O_list (read var15 var9)) (and (and (and (and (and (and (and (= var7 (write var15 var9 (O_list (list var8 (next (getlist (read var15 var9))))))) (= var6 var14)) (= var5 var13)) (= var4 var12)) (= var3 var11)) (= var2 var10)) (= var1 var9)) (= var0 var8))))) (inv_main60 var7 var6 var5 var4 var3 var2 var1 var0 var5))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Addr) (var6 Int) (var7 Heap)) (or (not (and (inv_main86 var7 var6 var5 var4 var3 var2 var1 var0) (is-O_list (read var7 var1)))) (inv_main95 var7 var6 var5 var4 var3 var2 var1 var0 (next (getlist (read var7 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Addr) (var5 Int) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Int) (var14 Addr) (var15 Int) (var16 Heap)) (or (not (and (inv_main87 var16 var15 var14 var13 var12 var11 var10 var9) (and (and (not (= var8 var7)) (is-O_list (read var16 var9))) (and (and (and (and (and (and (and (and (= var6 var16) (= var5 var15)) (= var4 var14)) (= var3 var13)) (= var2 var12)) (= var1 var11)) (= var7 var10)) (= var0 var9)) (= var8 (next (getlist (read var16 var9)))))))) (inv_main90 var6 var5 var4 var3 var2 var1 var7 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Addr) (var6 Int) (var7 Heap) (var8 Int) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Int) (var13 Addr) (var14 Int) (var15 Heap)) (or (not (and (inv_main14 var15 var14 var13 var12 var11 var10 var9 var8) (and (is-O_list (read var15 var9)) (and (and (and (and (and (and (and (= var7 (write var15 var9 (O_list (list var8 (next (getlist (read var15 var9))))))) (= var6 var14)) (= var5 var13)) (= var4 var12)) (= var3 var11)) (= var2 var10)) (= var1 var9)) (= var0 var8))))) (inv_main18 var7 var6 var5 var4 var3 var2 var1 var0 var5))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Int) (var10 Int) (var11 Addr) (var12 Int) (var13 Int) (var14 list) (var15 Heap) (var16 Heap) (var17 Addr) (var18 Int) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Int) (var23 Addr) (var24 Int) (var25 Heap)) (or (not (and (inv_main16 var25 var24 var23 var22 var21 var20 var19 var18) (and (and (= var17 nullAddr) (and (and (and (and (and (and (and (and (= var16 (newHeap (alloc var15 (O_list var14)))) (= var13 var12)) (= var17 var11)) (= var10 var9)) (= var8 var7)) (= var6 var5)) (= var4 var7)) (= var3 5)) (= var2 (newAddr (alloc var15 (O_list var14)))))) (and (is-O_list (read var25 var19)) (and (and (and (and (and (and (and (= var15 (write var25 var19 (O_list (list (key (getlist (read var25 var19))) nullAddr)))) (= var12 var24)) (= var1 var23)) (= var9 var22)) (= var7 var21)) (= var5 var20)) (= var11 var19)) (= var0 var18)))))) (inv_main27 var16 var13 var17 var10 var8 var6 var2 var3))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Int) (var10 Int) (var11 Addr) (var12 Int) (var13 Int) (var14 list) (var15 Heap) (var16 Heap) (var17 Addr) (var18 Addr) (var19 Int) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Int) (var24 Addr) (var25 Int) (var26 Heap)) (or (not (and (inv_main18 var26 var25 var24 var23 var22 var21 var20 var19 var18) (and (and (= var17 nullAddr) (and (and (and (and (and (and (and (and (= var16 (newHeap (alloc var15 (O_list var14)))) (= var13 var12)) (= var17 var11)) (= var10 var9)) (= var8 var7)) (= var6 var5)) (= var4 var7)) (= var3 5)) (= var2 (newAddr (alloc var15 (O_list var14)))))) (and (is-O_list (read var26 var20)) (and (and (and (and (and (and (and (= var15 (write var26 var20 (O_list (list (key (getlist (read var26 var20))) var18)))) (= var12 var25)) (= var1 var24)) (= var9 var23)) (= var7 var22)) (= var5 var21)) (= var11 var20)) (= var0 var19)))))) (inv_main27 var16 var13 var17 var10 var8 var6 var2 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Int) (var5 Heap)) (or (not (and (inv_main62 var5 var4 var3 var2 var1 var0) (not (= var1 nullAddr)))) (inv_main65 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Addr) (var6 Int) (var7 Heap)) (or (not (and (inv_main13 var7 var6 var5 var4 var3 var2 var1 var0) (is-O_list (read var7 var1)))) (inv_main16 (write var7 var1 (O_list (list var0 (next (getlist (read var7 var1)))))) var6 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Int) (var10 Int) (var11 Addr) (var12 Int) (var13 Int) (var14 list) (var15 Heap) (var16 Heap) (var17 Addr) (var18 Int) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Int) (var23 Addr) (var24 Int) (var25 Heap)) (or (not (and (inv_main30 var25 var24 var23 var22 var21 var20 var19 var18) (and (and (= var17 nullAddr) (and (and (and (and (and (and (and (and (= var16 (newHeap (alloc var15 (O_list var14)))) (= var13 var12)) (= var17 var11)) (= var10 var9)) (= var8 var7)) (= var6 var5)) (= var4 var7)) (= var3 1)) (= var2 (newAddr (alloc var15 (O_list var14)))))) (and (is-O_list (read var25 var19)) (and (and (and (and (and (and (and (= var15 (write var25 var19 (O_list (list (key (getlist (read var25 var19))) nullAddr)))) (= var12 var24)) (= var1 var23)) (= var9 var22)) (= var7 var21)) (= var5 var20)) (= var11 var19)) (= var0 var18)))))) (inv_main41 var16 var13 var17 var10 var8 var6 var2 var3))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Int) (var10 Int) (var11 Addr) (var12 Int) (var13 Int) (var14 list) (var15 Heap) (var16 Heap) (var17 Addr) (var18 Addr) (var19 Int) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Int) (var24 Addr) (var25 Int) (var26 Heap)) (or (not (and (inv_main32 var26 var25 var24 var23 var22 var21 var20 var19 var18) (and (and (= var17 nullAddr) (and (and (and (and (and (and (and (and (= var16 (newHeap (alloc var15 (O_list var14)))) (= var13 var12)) (= var17 var11)) (= var10 var9)) (= var8 var7)) (= var6 var5)) (= var4 var7)) (= var3 1)) (= var2 (newAddr (alloc var15 (O_list var14)))))) (and (is-O_list (read var26 var20)) (and (and (and (and (and (and (and (= var15 (write var26 var20 (O_list (list (key (getlist (read var26 var20))) var18)))) (= var12 var25)) (= var1 var24)) (= var9 var23)) (= var7 var22)) (= var5 var21)) (= var11 var20)) (= var0 var19)))))) (inv_main41 var16 var13 var17 var10 var8 var6 var2 var3))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Addr) (var6 Int) (var7 Heap) (var8 Int) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Int) (var13 Addr) (var14 Int) (var15 Heap)) (or (not (and (inv_main42 var15 var14 var13 var12 var11 var10 var9 var8) (and (is-O_list (read var15 var9)) (and (and (and (and (and (and (and (= var7 (write var15 var9 (O_list (list var8 (next (getlist (read var15 var9))))))) (= var6 var14)) (= var5 var13)) (= var4 var12)) (= var3 var11)) (= var2 var10)) (= var1 var9)) (= var0 var8))))) (inv_main46 var7 var6 var5 var4 var3 var2 var1 var0 var5))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Int) (var6 Int) (var7 list) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Int) (var13 Addr) (var14 Int) (var15 Heap)) (or (not (and (inv_main5 var15 var14 var13 var12 var11 var10) (and (= var9 nullAddr) (and (and (and (and (and (and (and (and (= var8 (newHeap (alloc var15 (O_list var7)))) (= var6 var14)) (= var9 var13)) (= var5 var12)) (= var4 var11)) (= var3 var10)) (= var2 var11)) (= var1 2)) (= var0 (newAddr (alloc var15 (O_list var7)))))))) (inv_main13 var8 var6 var9 var5 var4 var3 var0 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Addr) (var5 Int) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Int) (var10 Addr) (var11 Int) (var12 Heap)) (or (not (and (inv_main65 var12 var11 var10 var9 var8 var7) (and (is-O_list (read var12 var8)) (and (and (and (and (and (and (= var6 var12) (= var5 var11)) (= var4 var10)) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var0 (next (getlist (read var12 var8)))))))) (inv_main62 var6 var5 var4 var3 var0 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Addr) (var6 Int) (var7 Heap) (var8 Int) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Int) (var13 Addr) (var14 Int) (var15 Heap)) (or (not (and (inv_main58 var15 var14 var13 var12 var11 var10 var9 var8) (and (is-O_list (read var15 var9)) (and (and (and (and (and (and (and (= var7 (write var15 var9 (O_list (list (key (getlist (read var15 var9))) nullAddr)))) (= var6 var14)) (= var5 var13)) (= var4 var12)) (= var3 var11)) (= var2 var10)) (= var1 var9)) (= var0 var8))))) (inv_main62 var7 var6 var1 var4 var1 var2))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Addr) (var6 Int) (var7 Heap) (var8 Addr) (var9 Int) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Int) (var14 Addr) (var15 Int) (var16 Heap)) (or (not (and (inv_main60 var16 var15 var14 var13 var12 var11 var10 var9 var8) (and (is-O_list (read var16 var10)) (and (and (and (and (and (and (and (= var7 (write var16 var10 (O_list (list (key (getlist (read var16 var10))) var8)))) (= var6 var15)) (= var5 var14)) (= var4 var13)) (= var3 var12)) (= var2 var11)) (= var1 var10)) (= var0 var9))))) (inv_main62 var7 var6 var1 var4 var1 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Int) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Int) (var10 Addr) (var11 Int) (var12 Heap)) (or (not (and (inv_main100 var12 var11 var10 var9 var8 var7) (and (not (= var6 nullAddr)) (and (is-O_list (read var12 var8)) (and (and (and (and (and (and (= var5 var12) (= var4 var11)) (= var3 var10)) (= var2 var9)) (= var1 var8)) (= var0 var7)) (= var6 (next (getlist (read var12 var8))))))))) (inv_main100 var5 var4 var3 var2 var6 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Int) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Int) (var12 Addr) (var13 Int) (var14 Heap) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Int) (var22 Addr) (var23 Int) (var24 Heap)) (or (not (and (inv_main95 var24 var23 var22 var21 var20 var19 var18 var17 var16) (and (not (= var15 nullAddr)) (and (and (is-O_list (read var24 var17)) (and (and (and (and (and (and (and (= var14 (write var24 var17 (O_list (list (key (getlist (read var24 var17))) var16)))) (= var13 var23)) (= var12 var22)) (= var11 var21)) (= var10 var20)) (= var9 var19)) (= var8 var18)) (= var7 var17))) (and (and (and (and (and (and (and (= var6 (write var14 var8 defObj)) (= var5 var13)) (= var15 var12)) (= var4 var11)) (= var3 var10)) (= var2 var9)) (= var1 var8)) (= var0 var7)))))) (inv_main100 var6 var5 var15 var4 var15 var2))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Addr) (var6 Int) (var7 Heap)) (or (not (and (inv_main27 var7 var6 var5 var4 var3 var2 var1 var0) (is-O_list (read var7 var1)))) (inv_main30 (write var7 var1 (O_list (list var0 (next (getlist (read var7 var1)))))) var6 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Int) (var10 Int) (var11 Addr) (var12 Int) (var13 Int) (var14 list) (var15 Heap) (var16 Heap) (var17 Addr) (var18 Int) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Int) (var23 Addr) (var24 Int) (var25 Heap)) (or (not (and (inv_main16 var25 var24 var23 var22 var21 var20 var19 var18) (and (and (not (= var17 nullAddr)) (and (and (and (and (and (and (and (and (= var16 (newHeap (alloc var15 (O_list var14)))) (= var13 var12)) (= var17 var11)) (= var10 var9)) (= var8 var7)) (= var6 var5)) (= var4 var7)) (= var3 5)) (= var2 (newAddr (alloc var15 (O_list var14)))))) (and (is-O_list (read var25 var19)) (and (and (and (and (and (and (and (= var15 (write var25 var19 (O_list (list (key (getlist (read var25 var19))) nullAddr)))) (= var12 var24)) (= var1 var23)) (= var9 var22)) (= var7 var21)) (= var5 var20)) (= var11 var19)) (= var0 var18)))))) (inv_main28 var16 var13 var17 var10 var8 var6 var2 var3))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Int) (var10 Int) (var11 Addr) (var12 Int) (var13 Int) (var14 list) (var15 Heap) (var16 Heap) (var17 Addr) (var18 Addr) (var19 Int) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Int) (var24 Addr) (var25 Int) (var26 Heap)) (or (not (and (inv_main18 var26 var25 var24 var23 var22 var21 var20 var19 var18) (and (and (not (= var17 nullAddr)) (and (and (and (and (and (and (and (and (= var16 (newHeap (alloc var15 (O_list var14)))) (= var13 var12)) (= var17 var11)) (= var10 var9)) (= var8 var7)) (= var6 var5)) (= var4 var7)) (= var3 5)) (= var2 (newAddr (alloc var15 (O_list var14)))))) (and (is-O_list (read var26 var20)) (and (and (and (and (and (and (and (= var15 (write var26 var20 (O_list (list (key (getlist (read var26 var20))) var18)))) (= var12 var25)) (= var1 var24)) (= var9 var23)) (= var7 var22)) (= var5 var21)) (= var11 var20)) (= var0 var19)))))) (inv_main28 var16 var13 var17 var10 var8 var6 var2 var3))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Int) (var6 Int) (var7 list) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Int) (var13 Addr) (var14 Int) (var15 Heap)) (or (not (and (inv_main5 var15 var14 var13 var12 var11 var10) (and (not (= var9 nullAddr)) (and (and (and (and (and (and (and (and (= var8 (newHeap (alloc var15 (O_list var7)))) (= var6 var14)) (= var9 var13)) (= var5 var12)) (= var4 var11)) (= var3 var10)) (= var2 var11)) (= var1 2)) (= var0 (newAddr (alloc var15 (O_list var7)))))))) (inv_main14 var8 var6 var9 var5 var4 var3 var0 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Int) (var10 Int) (var11 Addr) (var12 Int) (var13 Int) (var14 list) (var15 Heap) (var16 Heap) (var17 Addr) (var18 Int) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Int) (var23 Addr) (var24 Int) (var25 Heap)) (or (not (and (inv_main44 var25 var24 var23 var22 var21 var20 var19 var18) (and (and (= var17 nullAddr) (and (and (and (and (and (and (and (and (= var16 (newHeap (alloc var15 (O_list var14)))) (= var13 var12)) (= var17 var11)) (= var10 var9)) (= var8 var7)) (= var6 var5)) (= var4 var7)) (= var3 3)) (= var2 (newAddr (alloc var15 (O_list var14)))))) (and (is-O_list (read var25 var19)) (and (and (and (and (and (and (and (= var15 (write var25 var19 (O_list (list (key (getlist (read var25 var19))) nullAddr)))) (= var12 var24)) (= var1 var23)) (= var9 var22)) (= var7 var21)) (= var5 var20)) (= var11 var19)) (= var0 var18)))))) (inv_main55 var16 var13 var17 var10 var8 var6 var2 var3))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Int) (var10 Int) (var11 Addr) (var12 Int) (var13 Int) (var14 list) (var15 Heap) (var16 Heap) (var17 Addr) (var18 Addr) (var19 Int) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Int) (var24 Addr) (var25 Int) (var26 Heap)) (or (not (and (inv_main46 var26 var25 var24 var23 var22 var21 var20 var19 var18) (and (and (= var17 nullAddr) (and (and (and (and (and (and (and (and (= var16 (newHeap (alloc var15 (O_list var14)))) (= var13 var12)) (= var17 var11)) (= var10 var9)) (= var8 var7)) (= var6 var5)) (= var4 var7)) (= var3 3)) (= var2 (newAddr (alloc var15 (O_list var14)))))) (and (is-O_list (read var26 var20)) (and (and (and (and (and (and (and (= var15 (write var26 var20 (O_list (list (key (getlist (read var26 var20))) var18)))) (= var12 var25)) (= var1 var24)) (= var9 var23)) (= var7 var22)) (= var5 var21)) (= var11 var20)) (= var0 var19)))))) (inv_main55 var16 var13 var17 var10 var8 var6 var2 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Int) (var6 Addr) (var7 Int) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Int) (var14 Addr) (var15 Int) (var16 Heap)) (or (not (and (inv_main90 var16 var15 var14 var13 var12 var11 var10 var9) (and (is-O_list (read var16 var9)) (and (and (and (and (and (and (and (and (= var8 var16) (= var7 var15)) (= var6 var14)) (= var5 var13)) (= var4 var12)) (= var3 var11)) (= var2 var10)) (= var1 var9)) (= var0 (next (getlist (read var16 var9)))))))) (inv_main87 var8 var7 var6 var5 var4 var3 var2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Int) (var5 Heap)) (or (not (and (inv_main67 var5 var4 var3 var2 var1 var0) (and (not (= var3 var0)) (is-O_list (read var5 var0))))) (inv_main87 var5 var4 var3 var2 var1 var0 var0 var3))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Addr) (var6 Int) (var7 Heap)) (or (not (and (inv_main55 var7 var6 var5 var4 var3 var2 var1 var0) (is-O_list (read var7 var1)))) (inv_main58 (write var7 var1 (O_list (list var0 (next (getlist (read var7 var1)))))) var6 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Addr) (var6 Int) (var7 Heap) (var8 Int) (var9 Int) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Int) (var14 Addr) (var15 Int) (var16 Heap) (var17 Int) (var18 Int) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Int) (var23 Addr) (var24 Int) (var25 Heap)) (or (not (and (inv_main71 var25 var24 var23 var22 var21 var20 var19 var18) (and (and (not (= var17 0)) (and (and (not (= var19 nullAddr)) (is-O_list (read var25 var19))) (and (and (and (and (and (and (and (and (= var16 var25) (= var15 var24)) (= var14 var23)) (= var13 var22)) (= var12 var21)) (= var11 var20)) (= var10 var19)) (= var9 var18)) (= var8 (key (getlist (read var25 var19))))))) (and (and (and (and (and (and (and (and (= var7 var16) (= var6 var15)) (= var5 var14)) (= var4 var13)) (= var3 var12)) (= var2 var11)) (= var1 var10)) (= var0 var9)) (or (and (not (= var8 var9)) (= var17 1)) (and (= var8 var9) (= var17 0))))))) (inv_main74 var7 var6 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Addr) (var6 Int) (var7 Heap)) (not (and (inv_main13 var7 var6 var5 var4 var3 var2 var1 var0) (not (is-O_list (read var7 var1)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Addr) (var6 Int) (var7 Heap)) (not (and (inv_main16 var7 var6 var5 var4 var3 var2 var1 var0) (not (is-O_list (read var7 var1)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Addr) (var6 Int) (var7 Heap)) (not (and (inv_main14 var7 var6 var5 var4 var3 var2 var1 var0) (not (is-O_list (read var7 var1)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Int) (var6 Addr) (var7 Int) (var8 Heap)) (not (and (inv_main18 var8 var7 var6 var5 var4 var3 var2 var1 var0) (not (is-O_list (read var8 var2)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Addr) (var6 Int) (var7 Heap)) (not (and (inv_main27 var7 var6 var5 var4 var3 var2 var1 var0) (not (is-O_list (read var7 var1)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Addr) (var6 Int) (var7 Heap)) (not (and (inv_main30 var7 var6 var5 var4 var3 var2 var1 var0) (not (is-O_list (read var7 var1)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Addr) (var6 Int) (var7 Heap)) (not (and (inv_main28 var7 var6 var5 var4 var3 var2 var1 var0) (not (is-O_list (read var7 var1)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Int) (var6 Addr) (var7 Int) (var8 Heap)) (not (and (inv_main32 var8 var7 var6 var5 var4 var3 var2 var1 var0) (not (is-O_list (read var8 var2)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Addr) (var6 Int) (var7 Heap)) (not (and (inv_main41 var7 var6 var5 var4 var3 var2 var1 var0) (not (is-O_list (read var7 var1)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Addr) (var6 Int) (var7 Heap)) (not (and (inv_main44 var7 var6 var5 var4 var3 var2 var1 var0) (not (is-O_list (read var7 var1)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Addr) (var6 Int) (var7 Heap)) (not (and (inv_main42 var7 var6 var5 var4 var3 var2 var1 var0) (not (is-O_list (read var7 var1)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Int) (var6 Addr) (var7 Int) (var8 Heap)) (not (and (inv_main46 var8 var7 var6 var5 var4 var3 var2 var1 var0) (not (is-O_list (read var8 var2)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Addr) (var6 Int) (var7 Heap)) (not (and (inv_main55 var7 var6 var5 var4 var3 var2 var1 var0) (not (is-O_list (read var7 var1)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Addr) (var6 Int) (var7 Heap)) (not (and (inv_main58 var7 var6 var5 var4 var3 var2 var1 var0) (not (is-O_list (read var7 var1)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Addr) (var6 Int) (var7 Heap)) (not (and (inv_main56 var7 var6 var5 var4 var3 var2 var1 var0) (not (is-O_list (read var7 var1)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Int) (var6 Addr) (var7 Int) (var8 Heap)) (not (and (inv_main60 var8 var7 var6 var5 var4 var3 var2 var1 var0) (not (is-O_list (read var8 var2)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Int) (var5 Heap)) (not (and (inv_main65 var5 var4 var3 var2 var1 var0) (not (is-O_list (read var5 var1)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Addr) (var6 Int) (var7 Heap)) (not (and (inv_main71 var7 var6 var5 var4 var3 var2 var1 var0) (and (not (= var1 nullAddr)) (not (is-O_list (read var7 var1))))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Addr) (var6 Int) (var7 Heap)) (not (and (inv_main74 var7 var6 var5 var4 var3 var2 var1 var0) (not (is-O_list (read var7 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Int) (var5 Heap)) (not (and (inv_main67 var5 var4 var3 var2 var1 var0) (not (is-O_list (read var5 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Int) (var5 Heap)) (not (and (inv_main67 var5 var4 var3 var2 var1 var0) (and (is-O_list (read var5 var0)) (not (= (key (getlist (read var5 var0))) 2)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Addr) (var6 Int) (var7 Heap)) (not (and (inv_main87 var7 var6 var5 var4 var3 var2 var1 var0) (not (is-O_list (read var7 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Addr) (var6 Int) (var7 Heap)) (not (and (inv_main90 var7 var6 var5 var4 var3 var2 var1 var0) (not (is-O_list (read var7 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Addr) (var6 Int) (var7 Heap)) (not (and (inv_main88 var7 var6 var5 var4 var3 var2 var1 var0) (not (is-O_list (read var7 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Addr) (var6 Int) (var7 Heap)) (not (and (inv_main86 var7 var6 var5 var4 var3 var2 var1 var0) (not (is-O_list (read var7 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Int) (var6 Addr) (var7 Int) (var8 Heap)) (not (and (inv_main95 var8 var7 var6 var5 var4 var3 var2 var1 var0) (not (is-O_list (read var8 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Int) (var5 Heap)) (not (and (inv_main100 var5 var4 var3 var2 var1 var0) (not (is-O_list (read var5 var1)))))))
(check-sat)
