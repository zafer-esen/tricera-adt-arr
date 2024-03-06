(set-logic HORN)
(set-info :source |
    Benchmark: C_VC
    Output by Princess (http://www.philipp.ruemmer.org/princess.shtml)
|)
(set-info :status unknown)
(declare-datatype bool (
  (true)
  (false)
))
(declare-heap Heap Addr HeapObject
 defObj
 ((HeapObject 0) (internal_node 0) (sll 0)) (
  (
   (O_Int (getInt Int))
   (O_UInt (getUInt Int))
   (O_Addr (getAddr Addr))
   (O_AddrRange (getAddrRange AddrRange))
   (O_internal_node (getinternal_node internal_node))
   (O_sll (getsll sll))
   (defObj)
  )
  (
   (internal_node (|internal_node::next| Addr))
  )
  (
   (sll (|sll::next| Addr) (|sll::shared| Addr))
  )
))
(declare-fun inv_main2415_5 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main2455_5 (Heap Addr) Bool)
(declare-fun inv_main2457_5 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main2458_5 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main2459_12 (Heap Addr Int) Bool)
(declare-fun inv_main_10 (Heap Addr Addr Addr Addr Addr) Bool)
(assert (forall ((var0 Addr) (var1 Heap)) (or (not (and (= var1 emptyHeap) (= var0 nullAddr))) (inv_main2455_5 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Bool) (var10 Addr) (var11 internal_node) (var12 Heap) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Heap) (var21 Heap) (var22 Addr) (var23 Addr) (var24 Addr) (var25 Heap)) (or (not (and (inv_main2415_5 var25 var24 var23 var22) (and (and (and (and (and (and (= var21 var20) (= var19 var18)) (= var17 var16)) (= var15 var14)) (= var13 (|internal_node::next| (getinternal_node (read var20 var14))))) (and (and (and (and (and (and (= var12 (newHeap (alloc var25 (O_internal_node var11)))) (or (and var9 (= var10 (newAddr (alloc var25 (O_internal_node var11))))) (and (not var9) (= var10 var24)))) (= var8 var23)) (= var7 var22)) (= var6 (newAddr (alloc var25 (O_internal_node var11))))) (and (and (and (and (= var5 (write var12 var6 (O_internal_node (internal_node nullAddr)))) (= var4 var10)) (= var3 var8)) (= var2 var7)) (= var1 var6))) (not (= var0 0)))) (and (and (and (= var20 (write var5 var2 (O_internal_node (internal_node var1)))) (= var18 var4)) (= var16 var3)) (= var14 var2))))) (inv_main2415_5 var21 var19 var17 var13))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Bool) (var5 Addr) (var6 internal_node) (var7 Heap) (var8 Addr) (var9 Heap)) (or (not (and (inv_main2455_5 var9 var8) (and (and (and (= var7 (newHeap (alloc var9 (O_internal_node var6)))) (or (and var4 (= var5 (newAddr (alloc var9 (O_internal_node var6))))) (and (not var4) (= var5 var8)))) (= var3 (newAddr (alloc var9 (O_internal_node var6))))) (and (and (= var2 (write var7 var3 (O_internal_node (internal_node nullAddr)))) (= var1 var5)) (= var0 var3))))) (inv_main2415_5 var2 var1 var0 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main2458_5 var5 var4 var3 var2 var1) (and (= var1 nullAddr) (= var0 0)))) (inv_main2459_12 var5 var4 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Heap) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Heap)) (or (not (and (inv_main2458_5 var16 var15 var14 var13 var12) (and (and (and (and (and (and (and (= var11 var16) (= var10 var15)) (= var9 var14)) (= var8 var13)) (= var7 var12)) (= var6 (|sll::next| (getsll (read var16 var12))))) (and (and (and (and (and (= var5 (write var11 var7 defObj)) (or (and (= var10 var7) (= var4 nullAddr)) (and (not (= var10 var7)) (= var4 var10)))) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var0 var6))) (not (= var12 nullAddr))))) (inv_main2458_5 var5 var4 var3 var2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main2457_5 var4 var3 var2 var1 var0) (= var0 nullAddr))) (inv_main2458_5 var4 var3 var2 var1 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Heap) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Heap)) (or (not (and (inv_main2457_5 var16 var15 var14 var13 var12) (and (and (and (and (and (and (and (= var11 var16) (= var10 var15)) (= var9 var14)) (= var8 var13)) (= var7 var12)) (= var6 (|internal_node::next| (getinternal_node (read var16 var12))))) (and (and (and (and (and (= var5 (write var11 var7 defObj)) (or (and (= var10 var7) (= var4 nullAddr)) (and (not (= var10 var7)) (= var4 var10)))) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var0 var6))) (not (= var12 nullAddr))))) (inv_main2457_5 var5 var4 var3 var2 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main_10 var6 var5 var4 var3 var2 var1) (= var0 0))) (inv_main2457_5 var6 var5 var4 var2 var4))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Int) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Heap) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Heap) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Addr) (var25 Addr) (var26 Bool) (var27 Addr) (var28 sll) (var29 Heap) (var30 Addr) (var31 Addr) (var32 Addr) (var33 Addr) (var34 Addr) (var35 Addr) (var36 Addr) (var37 Addr) (var38 Addr) (var39 Addr) (var40 Addr) (var41 Heap) (var42 Heap) (var43 Addr) (var44 Addr) (var45 Addr) (var46 Addr) (var47 Addr) (var48 Heap)) (or (not (and (inv_main_10 var48 var47 var46 var45 var44 var43) (and (and (and (and (and (and (and (and (= var42 var41) (= var40 var39)) (= var38 var37)) (= var36 var35)) (= var34 var33)) (= var32 var31)) (= var30 (|sll::next| (getsll (read var41 var31))))) (and (and (and (and (and (and (and (and (and (and (= var29 (newHeap (alloc var48 (O_sll var28)))) (or (and var26 (= var27 (newAddr (alloc var48 (O_sll var28))))) (and (not var26) (= var27 var47)))) (= var25 var46)) (= var24 var45)) (= var23 var44)) (= var22 var43)) (= var21 (newAddr (alloc var48 (O_sll var28))))) (and (and (and (and (and (and (= var20 (write var29 var21 (O_sll (sll nullAddr (|sll::shared| (getsll (read var29 var21))))))) (= var19 var27)) (= var18 var25)) (= var17 var24)) (= var16 var23)) (= var15 var22)) (= var14 var21))) (and (and (and (and (and (and (= var13 (write var20 var14 (O_sll (sll (|sll::next| (getsll (read var20 var14))) nullAddr)))) (= var12 var19)) (= var11 var18)) (= var10 var17)) (= var9 var16)) (= var8 var15)) (= var7 var14))) (not (= var6 0))) (and (and (and (and (and (= var5 (write var13 var8 (O_sll (sll var7 (|sll::shared| (getsll (read var13 var8))))))) (= var4 var12)) (= var3 var11)) (= var2 var10)) (= var1 var9)) (= var0 var8)))) (and (and (and (and (and (= var41 (write var5 (|sll::next| (getsll (read var5 var0))) (O_sll (sll (|sll::next| (getsll (read var5 (|sll::next| (getsll (read var5 var0)))))) var2)))) (= var39 var4)) (= var37 var3)) (= var35 var2)) (= var33 var1)) (= var31 var0))))) (inv_main_10 var42 var40 var38 var36 var34 var30))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Heap) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Bool) (var16 Addr) (var17 sll) (var18 Heap) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Heap)) (or (not (and (inv_main2415_5 var22 var21 var20 var19) (and (and (and (and (and (and (and (and (= var18 (newHeap (alloc var22 (O_sll var17)))) (or (and var15 (= var16 (newAddr (alloc var22 (O_sll var17))))) (and (not var15) (= var16 var21)))) (= var14 var20)) (= var13 var20)) (= var12 (newAddr (alloc var22 (O_sll var17))))) (and (and (and (and (= var11 (write var18 var12 (O_sll (sll nullAddr (|sll::shared| (getsll (read var18 var12))))))) (= var10 var16)) (= var9 var14)) (= var8 var13)) (= var7 var12))) (and (and (and (and (= var6 (write var11 var7 (O_sll (sll (|sll::next| (getsll (read var11 var7))) nullAddr)))) (= var5 var10)) (= var4 var9)) (= var3 var8)) (= var2 var7))) (= var1 0)) (= var0 (write var6 var2 (O_sll (sll (|sll::next| (getsll (read var6 var2))) var3))))))) (inv_main_10 var0 var5 var4 var3 var2 var2))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap)) (not (and (inv_main2459_12 var2 var1 var0) (not (= var1 nullAddr))))))
(check-sat)
