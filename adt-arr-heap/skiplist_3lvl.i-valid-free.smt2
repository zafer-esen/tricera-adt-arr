(set-logic HORN)
(set-info :source |
    Benchmark: C_VC
    Output by Princess (http://www.philipp.ruemmer.org/princess.shtml)
|)
(set-info :status sat)
(declare-heap Heap Addr HeapObject
 defObj
 ((HeapObject 0) (sl_item 0) (sl 0)) (
  (
   (O_Int (getInt Int))
   (O_UInt (getUInt Int))
   (O_Addr (getAddr Addr))
   (O_AddrRange (getAddrRange AddrRange))
   (O_sl_item (getsl_item sl_item))
   (O_sl (getsl sl))
   (defObj)
  )
  (
   (sl_item (|sl_item::n1| Addr) (|sl_item::n2| Addr) (|sl_item::n3| Addr))
  )
  (
   (sl (|sl::head| Addr) (|sl::tail| Addr))
  )
))
(declare-fun inv_main581_2 (Heap) Bool)
(declare-fun inv_main581_2_4 (Heap Addr) Bool)
(declare-fun inv_main_12 (Heap Addr Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main_17 (Heap Addr Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main_33 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main_36 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main_7 (Heap Addr Addr Addr Addr Addr Addr) Bool)
(assert (forall ((var0 Heap)) (or (not (= var0 emptyHeap)) (inv_main581_2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Int) (var9 Int) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Heap) (var24 Heap) (var25 Addr) (var26 Addr) (var27 Addr) (var28 Addr) (var29 Addr) (var30 Addr) (var31 Heap)) (or (not (and (inv_main_7 var31 var30 var29 var28 var27 var26 var25) (and (and (and (and (and (and (and (and (= var24 var23) (= var22 var21)) (= var20 var19)) (= var18 var17)) (= var16 var15)) (= var14 var13)) (= var12 var11)) (= var10 (|sl_item::n3| (getsl_item (read var23 var13))))) (and (not (= var9 0)) (and (and (not (= var8 0)) (and (and (and (and (and (and (and (= var7 var31) (= var6 var30)) (= var5 var29)) (= var4 var28)) (= var3 var27)) (= var2 var26)) (= var1 var25)) (= var0 (|sl_item::n3| (getsl_item (read var31 var26)))))) (and (and (and (and (and (and (and (= var23 var7) (= var21 var6)) (= var19 var5)) (= var17 var4)) (= var15 var3)) (= var13 var2)) (= var11 var1)) (or (and (not (= var0 (|sl::tail| (getsl (read var7 var5))))) (= var8 1)) (and (= var0 (|sl::tail| (getsl (read var7 var5)))) (= var8 0))))))))) (inv_main_7 var24 var22 var20 var18 var16 var10 var12))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Heap) (var13 Addr) (var14 Heap)) (or (not (and (inv_main581_2_4 var14 var13) (and (and (and (and (and (and (and (and (= var12 var14) (= var11 var13)) (= var10 var13)) (= var9 var8)) (= var7 var6)) (= var5 var4)) (= var3 var2)) (= var1 (|sl::head| (getsl (read var14 var13))))) (not (= var0 0))))) (inv_main_7 var12 var11 var10 var9 var7 var1 var3))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Heap) (var14 Heap) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Heap)) (or (not (and (inv_main_36 var18 var17 var16 var15) (and (and (and (and (and (and (and (= var14 var13) (= var12 var11)) (= var10 var9)) (= var8 var7)) (= var6 (|sl_item::n1| (getsl_item (read var13 (|sl::head| (getsl (read var13 var9)))))))) (and (and (and (and (and (= var13 var5) (= var11 var4)) (= var9 var3)) (= var2 var1)) (= var7 (|sl::head| (getsl (read var5 var3))))) (not (= (|sl::head| (getsl (read var5 var3))) nullAddr)))) (and (and (and (= var5 (write var18 var15 defObj)) (= var4 var17)) (= var3 var16)) (= var1 var15))) (= var0 (write var14 var10 (O_sl (sl var6 (|sl::tail| (getsl (read var14 var10)))))))))) (inv_main_36 var0 var12 var10 var8))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Heap) (var12 Heap) (var13 Addr) (var14 Heap)) (or (not (and (inv_main581_2_4 var14 var13) (and (and (and (and (and (and (and (= var12 var11) (= var10 var9)) (= var8 var7)) (= var6 var5)) (= var4 (|sl_item::n1| (getsl_item (read var11 (|sl::head| (getsl (read var11 var7)))))))) (and (and (and (and (and (= var11 var14) (= var9 var13)) (= var7 var13)) (= var3 var2)) (= var5 (|sl::head| (getsl (read var14 var13))))) (not (= (|sl::head| (getsl (read var14 var13))) nullAddr)))) (= var1 0)) (= var0 (write var12 var8 (O_sl (sl var4 (|sl::tail| (getsl (read var12 var8)))))))))) (inv_main_36 var0 var10 var8 var6))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Heap) (var15 Int) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Heap)) (or (not (and (inv_main_7 var22 var21 var20 var19 var18 var17 var16) (and (and (= var15 0) (and (and (and (and (and (and (and (= var14 var22) (= var13 var21)) (= var12 var20)) (= var11 var19)) (= var10 var18)) (= var9 var17)) (= var8 var16)) (= var7 (|sl_item::n3| (getsl_item (read var22 var17)))))) (and (and (and (and (and (and (and (= var6 var14) (= var5 var13)) (= var4 var12)) (= var3 var11)) (= var2 var10)) (= var1 var9)) (= var0 var8)) (or (and (not (= var7 (|sl::tail| (getsl (read var14 var12))))) (= var15 1)) (and (= var7 (|sl::tail| (getsl (read var14 var12)))) (= var15 0))))))) (inv_main_12 var6 var5 var4 var3 var1 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Heap) (var15 Int) (var16 Int) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Heap)) (or (not (and (inv_main_7 var23 var22 var21 var20 var19 var18 var17) (and (= var16 0) (and (and (not (= var15 0)) (and (and (and (and (and (and (and (= var14 var23) (= var13 var22)) (= var12 var21)) (= var11 var20)) (= var10 var19)) (= var9 var18)) (= var8 var17)) (= var7 (|sl_item::n3| (getsl_item (read var23 var18)))))) (and (and (and (and (and (and (and (= var6 var14) (= var5 var13)) (= var4 var12)) (= var3 var11)) (= var2 var10)) (= var1 var9)) (= var0 var8)) (or (and (not (= var7 (|sl::tail| (getsl (read var14 var12))))) (= var15 1)) (and (= var7 (|sl::tail| (getsl (read var14 var12)))) (= var15 0)))))))) (inv_main_12 var6 var5 var4 var3 var1 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Int) (var9 Int) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Heap) (var24 Heap) (var25 Addr) (var26 Addr) (var27 Addr) (var28 Addr) (var29 Addr) (var30 Addr) (var31 Heap)) (or (not (and (inv_main_12 var31 var30 var29 var28 var27 var26 var25) (and (and (and (and (and (and (and (and (= var24 var23) (= var22 var21)) (= var20 var19)) (= var18 var17)) (= var16 var15)) (= var14 var13)) (= var12 var11)) (= var10 (|sl_item::n2| (getsl_item (read var23 var15))))) (and (not (= var9 0)) (and (and (not (= var8 0)) (and (and (and (and (and (and (and (= var7 var31) (= var6 var30)) (= var5 var29)) (= var4 var28)) (= var3 var27)) (= var2 var26)) (= var1 var25)) (= var0 (|sl_item::n2| (getsl_item (read var31 var27)))))) (and (and (and (and (and (and (and (= var23 var7) (= var21 var6)) (= var19 var5)) (= var17 var4)) (= var15 var3)) (= var13 var2)) (= var11 var1)) (or (and (not (= var0 (|sl_item::n3| (getsl_item (read var7 var2))))) (= var8 1)) (and (= var0 (|sl_item::n3| (getsl_item (read var7 var2)))) (= var8 0))))))))) (inv_main_12 var24 var22 var20 var18 var10 var14 var12))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main_36 var7 var6 var5 var4) (and (= (|sl::head| (getsl (read var3 var2))) nullAddr) (and (and (and (= var3 (write var7 var4 defObj)) (= var1 var6)) (= var2 var5)) (= var0 var4))))) (inv_main_33 var3 var1 var2 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Heap)) (or (not (and (inv_main581_2_4 var3 var2) (and (= (|sl::head| (getsl (read var3 var2))) nullAddr) (= var1 0)))) (inv_main_33 var3 var2 var2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Heap) (var15 Int) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Heap)) (or (not (and (inv_main_12 var22 var21 var20 var19 var18 var17 var16) (and (and (= var15 0) (and (and (and (and (and (and (and (= var14 var22) (= var13 var21)) (= var12 var20)) (= var11 var19)) (= var10 var18)) (= var9 var17)) (= var8 var16)) (= var7 (|sl_item::n2| (getsl_item (read var22 var18)))))) (and (and (and (and (and (and (and (= var6 var14) (= var5 var13)) (= var4 var12)) (= var3 var11)) (= var2 var10)) (= var1 var9)) (= var0 var8)) (or (and (not (= var7 (|sl_item::n3| (getsl_item (read var14 var9))))) (= var15 1)) (and (= var7 (|sl_item::n3| (getsl_item (read var14 var9)))) (= var15 0))))))) (inv_main_17 var6 var5 var4 var2 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Heap) (var15 Int) (var16 Int) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Heap)) (or (not (and (inv_main_12 var23 var22 var21 var20 var19 var18 var17) (and (= var16 0) (and (and (not (= var15 0)) (and (and (and (and (and (and (and (= var14 var23) (= var13 var22)) (= var12 var21)) (= var11 var20)) (= var10 var19)) (= var9 var18)) (= var8 var17)) (= var7 (|sl_item::n2| (getsl_item (read var23 var19)))))) (and (and (and (and (and (and (and (= var6 var14) (= var5 var13)) (= var4 var12)) (= var3 var11)) (= var2 var10)) (= var1 var9)) (= var0 var8)) (or (and (not (= var7 (|sl_item::n3| (getsl_item (read var14 var9))))) (= var15 1)) (and (= var7 (|sl_item::n3| (getsl_item (read var14 var9)))) (= var15 0)))))))) (inv_main_17 var6 var5 var4 var2 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Int) (var9 Int) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Heap) (var24 Heap) (var25 Addr) (var26 Addr) (var27 Addr) (var28 Addr) (var29 Addr) (var30 Addr) (var31 Heap)) (or (not (and (inv_main_17 var31 var30 var29 var28 var27 var26 var25) (and (and (and (and (and (and (and (and (= var24 var23) (= var22 var21)) (= var20 var19)) (= var18 var17)) (= var16 var15)) (= var14 var13)) (= var12 var11)) (= var10 (|sl_item::n1| (getsl_item (read var23 var17))))) (and (not (= var9 0)) (and (and (not (= var8 0)) (and (and (and (and (and (and (and (= var7 var31) (= var6 var30)) (= var5 var29)) (= var4 var28)) (= var3 var27)) (= var2 var26)) (= var1 var25)) (= var0 (|sl_item::n1| (getsl_item (read var31 var28)))))) (and (and (and (and (and (and (and (= var23 var7) (= var21 var6)) (= var19 var5)) (= var17 var4)) (= var15 var3)) (= var13 var2)) (= var11 var1)) (or (and (not (= var0 (|sl_item::n2| (getsl_item (read var7 var3))))) (= var8 1)) (and (= var0 (|sl_item::n2| (getsl_item (read var7 var3)))) (= var8 0))))))))) (inv_main_17 var24 var22 var20 var10 var16 var14 var12))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Heap) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Heap) (var22 Int) (var23 Addr) (var24 Addr) (var25 Addr) (var26 Addr) (var27 Addr) (var28 Addr) (var29 Addr) (var30 sl_item) (var31 Heap) (var32 Addr) (var33 Addr) (var34 Addr) (var35 Addr) (var36 Addr) (var37 Addr) (var38 Addr) (var39 Addr) (var40 Addr) (var41 Addr) (var42 Addr) (var43 Addr) (var44 Addr) (var45 Heap) (var46 Heap) (var47 Int) (var48 Addr) (var49 Addr) (var50 Addr) (var51 Addr) (var52 Addr) (var53 Addr) (var54 Heap)) (or (not (and (inv_main_17 var54 var53 var52 var51 var50 var49 var48) (and (= var47 0) (and (and (and (and (and (and (and (and (and (and (= var46 var45) (= var44 var43)) (= var42 var41)) (= var40 var39)) (= var38 var37)) (= var36 var35)) (= var34 var33)) (= var32 (|sl_item::n1| (getsl_item (read var45 var39))))) (and (and (and (and (and (and (and (and (= var45 (newHeap (alloc var31 (O_sl_item var30)))) (= var43 var29)) (= var41 var28)) (= var39 var27)) (= var37 var26)) (= var35 var25)) (= var24 var23)) (= var33 (newAddr (alloc var31 (O_sl_item var30))))) (and (and (= var22 0) (and (and (and (and (and (and (and (= var21 var54) (= var20 var53)) (= var19 var52)) (= var18 var51)) (= var17 var50)) (= var16 var49)) (= var15 var48)) (= var14 (|sl_item::n1| (getsl_item (read var54 var51)))))) (and (and (and (and (and (and (and (= var31 var21) (= var29 var20)) (= var28 var19)) (= var27 var18)) (= var26 var17)) (= var25 var16)) (= var23 var15)) (or (and (not (= var14 (|sl_item::n2| (getsl_item (read var21 var17))))) (= var22 1)) (and (= var14 (|sl_item::n2| (getsl_item (read var21 var17)))) (= var22 0))))))) (and (and (and (and (and (and (= var13 (write var46 var34 (O_sl_item (sl_item var32 (|sl_item::n2| (getsl_item (read var46 var34))) (|sl_item::n3| (getsl_item (read var46 var34))))))) (= var12 var44)) (= var11 var42)) (= var10 var40)) (= var9 var38)) (= var8 var36)) (= var7 var34))) (and (and (and (and (and (and (= var6 (write var13 var10 (O_sl_item (sl_item var7 (|sl_item::n2| (getsl_item (read var13 var10))) (|sl_item::n3| (getsl_item (read var13 var10))))))) (= var5 var12)) (= var4 var11)) (= var3 var10)) (= var2 var9)) (= var1 var8)) (= var0 var7)))))) (inv_main581_2_4 var6 var5))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Heap) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Heap) (var22 Int) (var23 Int) (var24 Addr) (var25 Addr) (var26 Addr) (var27 Addr) (var28 Addr) (var29 Addr) (var30 Addr) (var31 sl_item) (var32 Heap) (var33 Addr) (var34 Addr) (var35 Addr) (var36 Addr) (var37 Addr) (var38 Addr) (var39 Addr) (var40 Addr) (var41 Addr) (var42 Addr) (var43 Addr) (var44 Addr) (var45 Addr) (var46 Heap) (var47 Heap) (var48 Int) (var49 Addr) (var50 Addr) (var51 Addr) (var52 Addr) (var53 Addr) (var54 Addr) (var55 Heap)) (or (not (and (inv_main_17 var55 var54 var53 var52 var51 var50 var49) (and (= var48 0) (and (and (and (and (and (and (and (and (and (and (= var47 var46) (= var45 var44)) (= var43 var42)) (= var41 var40)) (= var39 var38)) (= var37 var36)) (= var35 var34)) (= var33 (|sl_item::n1| (getsl_item (read var46 var40))))) (and (and (and (and (and (and (and (and (= var46 (newHeap (alloc var32 (O_sl_item var31)))) (= var44 var30)) (= var42 var29)) (= var40 var28)) (= var38 var27)) (= var36 var26)) (= var25 var24)) (= var34 (newAddr (alloc var32 (O_sl_item var31))))) (and (= var23 0) (and (and (not (= var22 0)) (and (and (and (and (and (and (and (= var21 var55) (= var20 var54)) (= var19 var53)) (= var18 var52)) (= var17 var51)) (= var16 var50)) (= var15 var49)) (= var14 (|sl_item::n1| (getsl_item (read var55 var52)))))) (and (and (and (and (and (and (and (= var32 var21) (= var30 var20)) (= var29 var19)) (= var28 var18)) (= var27 var17)) (= var26 var16)) (= var24 var15)) (or (and (not (= var14 (|sl_item::n2| (getsl_item (read var21 var17))))) (= var22 1)) (and (= var14 (|sl_item::n2| (getsl_item (read var21 var17)))) (= var22 0)))))))) (and (and (and (and (and (and (= var13 (write var47 var35 (O_sl_item (sl_item var33 (|sl_item::n2| (getsl_item (read var47 var35))) (|sl_item::n3| (getsl_item (read var47 var35))))))) (= var12 var45)) (= var11 var43)) (= var10 var41)) (= var9 var39)) (= var8 var37)) (= var7 var35))) (and (and (and (and (and (and (= var6 (write var13 var10 (O_sl_item (sl_item var7 (|sl_item::n2| (getsl_item (read var13 var10))) (|sl_item::n3| (getsl_item (read var13 var10))))))) (= var5 var12)) (= var4 var11)) (= var3 var10)) (= var2 var9)) (= var1 var8)) (= var0 var7)))))) (inv_main581_2_4 var6 var5))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Heap) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Heap) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Addr) (var25 Addr) (var26 Addr) (var27 Addr) (var28 Heap) (var29 Int) (var30 Addr) (var31 Addr) (var32 Addr) (var33 Addr) (var34 Addr) (var35 Addr) (var36 Addr) (var37 sl_item) (var38 Heap) (var39 Addr) (var40 Addr) (var41 Addr) (var42 Addr) (var43 Addr) (var44 Addr) (var45 Addr) (var46 Addr) (var47 Addr) (var48 Addr) (var49 Addr) (var50 Addr) (var51 Addr) (var52 Heap) (var53 Heap) (var54 Int) (var55 Addr) (var56 Addr) (var57 Addr) (var58 Addr) (var59 Addr) (var60 Addr) (var61 Addr) (var62 Addr) (var63 Addr) (var64 Addr) (var65 Addr) (var66 Addr) (var67 Addr) (var68 Heap) (var69 Heap) (var70 Int) (var71 Addr) (var72 Addr) (var73 Addr) (var74 Addr) (var75 Addr) (var76 Addr) (var77 Heap)) (or (not (and (inv_main_17 var77 var76 var75 var74 var73 var72 var71) (and (= var70 0) (and (and (and (and (and (and (and (and (and (and (= var69 var68) (= var67 var66)) (= var65 var64)) (= var63 var62)) (= var61 var60)) (= var59 var58)) (= var57 var56)) (= var55 (|sl_item::n2| (getsl_item (read var68 var60))))) (and (not (= var54 0)) (and (and (and (and (and (and (and (and (and (and (= var53 var52) (= var51 var50)) (= var49 var48)) (= var47 var46)) (= var45 var44)) (= var43 var42)) (= var41 var40)) (= var39 (|sl_item::n1| (getsl_item (read var52 var46))))) (and (and (and (and (and (and (and (and (= var52 (newHeap (alloc var38 (O_sl_item var37)))) (= var50 var36)) (= var48 var35)) (= var46 var34)) (= var44 var33)) (= var42 var32)) (= var31 var30)) (= var40 (newAddr (alloc var38 (O_sl_item var37))))) (and (and (= var29 0) (and (and (and (and (and (and (and (= var28 var77) (= var27 var76)) (= var26 var75)) (= var25 var74)) (= var24 var73)) (= var23 var72)) (= var22 var71)) (= var21 (|sl_item::n1| (getsl_item (read var77 var74)))))) (and (and (and (and (and (and (and (= var38 var28) (= var36 var27)) (= var35 var26)) (= var34 var25)) (= var33 var24)) (= var32 var23)) (= var30 var22)) (or (and (not (= var21 (|sl_item::n2| (getsl_item (read var28 var24))))) (= var29 1)) (and (= var21 (|sl_item::n2| (getsl_item (read var28 var24)))) (= var29 0))))))) (and (and (and (and (and (and (= var20 (write var53 var41 (O_sl_item (sl_item var39 (|sl_item::n2| (getsl_item (read var53 var41))) (|sl_item::n3| (getsl_item (read var53 var41))))))) (= var19 var51)) (= var18 var49)) (= var17 var47)) (= var16 var45)) (= var15 var43)) (= var14 var41))) (and (and (and (and (and (and (= var68 (write var20 var17 (O_sl_item (sl_item var14 (|sl_item::n2| (getsl_item (read var20 var17))) (|sl_item::n3| (getsl_item (read var20 var17))))))) (= var66 var19)) (= var64 var18)) (= var62 var17)) (= var60 var16)) (= var58 var15)) (= var56 var14))))) (and (and (and (and (and (and (= var13 (write var69 var57 (O_sl_item (sl_item (|sl_item::n1| (getsl_item (read var69 var57))) var55 (|sl_item::n3| (getsl_item (read var69 var57))))))) (= var12 var67)) (= var11 var65)) (= var10 var63)) (= var9 var61)) (= var8 var59)) (= var7 var57))) (and (and (and (and (and (and (= var6 (write var13 var9 (O_sl_item (sl_item (|sl_item::n1| (getsl_item (read var13 var9))) var7 (|sl_item::n3| (getsl_item (read var13 var9))))))) (= var5 var12)) (= var4 var11)) (= var3 var10)) (= var2 var9)) (= var1 var8)) (= var0 var7)))))) (inv_main581_2_4 var6 var5))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Heap) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Heap) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Addr) (var25 Addr) (var26 Addr) (var27 Addr) (var28 Heap) (var29 Int) (var30 Int) (var31 Addr) (var32 Addr) (var33 Addr) (var34 Addr) (var35 Addr) (var36 Addr) (var37 Addr) (var38 sl_item) (var39 Heap) (var40 Addr) (var41 Addr) (var42 Addr) (var43 Addr) (var44 Addr) (var45 Addr) (var46 Addr) (var47 Addr) (var48 Addr) (var49 Addr) (var50 Addr) (var51 Addr) (var52 Addr) (var53 Heap) (var54 Heap) (var55 Int) (var56 Addr) (var57 Addr) (var58 Addr) (var59 Addr) (var60 Addr) (var61 Addr) (var62 Addr) (var63 Addr) (var64 Addr) (var65 Addr) (var66 Addr) (var67 Addr) (var68 Addr) (var69 Heap) (var70 Heap) (var71 Int) (var72 Addr) (var73 Addr) (var74 Addr) (var75 Addr) (var76 Addr) (var77 Addr) (var78 Heap)) (or (not (and (inv_main_17 var78 var77 var76 var75 var74 var73 var72) (and (= var71 0) (and (and (and (and (and (and (and (and (and (and (= var70 var69) (= var68 var67)) (= var66 var65)) (= var64 var63)) (= var62 var61)) (= var60 var59)) (= var58 var57)) (= var56 (|sl_item::n2| (getsl_item (read var69 var61))))) (and (not (= var55 0)) (and (and (and (and (and (and (and (and (and (and (= var54 var53) (= var52 var51)) (= var50 var49)) (= var48 var47)) (= var46 var45)) (= var44 var43)) (= var42 var41)) (= var40 (|sl_item::n1| (getsl_item (read var53 var47))))) (and (and (and (and (and (and (and (and (= var53 (newHeap (alloc var39 (O_sl_item var38)))) (= var51 var37)) (= var49 var36)) (= var47 var35)) (= var45 var34)) (= var43 var33)) (= var32 var31)) (= var41 (newAddr (alloc var39 (O_sl_item var38))))) (and (= var30 0) (and (and (not (= var29 0)) (and (and (and (and (and (and (and (= var28 var78) (= var27 var77)) (= var26 var76)) (= var25 var75)) (= var24 var74)) (= var23 var73)) (= var22 var72)) (= var21 (|sl_item::n1| (getsl_item (read var78 var75)))))) (and (and (and (and (and (and (and (= var39 var28) (= var37 var27)) (= var36 var26)) (= var35 var25)) (= var34 var24)) (= var33 var23)) (= var31 var22)) (or (and (not (= var21 (|sl_item::n2| (getsl_item (read var28 var24))))) (= var29 1)) (and (= var21 (|sl_item::n2| (getsl_item (read var28 var24)))) (= var29 0)))))))) (and (and (and (and (and (and (= var20 (write var54 var42 (O_sl_item (sl_item var40 (|sl_item::n2| (getsl_item (read var54 var42))) (|sl_item::n3| (getsl_item (read var54 var42))))))) (= var19 var52)) (= var18 var50)) (= var17 var48)) (= var16 var46)) (= var15 var44)) (= var14 var42))) (and (and (and (and (and (and (= var69 (write var20 var17 (O_sl_item (sl_item var14 (|sl_item::n2| (getsl_item (read var20 var17))) (|sl_item::n3| (getsl_item (read var20 var17))))))) (= var67 var19)) (= var65 var18)) (= var63 var17)) (= var61 var16)) (= var59 var15)) (= var57 var14))))) (and (and (and (and (and (and (= var13 (write var70 var58 (O_sl_item (sl_item (|sl_item::n1| (getsl_item (read var70 var58))) var56 (|sl_item::n3| (getsl_item (read var70 var58))))))) (= var12 var68)) (= var11 var66)) (= var10 var64)) (= var9 var62)) (= var8 var60)) (= var7 var58))) (and (and (and (and (and (and (= var6 (write var13 var9 (O_sl_item (sl_item (|sl_item::n1| (getsl_item (read var13 var9))) var7 (|sl_item::n3| (getsl_item (read var13 var9))))))) (= var5 var12)) (= var4 var11)) (= var3 var10)) (= var2 var9)) (= var1 var8)) (= var0 var7)))))) (inv_main581_2_4 var6 var5))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Heap) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Heap) (var24 Addr) (var25 Addr) (var26 Addr) (var27 Addr) (var28 Addr) (var29 Addr) (var30 Addr) (var31 Heap) (var32 Int) (var33 Addr) (var34 Addr) (var35 Addr) (var36 Addr) (var37 Addr) (var38 Addr) (var39 Addr) (var40 sl_item) (var41 Heap) (var42 Addr) (var43 Addr) (var44 Addr) (var45 Addr) (var46 Addr) (var47 Addr) (var48 Addr) (var49 Addr) (var50 Addr) (var51 Addr) (var52 Addr) (var53 Addr) (var54 Addr) (var55 Heap) (var56 Heap) (var57 Int) (var58 Addr) (var59 Addr) (var60 Addr) (var61 Addr) (var62 Addr) (var63 Addr) (var64 Addr) (var65 Addr) (var66 Addr) (var67 Addr) (var68 Addr) (var69 Addr) (var70 Addr) (var71 Heap) (var72 Heap) (var73 Int) (var74 Addr) (var75 Addr) (var76 Addr) (var77 Addr) (var78 Addr) (var79 Addr) (var80 Addr) (var81 Addr) (var82 Addr) (var83 Addr) (var84 Addr) (var85 Addr) (var86 Addr) (var87 Heap) (var88 Heap) (var89 Addr) (var90 Addr) (var91 Addr) (var92 Addr) (var93 Addr) (var94 Addr) (var95 Heap)) (or (not (and (inv_main_17 var95 var94 var93 var92 var91 var90 var89) (and (and (and (and (and (and (and (and (and (and (= var88 var87) (= var86 var85)) (= var84 var83)) (= var82 var81)) (= var80 var79)) (= var78 var77)) (= var76 var75)) (= var74 (|sl_item::n3| (getsl_item (read var87 var77))))) (and (not (= var73 0)) (and (and (and (and (and (and (and (and (and (and (= var72 var71) (= var70 var69)) (= var68 var67)) (= var66 var65)) (= var64 var63)) (= var62 var61)) (= var60 var59)) (= var58 (|sl_item::n2| (getsl_item (read var71 var63))))) (and (not (= var57 0)) (and (and (and (and (and (and (and (and (and (and (= var56 var55) (= var54 var53)) (= var52 var51)) (= var50 var49)) (= var48 var47)) (= var46 var45)) (= var44 var43)) (= var42 (|sl_item::n1| (getsl_item (read var55 var49))))) (and (and (and (and (and (and (and (and (= var55 (newHeap (alloc var41 (O_sl_item var40)))) (= var53 var39)) (= var51 var38)) (= var49 var37)) (= var47 var36)) (= var45 var35)) (= var34 var33)) (= var43 (newAddr (alloc var41 (O_sl_item var40))))) (and (and (= var32 0) (and (and (and (and (and (and (and (= var31 var95) (= var30 var94)) (= var29 var93)) (= var28 var92)) (= var27 var91)) (= var26 var90)) (= var25 var89)) (= var24 (|sl_item::n1| (getsl_item (read var95 var92)))))) (and (and (and (and (and (and (and (= var41 var31) (= var39 var30)) (= var38 var29)) (= var37 var28)) (= var36 var27)) (= var35 var26)) (= var33 var25)) (or (and (not (= var24 (|sl_item::n2| (getsl_item (read var31 var27))))) (= var32 1)) (and (= var24 (|sl_item::n2| (getsl_item (read var31 var27)))) (= var32 0))))))) (and (and (and (and (and (and (= var23 (write var56 var44 (O_sl_item (sl_item var42 (|sl_item::n2| (getsl_item (read var56 var44))) (|sl_item::n3| (getsl_item (read var56 var44))))))) (= var22 var54)) (= var21 var52)) (= var20 var50)) (= var19 var48)) (= var18 var46)) (= var17 var44))) (and (and (and (and (and (and (= var71 (write var23 var20 (O_sl_item (sl_item var17 (|sl_item::n2| (getsl_item (read var23 var20))) (|sl_item::n3| (getsl_item (read var23 var20))))))) (= var69 var22)) (= var67 var21)) (= var65 var20)) (= var63 var19)) (= var61 var18)) (= var59 var17))))) (and (and (and (and (and (and (= var16 (write var72 var60 (O_sl_item (sl_item (|sl_item::n1| (getsl_item (read var72 var60))) var58 (|sl_item::n3| (getsl_item (read var72 var60))))))) (= var15 var70)) (= var14 var68)) (= var13 var66)) (= var12 var64)) (= var11 var62)) (= var10 var60))) (and (and (and (and (and (and (= var87 (write var16 var12 (O_sl_item (sl_item (|sl_item::n1| (getsl_item (read var16 var12))) var10 (|sl_item::n3| (getsl_item (read var16 var12))))))) (= var85 var15)) (= var83 var14)) (= var81 var13)) (= var79 var12)) (= var77 var11)) (= var75 var10))))) (and (and (and (and (and (and (= var9 (write var88 var76 (O_sl_item (sl_item (|sl_item::n1| (getsl_item (read var88 var76))) (|sl_item::n2| (getsl_item (read var88 var76))) var74)))) (= var8 var86)) (= var7 var84)) (= var6 var82)) (= var5 var80)) (= var4 var78)) (= var3 var76))) (and (and (= var2 (write var9 var4 (O_sl_item (sl_item (|sl_item::n1| (getsl_item (read var9 var4))) (|sl_item::n2| (getsl_item (read var9 var4))) var3)))) (= var1 var8)) (= var0 var7))))) (inv_main581_2_4 var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Heap) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Heap) (var24 Addr) (var25 Addr) (var26 Addr) (var27 Addr) (var28 Addr) (var29 Addr) (var30 Addr) (var31 Heap) (var32 Int) (var33 Int) (var34 Addr) (var35 Addr) (var36 Addr) (var37 Addr) (var38 Addr) (var39 Addr) (var40 Addr) (var41 sl_item) (var42 Heap) (var43 Addr) (var44 Addr) (var45 Addr) (var46 Addr) (var47 Addr) (var48 Addr) (var49 Addr) (var50 Addr) (var51 Addr) (var52 Addr) (var53 Addr) (var54 Addr) (var55 Addr) (var56 Heap) (var57 Heap) (var58 Int) (var59 Addr) (var60 Addr) (var61 Addr) (var62 Addr) (var63 Addr) (var64 Addr) (var65 Addr) (var66 Addr) (var67 Addr) (var68 Addr) (var69 Addr) (var70 Addr) (var71 Addr) (var72 Heap) (var73 Heap) (var74 Int) (var75 Addr) (var76 Addr) (var77 Addr) (var78 Addr) (var79 Addr) (var80 Addr) (var81 Addr) (var82 Addr) (var83 Addr) (var84 Addr) (var85 Addr) (var86 Addr) (var87 Addr) (var88 Heap) (var89 Heap) (var90 Addr) (var91 Addr) (var92 Addr) (var93 Addr) (var94 Addr) (var95 Addr) (var96 Heap)) (or (not (and (inv_main_17 var96 var95 var94 var93 var92 var91 var90) (and (and (and (and (and (and (and (and (and (and (= var89 var88) (= var87 var86)) (= var85 var84)) (= var83 var82)) (= var81 var80)) (= var79 var78)) (= var77 var76)) (= var75 (|sl_item::n3| (getsl_item (read var88 var78))))) (and (not (= var74 0)) (and (and (and (and (and (and (and (and (and (and (= var73 var72) (= var71 var70)) (= var69 var68)) (= var67 var66)) (= var65 var64)) (= var63 var62)) (= var61 var60)) (= var59 (|sl_item::n2| (getsl_item (read var72 var64))))) (and (not (= var58 0)) (and (and (and (and (and (and (and (and (and (and (= var57 var56) (= var55 var54)) (= var53 var52)) (= var51 var50)) (= var49 var48)) (= var47 var46)) (= var45 var44)) (= var43 (|sl_item::n1| (getsl_item (read var56 var50))))) (and (and (and (and (and (and (and (and (= var56 (newHeap (alloc var42 (O_sl_item var41)))) (= var54 var40)) (= var52 var39)) (= var50 var38)) (= var48 var37)) (= var46 var36)) (= var35 var34)) (= var44 (newAddr (alloc var42 (O_sl_item var41))))) (and (= var33 0) (and (and (not (= var32 0)) (and (and (and (and (and (and (and (= var31 var96) (= var30 var95)) (= var29 var94)) (= var28 var93)) (= var27 var92)) (= var26 var91)) (= var25 var90)) (= var24 (|sl_item::n1| (getsl_item (read var96 var93)))))) (and (and (and (and (and (and (and (= var42 var31) (= var40 var30)) (= var39 var29)) (= var38 var28)) (= var37 var27)) (= var36 var26)) (= var34 var25)) (or (and (not (= var24 (|sl_item::n2| (getsl_item (read var31 var27))))) (= var32 1)) (and (= var24 (|sl_item::n2| (getsl_item (read var31 var27)))) (= var32 0)))))))) (and (and (and (and (and (and (= var23 (write var57 var45 (O_sl_item (sl_item var43 (|sl_item::n2| (getsl_item (read var57 var45))) (|sl_item::n3| (getsl_item (read var57 var45))))))) (= var22 var55)) (= var21 var53)) (= var20 var51)) (= var19 var49)) (= var18 var47)) (= var17 var45))) (and (and (and (and (and (and (= var72 (write var23 var20 (O_sl_item (sl_item var17 (|sl_item::n2| (getsl_item (read var23 var20))) (|sl_item::n3| (getsl_item (read var23 var20))))))) (= var70 var22)) (= var68 var21)) (= var66 var20)) (= var64 var19)) (= var62 var18)) (= var60 var17))))) (and (and (and (and (and (and (= var16 (write var73 var61 (O_sl_item (sl_item (|sl_item::n1| (getsl_item (read var73 var61))) var59 (|sl_item::n3| (getsl_item (read var73 var61))))))) (= var15 var71)) (= var14 var69)) (= var13 var67)) (= var12 var65)) (= var11 var63)) (= var10 var61))) (and (and (and (and (and (and (= var88 (write var16 var12 (O_sl_item (sl_item (|sl_item::n1| (getsl_item (read var16 var12))) var10 (|sl_item::n3| (getsl_item (read var16 var12))))))) (= var86 var15)) (= var84 var14)) (= var82 var13)) (= var80 var12)) (= var78 var11)) (= var76 var10))))) (and (and (and (and (and (and (= var9 (write var89 var77 (O_sl_item (sl_item (|sl_item::n1| (getsl_item (read var89 var77))) (|sl_item::n2| (getsl_item (read var89 var77))) var75)))) (= var8 var87)) (= var7 var85)) (= var6 var83)) (= var5 var81)) (= var4 var79)) (= var3 var77))) (and (and (= var2 (write var9 var4 (O_sl_item (sl_item (|sl_item::n1| (getsl_item (read var9 var4))) (|sl_item::n2| (getsl_item (read var9 var4))) var3)))) (= var1 var8)) (= var0 var7))))) (inv_main581_2_4 var2 var1))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 sl) (var3 Addr) (var4 Addr) (var5 Addr) (var6 sl_item) (var7 Heap) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Addr) (var12 sl_item) (var13 Heap) (var14 Heap) (var15 Addr) (var16 Addr) (var17 Heap) (var18 Addr) (var19 Addr) (var20 Heap) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Heap) (var25 Heap) (var26 Addr) (var27 Addr) (var28 Heap) (var29 Addr) (var30 Addr) (var31 Addr) (var32 Heap) (var33 Heap) (var34 Heap)) (or (not (and (inv_main581_2 var34) (and (and (and (and (and (and (= var33 (write var32 (|sl::tail| (getsl (read var32 var31))) (O_sl_item (sl_item nullAddr (|sl_item::n2| (getsl_item (read var32 (|sl::tail| (getsl (read var32 var31)))))) (|sl_item::n3| (getsl_item (read var32 (|sl::tail| (getsl (read var32 var31)))))))))) (= var30 var31)) (= var29 nullAddr)) (and (and (= var28 (write var33 (|sl::tail| (getsl (read var33 var30))) (O_sl_item (sl_item (|sl_item::n1| (getsl_item (read var33 (|sl::tail| (getsl (read var33 var30)))))) var29 (|sl_item::n3| (getsl_item (read var33 (|sl::tail| (getsl (read var33 var30)))))))))) (= var27 var30)) (= var26 var29))) (and (and (and (and (and (and (= var25 var24) (= var23 var22)) (= var21 (|sl::tail| (getsl (read var24 var22))))) (and (and (= var20 (write var25 (|sl::head| (getsl (read var25 var23))) (O_sl_item (sl_item var21 (|sl_item::n2| (getsl_item (read var25 (|sl::head| (getsl (read var25 var23)))))) (|sl_item::n3| (getsl_item (read var25 (|sl::head| (getsl (read var25 var23)))))))))) (= var19 var23)) (= var18 var21))) (and (and (= var17 (write var20 (|sl::head| (getsl (read var20 var19))) (O_sl_item (sl_item (|sl_item::n1| (getsl_item (read var20 (|sl::head| (getsl (read var20 var19)))))) var18 (|sl_item::n3| (getsl_item (read var20 (|sl::head| (getsl (read var20 var19)))))))))) (= var16 var19)) (= var15 var18))) (and (and (and (and (= var14 (newHeap (alloc var13 (O_sl_item var12)))) (= var11 var10)) (= var9 (newAddr (alloc var13 (O_sl_item var12))))) (and (and (and (= var8 (newHeap (alloc var7 (O_sl_item var6)))) (= var5 var4)) (= var3 (newAddr (alloc var7 (O_sl_item var6))))) (and (= var7 (newHeap (alloc var34 (O_sl var2)))) (= var4 (newAddr (alloc var34 (O_sl var2))))))) (and (= var13 (write var8 var5 (O_sl (sl var3 (|sl::tail| (getsl (read var8 var5))))))) (= var10 var5)))) (and (= var24 (write var14 var11 (O_sl (sl (|sl::head| (getsl (read var14 var11))) var9)))) (= var22 var11)))) (and (= var32 (write var17 (|sl::head| (getsl (read var17 var16))) (O_sl_item (sl_item (|sl_item::n1| (getsl_item (read var17 (|sl::head| (getsl (read var17 var16)))))) (|sl_item::n2| (getsl_item (read var17 (|sl::head| (getsl (read var17 var16)))))) var15)))) (= var31 var16))) (and (= var1 (write var28 (|sl::tail| (getsl (read var28 var27))) (O_sl_item (sl_item (|sl_item::n1| (getsl_item (read var28 (|sl::tail| (getsl (read var28 var27)))))) (|sl_item::n2| (getsl_item (read var28 (|sl::tail| (getsl (read var28 var27)))))) var26)))) (= var0 var27))))) (inv_main581_2_4 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_36 var3 var2 var1 var0) (and (not (= var0 nullAddr)) (= (read var3 var0) defObj))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_33 var3 var2 var1 var0) (and (not (= var1 nullAddr)) (= (read var3 var1) defObj))))))
(check-sat)
