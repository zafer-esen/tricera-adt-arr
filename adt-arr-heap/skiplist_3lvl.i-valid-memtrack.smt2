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
(declare-fun inv_main571_2 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main581_2 (Heap Addr) Bool)
(declare-fun inv_main581_2_4 (Heap Addr Addr) Bool)
(declare-fun inv_main585_9 (Heap Addr Int) Bool)
(declare-fun inv_main_12 (Heap Addr Addr Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main_17 (Heap Addr Addr Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main_7 (Heap Addr Addr Addr Addr Addr Addr Addr) Bool)
(assert (forall ((var0 Addr) (var1 Heap)) (or (not (and (= var1 emptyHeap) (= var0 nullAddr))) (inv_main581_2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Heap) (var17 Int) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Addr) (var25 Heap)) (or (not (and (inv_main_7 var25 var24 var23 var22 var21 var20 var19 var18) (and (and (= var17 0) (and (and (and (and (and (and (and (and (= var16 var25) (= var15 var24)) (= var14 var23)) (= var13 var22)) (= var12 var21)) (= var11 var20)) (= var10 var19)) (= var9 var18)) (= var8 (|sl_item::n3| (getsl_item (read var25 var19)))))) (and (and (and (and (and (and (and (and (= var7 var16) (= var6 var15)) (= var5 var14)) (= var4 var13)) (= var3 var12)) (= var2 var11)) (= var1 var10)) (= var0 var9)) (or (and (not (= var8 (|sl::tail| (getsl (read var16 var13))))) (= var17 1)) (and (= var8 (|sl::tail| (getsl (read var16 var13)))) (= var17 0))))))) (inv_main_12 var7 var6 var5 var4 var3 var1 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Heap) (var17 Int) (var18 Int) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Addr) (var25 Addr) (var26 Heap)) (or (not (and (inv_main_7 var26 var25 var24 var23 var22 var21 var20 var19) (and (= var18 0) (and (and (not (= var17 0)) (and (and (and (and (and (and (and (and (= var16 var26) (= var15 var25)) (= var14 var24)) (= var13 var23)) (= var12 var22)) (= var11 var21)) (= var10 var20)) (= var9 var19)) (= var8 (|sl_item::n3| (getsl_item (read var26 var20)))))) (and (and (and (and (and (and (and (and (= var7 var16) (= var6 var15)) (= var5 var14)) (= var4 var13)) (= var3 var12)) (= var2 var11)) (= var1 var10)) (= var0 var9)) (or (and (not (= var8 (|sl::tail| (getsl (read var16 var13))))) (= var17 1)) (and (= var8 (|sl::tail| (getsl (read var16 var13)))) (= var17 0)))))))) (inv_main_12 var7 var6 var5 var4 var3 var1 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap) (var9 Int) (var10 Int) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Addr) (var25 Addr) (var26 Heap) (var27 Heap) (var28 Addr) (var29 Addr) (var30 Addr) (var31 Addr) (var32 Addr) (var33 Addr) (var34 Addr) (var35 Heap)) (or (not (and (inv_main_12 var35 var34 var33 var32 var31 var30 var29 var28) (and (and (and (and (and (and (and (and (and (= var27 var26) (= var25 var24)) (= var23 var22)) (= var21 var20)) (= var19 var18)) (= var17 var16)) (= var15 var14)) (= var13 var12)) (= var11 (|sl_item::n2| (getsl_item (read var26 var16))))) (and (not (= var10 0)) (and (and (not (= var9 0)) (and (and (and (and (and (and (and (and (= var8 var35) (= var7 var34)) (= var6 var33)) (= var5 var32)) (= var4 var31)) (= var3 var30)) (= var2 var29)) (= var1 var28)) (= var0 (|sl_item::n2| (getsl_item (read var35 var30)))))) (and (and (and (and (and (and (and (and (= var26 var8) (= var24 var7)) (= var22 var6)) (= var20 var5)) (= var18 var4)) (= var16 var3)) (= var14 var2)) (= var12 var1)) (or (and (not (= var0 (|sl_item::n3| (getsl_item (read var8 var2))))) (= var9 1)) (and (= var0 (|sl_item::n3| (getsl_item (read var8 var2)))) (= var9 0))))))))) (inv_main_12 var27 var25 var23 var21 var19 var11 var15 var13))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Heap) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Heap) (var25 Int) (var26 Addr) (var27 Addr) (var28 Addr) (var29 Addr) (var30 Addr) (var31 Addr) (var32 Addr) (var33 Addr) (var34 Bool) (var35 sl_item) (var36 Heap) (var37 Addr) (var38 Addr) (var39 Addr) (var40 Addr) (var41 Addr) (var42 Addr) (var43 Addr) (var44 Addr) (var45 Addr) (var46 Addr) (var47 Addr) (var48 Addr) (var49 Addr) (var50 Addr) (var51 Addr) (var52 Heap) (var53 Heap) (var54 Int) (var55 Addr) (var56 Addr) (var57 Addr) (var58 Addr) (var59 Addr) (var60 Addr) (var61 Addr) (var62 Heap)) (or (not (and (inv_main_17 var62 var61 var60 var59 var58 var57 var56 var55) (and (= var54 0) (and (and (and (and (and (and (and (and (and (and (and (= var53 var52) (= var51 var50)) (= var49 var48)) (= var47 var46)) (= var45 var44)) (= var43 var42)) (= var41 var40)) (= var39 var38)) (= var37 (|sl_item::n1| (getsl_item (read var52 var44))))) (and (and (and (and (and (and (and (and (and (= var52 (newHeap (alloc var36 (O_sl_item var35)))) (or (and var34 (= var50 (newAddr (alloc var36 (O_sl_item var35))))) (and (not var34) (= var50 var33)))) (= var48 var32)) (= var46 var31)) (= var44 var30)) (= var42 var29)) (= var40 var28)) (= var27 var26)) (= var38 (newAddr (alloc var36 (O_sl_item var35))))) (and (and (= var25 0) (and (and (and (and (and (and (and (and (= var24 var62) (= var23 var61)) (= var22 var60)) (= var21 var59)) (= var20 var58)) (= var19 var57)) (= var18 var56)) (= var17 var55)) (= var16 (|sl_item::n1| (getsl_item (read var62 var58)))))) (and (and (and (and (and (and (and (and (= var36 var24) (= var33 var23)) (= var32 var22)) (= var31 var21)) (= var30 var20)) (= var29 var19)) (= var28 var18)) (= var26 var17)) (or (and (not (= var16 (|sl_item::n2| (getsl_item (read var24 var19))))) (= var25 1)) (and (= var16 (|sl_item::n2| (getsl_item (read var24 var19)))) (= var25 0))))))) (and (and (and (and (and (and (and (= var15 (write var53 var39 (O_sl_item (sl_item var37 (|sl_item::n2| (getsl_item (read var53 var39))) (|sl_item::n3| (getsl_item (read var53 var39))))))) (= var14 var51)) (= var13 var49)) (= var12 var47)) (= var11 var45)) (= var10 var43)) (= var9 var41)) (= var8 var39))) (and (and (and (and (and (and (and (= var7 (write var15 var11 (O_sl_item (sl_item var8 (|sl_item::n2| (getsl_item (read var15 var11))) (|sl_item::n3| (getsl_item (read var15 var11))))))) (= var6 var14)) (= var5 var13)) (= var4 var12)) (= var3 var11)) (= var2 var10)) (= var1 var9)) (= var0 var8)))))) (inv_main581_2_4 var7 var6 var5))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Heap) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Heap) (var25 Int) (var26 Int) (var27 Addr) (var28 Addr) (var29 Addr) (var30 Addr) (var31 Addr) (var32 Addr) (var33 Addr) (var34 Addr) (var35 Bool) (var36 sl_item) (var37 Heap) (var38 Addr) (var39 Addr) (var40 Addr) (var41 Addr) (var42 Addr) (var43 Addr) (var44 Addr) (var45 Addr) (var46 Addr) (var47 Addr) (var48 Addr) (var49 Addr) (var50 Addr) (var51 Addr) (var52 Addr) (var53 Heap) (var54 Heap) (var55 Int) (var56 Addr) (var57 Addr) (var58 Addr) (var59 Addr) (var60 Addr) (var61 Addr) (var62 Addr) (var63 Heap)) (or (not (and (inv_main_17 var63 var62 var61 var60 var59 var58 var57 var56) (and (= var55 0) (and (and (and (and (and (and (and (and (and (and (and (= var54 var53) (= var52 var51)) (= var50 var49)) (= var48 var47)) (= var46 var45)) (= var44 var43)) (= var42 var41)) (= var40 var39)) (= var38 (|sl_item::n1| (getsl_item (read var53 var45))))) (and (and (and (and (and (and (and (and (and (= var53 (newHeap (alloc var37 (O_sl_item var36)))) (or (and var35 (= var51 (newAddr (alloc var37 (O_sl_item var36))))) (and (not var35) (= var51 var34)))) (= var49 var33)) (= var47 var32)) (= var45 var31)) (= var43 var30)) (= var41 var29)) (= var28 var27)) (= var39 (newAddr (alloc var37 (O_sl_item var36))))) (and (= var26 0) (and (and (not (= var25 0)) (and (and (and (and (and (and (and (and (= var24 var63) (= var23 var62)) (= var22 var61)) (= var21 var60)) (= var20 var59)) (= var19 var58)) (= var18 var57)) (= var17 var56)) (= var16 (|sl_item::n1| (getsl_item (read var63 var59)))))) (and (and (and (and (and (and (and (and (= var37 var24) (= var34 var23)) (= var33 var22)) (= var32 var21)) (= var31 var20)) (= var30 var19)) (= var29 var18)) (= var27 var17)) (or (and (not (= var16 (|sl_item::n2| (getsl_item (read var24 var19))))) (= var25 1)) (and (= var16 (|sl_item::n2| (getsl_item (read var24 var19)))) (= var25 0)))))))) (and (and (and (and (and (and (and (= var15 (write var54 var40 (O_sl_item (sl_item var38 (|sl_item::n2| (getsl_item (read var54 var40))) (|sl_item::n3| (getsl_item (read var54 var40))))))) (= var14 var52)) (= var13 var50)) (= var12 var48)) (= var11 var46)) (= var10 var44)) (= var9 var42)) (= var8 var40))) (and (and (and (and (and (and (and (= var7 (write var15 var11 (O_sl_item (sl_item var8 (|sl_item::n2| (getsl_item (read var15 var11))) (|sl_item::n3| (getsl_item (read var15 var11))))))) (= var6 var14)) (= var5 var13)) (= var4 var12)) (= var3 var11)) (= var2 var10)) (= var1 var9)) (= var0 var8)))))) (inv_main581_2_4 var7 var6 var5))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Heap) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Heap) (var24 Addr) (var25 Addr) (var26 Addr) (var27 Addr) (var28 Addr) (var29 Addr) (var30 Addr) (var31 Addr) (var32 Heap) (var33 Int) (var34 Addr) (var35 Addr) (var36 Addr) (var37 Addr) (var38 Addr) (var39 Addr) (var40 Addr) (var41 Addr) (var42 Bool) (var43 sl_item) (var44 Heap) (var45 Addr) (var46 Addr) (var47 Addr) (var48 Addr) (var49 Addr) (var50 Addr) (var51 Addr) (var52 Addr) (var53 Addr) (var54 Addr) (var55 Addr) (var56 Addr) (var57 Addr) (var58 Addr) (var59 Addr) (var60 Heap) (var61 Heap) (var62 Int) (var63 Addr) (var64 Addr) (var65 Addr) (var66 Addr) (var67 Addr) (var68 Addr) (var69 Addr) (var70 Addr) (var71 Addr) (var72 Addr) (var73 Addr) (var74 Addr) (var75 Addr) (var76 Addr) (var77 Addr) (var78 Heap) (var79 Heap) (var80 Int) (var81 Addr) (var82 Addr) (var83 Addr) (var84 Addr) (var85 Addr) (var86 Addr) (var87 Addr) (var88 Heap)) (or (not (and (inv_main_17 var88 var87 var86 var85 var84 var83 var82 var81) (and (= var80 0) (and (and (and (and (and (and (and (and (and (and (and (= var79 var78) (= var77 var76)) (= var75 var74)) (= var73 var72)) (= var71 var70)) (= var69 var68)) (= var67 var66)) (= var65 var64)) (= var63 (|sl_item::n2| (getsl_item (read var78 var68))))) (and (not (= var62 0)) (and (and (and (and (and (and (and (and (and (and (and (= var61 var60) (= var59 var58)) (= var57 var56)) (= var55 var54)) (= var53 var52)) (= var51 var50)) (= var49 var48)) (= var47 var46)) (= var45 (|sl_item::n1| (getsl_item (read var60 var52))))) (and (and (and (and (and (and (and (and (and (= var60 (newHeap (alloc var44 (O_sl_item var43)))) (or (and var42 (= var58 (newAddr (alloc var44 (O_sl_item var43))))) (and (not var42) (= var58 var41)))) (= var56 var40)) (= var54 var39)) (= var52 var38)) (= var50 var37)) (= var48 var36)) (= var35 var34)) (= var46 (newAddr (alloc var44 (O_sl_item var43))))) (and (and (= var33 0) (and (and (and (and (and (and (and (and (= var32 var88) (= var31 var87)) (= var30 var86)) (= var29 var85)) (= var28 var84)) (= var27 var83)) (= var26 var82)) (= var25 var81)) (= var24 (|sl_item::n1| (getsl_item (read var88 var84)))))) (and (and (and (and (and (and (and (and (= var44 var32) (= var41 var31)) (= var40 var30)) (= var39 var29)) (= var38 var28)) (= var37 var27)) (= var36 var26)) (= var34 var25)) (or (and (not (= var24 (|sl_item::n2| (getsl_item (read var32 var27))))) (= var33 1)) (and (= var24 (|sl_item::n2| (getsl_item (read var32 var27)))) (= var33 0))))))) (and (and (and (and (and (and (and (= var23 (write var61 var47 (O_sl_item (sl_item var45 (|sl_item::n2| (getsl_item (read var61 var47))) (|sl_item::n3| (getsl_item (read var61 var47))))))) (= var22 var59)) (= var21 var57)) (= var20 var55)) (= var19 var53)) (= var18 var51)) (= var17 var49)) (= var16 var47))) (and (and (and (and (and (and (and (= var78 (write var23 var19 (O_sl_item (sl_item var16 (|sl_item::n2| (getsl_item (read var23 var19))) (|sl_item::n3| (getsl_item (read var23 var19))))))) (= var76 var22)) (= var74 var21)) (= var72 var20)) (= var70 var19)) (= var68 var18)) (= var66 var17)) (= var64 var16))))) (and (and (and (and (and (and (and (= var15 (write var79 var65 (O_sl_item (sl_item (|sl_item::n1| (getsl_item (read var79 var65))) var63 (|sl_item::n3| (getsl_item (read var79 var65))))))) (= var14 var77)) (= var13 var75)) (= var12 var73)) (= var11 var71)) (= var10 var69)) (= var9 var67)) (= var8 var65))) (and (and (and (and (and (and (and (= var7 (write var15 var10 (O_sl_item (sl_item (|sl_item::n1| (getsl_item (read var15 var10))) var8 (|sl_item::n3| (getsl_item (read var15 var10))))))) (= var6 var14)) (= var5 var13)) (= var4 var12)) (= var3 var11)) (= var2 var10)) (= var1 var9)) (= var0 var8)))))) (inv_main581_2_4 var7 var6 var5))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Heap) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Heap) (var24 Addr) (var25 Addr) (var26 Addr) (var27 Addr) (var28 Addr) (var29 Addr) (var30 Addr) (var31 Addr) (var32 Heap) (var33 Int) (var34 Int) (var35 Addr) (var36 Addr) (var37 Addr) (var38 Addr) (var39 Addr) (var40 Addr) (var41 Addr) (var42 Addr) (var43 Bool) (var44 sl_item) (var45 Heap) (var46 Addr) (var47 Addr) (var48 Addr) (var49 Addr) (var50 Addr) (var51 Addr) (var52 Addr) (var53 Addr) (var54 Addr) (var55 Addr) (var56 Addr) (var57 Addr) (var58 Addr) (var59 Addr) (var60 Addr) (var61 Heap) (var62 Heap) (var63 Int) (var64 Addr) (var65 Addr) (var66 Addr) (var67 Addr) (var68 Addr) (var69 Addr) (var70 Addr) (var71 Addr) (var72 Addr) (var73 Addr) (var74 Addr) (var75 Addr) (var76 Addr) (var77 Addr) (var78 Addr) (var79 Heap) (var80 Heap) (var81 Int) (var82 Addr) (var83 Addr) (var84 Addr) (var85 Addr) (var86 Addr) (var87 Addr) (var88 Addr) (var89 Heap)) (or (not (and (inv_main_17 var89 var88 var87 var86 var85 var84 var83 var82) (and (= var81 0) (and (and (and (and (and (and (and (and (and (and (and (= var80 var79) (= var78 var77)) (= var76 var75)) (= var74 var73)) (= var72 var71)) (= var70 var69)) (= var68 var67)) (= var66 var65)) (= var64 (|sl_item::n2| (getsl_item (read var79 var69))))) (and (not (= var63 0)) (and (and (and (and (and (and (and (and (and (and (and (= var62 var61) (= var60 var59)) (= var58 var57)) (= var56 var55)) (= var54 var53)) (= var52 var51)) (= var50 var49)) (= var48 var47)) (= var46 (|sl_item::n1| (getsl_item (read var61 var53))))) (and (and (and (and (and (and (and (and (and (= var61 (newHeap (alloc var45 (O_sl_item var44)))) (or (and var43 (= var59 (newAddr (alloc var45 (O_sl_item var44))))) (and (not var43) (= var59 var42)))) (= var57 var41)) (= var55 var40)) (= var53 var39)) (= var51 var38)) (= var49 var37)) (= var36 var35)) (= var47 (newAddr (alloc var45 (O_sl_item var44))))) (and (= var34 0) (and (and (not (= var33 0)) (and (and (and (and (and (and (and (and (= var32 var89) (= var31 var88)) (= var30 var87)) (= var29 var86)) (= var28 var85)) (= var27 var84)) (= var26 var83)) (= var25 var82)) (= var24 (|sl_item::n1| (getsl_item (read var89 var85)))))) (and (and (and (and (and (and (and (and (= var45 var32) (= var42 var31)) (= var41 var30)) (= var40 var29)) (= var39 var28)) (= var38 var27)) (= var37 var26)) (= var35 var25)) (or (and (not (= var24 (|sl_item::n2| (getsl_item (read var32 var27))))) (= var33 1)) (and (= var24 (|sl_item::n2| (getsl_item (read var32 var27)))) (= var33 0)))))))) (and (and (and (and (and (and (and (= var23 (write var62 var48 (O_sl_item (sl_item var46 (|sl_item::n2| (getsl_item (read var62 var48))) (|sl_item::n3| (getsl_item (read var62 var48))))))) (= var22 var60)) (= var21 var58)) (= var20 var56)) (= var19 var54)) (= var18 var52)) (= var17 var50)) (= var16 var48))) (and (and (and (and (and (and (and (= var79 (write var23 var19 (O_sl_item (sl_item var16 (|sl_item::n2| (getsl_item (read var23 var19))) (|sl_item::n3| (getsl_item (read var23 var19))))))) (= var77 var22)) (= var75 var21)) (= var73 var20)) (= var71 var19)) (= var69 var18)) (= var67 var17)) (= var65 var16))))) (and (and (and (and (and (and (and (= var15 (write var80 var66 (O_sl_item (sl_item (|sl_item::n1| (getsl_item (read var80 var66))) var64 (|sl_item::n3| (getsl_item (read var80 var66))))))) (= var14 var78)) (= var13 var76)) (= var12 var74)) (= var11 var72)) (= var10 var70)) (= var9 var68)) (= var8 var66))) (and (and (and (and (and (and (and (= var7 (write var15 var10 (O_sl_item (sl_item (|sl_item::n1| (getsl_item (read var15 var10))) var8 (|sl_item::n3| (getsl_item (read var15 var10))))))) (= var6 var14)) (= var5 var13)) (= var4 var12)) (= var3 var11)) (= var2 var10)) (= var1 var9)) (= var0 var8)))))) (inv_main581_2_4 var7 var6 var5))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Heap) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Heap) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Addr) (var25 Addr) (var26 Addr) (var27 Heap) (var28 Addr) (var29 Addr) (var30 Addr) (var31 Addr) (var32 Addr) (var33 Addr) (var34 Addr) (var35 Addr) (var36 Heap) (var37 Int) (var38 Addr) (var39 Addr) (var40 Addr) (var41 Addr) (var42 Addr) (var43 Addr) (var44 Addr) (var45 Addr) (var46 Bool) (var47 sl_item) (var48 Heap) (var49 Addr) (var50 Addr) (var51 Addr) (var52 Addr) (var53 Addr) (var54 Addr) (var55 Addr) (var56 Addr) (var57 Addr) (var58 Addr) (var59 Addr) (var60 Addr) (var61 Addr) (var62 Addr) (var63 Addr) (var64 Heap) (var65 Heap) (var66 Int) (var67 Addr) (var68 Addr) (var69 Addr) (var70 Addr) (var71 Addr) (var72 Addr) (var73 Addr) (var74 Addr) (var75 Addr) (var76 Addr) (var77 Addr) (var78 Addr) (var79 Addr) (var80 Addr) (var81 Addr) (var82 Heap) (var83 Heap) (var84 Int) (var85 Addr) (var86 Addr) (var87 Addr) (var88 Addr) (var89 Addr) (var90 Addr) (var91 Addr) (var92 Addr) (var93 Addr) (var94 Addr) (var95 Addr) (var96 Addr) (var97 Addr) (var98 Addr) (var99 Addr) (var100 Heap) (var101 Heap) (var102 Addr) (var103 Addr) (var104 Addr) (var105 Addr) (var106 Addr) (var107 Addr) (var108 Addr) (var109 Heap)) (or (not (and (inv_main_17 var109 var108 var107 var106 var105 var104 var103 var102) (and (and (and (and (and (and (and (and (and (and (and (= var101 var100) (= var99 var98)) (= var97 var96)) (= var95 var94)) (= var93 var92)) (= var91 var90)) (= var89 var88)) (= var87 var86)) (= var85 (|sl_item::n3| (getsl_item (read var100 var88))))) (and (not (= var84 0)) (and (and (and (and (and (and (and (and (and (and (and (= var83 var82) (= var81 var80)) (= var79 var78)) (= var77 var76)) (= var75 var74)) (= var73 var72)) (= var71 var70)) (= var69 var68)) (= var67 (|sl_item::n2| (getsl_item (read var82 var72))))) (and (not (= var66 0)) (and (and (and (and (and (and (and (and (and (and (and (= var65 var64) (= var63 var62)) (= var61 var60)) (= var59 var58)) (= var57 var56)) (= var55 var54)) (= var53 var52)) (= var51 var50)) (= var49 (|sl_item::n1| (getsl_item (read var64 var56))))) (and (and (and (and (and (and (and (and (and (= var64 (newHeap (alloc var48 (O_sl_item var47)))) (or (and var46 (= var62 (newAddr (alloc var48 (O_sl_item var47))))) (and (not var46) (= var62 var45)))) (= var60 var44)) (= var58 var43)) (= var56 var42)) (= var54 var41)) (= var52 var40)) (= var39 var38)) (= var50 (newAddr (alloc var48 (O_sl_item var47))))) (and (and (= var37 0) (and (and (and (and (and (and (and (and (= var36 var109) (= var35 var108)) (= var34 var107)) (= var33 var106)) (= var32 var105)) (= var31 var104)) (= var30 var103)) (= var29 var102)) (= var28 (|sl_item::n1| (getsl_item (read var109 var105)))))) (and (and (and (and (and (and (and (and (= var48 var36) (= var45 var35)) (= var44 var34)) (= var43 var33)) (= var42 var32)) (= var41 var31)) (= var40 var30)) (= var38 var29)) (or (and (not (= var28 (|sl_item::n2| (getsl_item (read var36 var31))))) (= var37 1)) (and (= var28 (|sl_item::n2| (getsl_item (read var36 var31)))) (= var37 0))))))) (and (and (and (and (and (and (and (= var27 (write var65 var51 (O_sl_item (sl_item var49 (|sl_item::n2| (getsl_item (read var65 var51))) (|sl_item::n3| (getsl_item (read var65 var51))))))) (= var26 var63)) (= var25 var61)) (= var24 var59)) (= var23 var57)) (= var22 var55)) (= var21 var53)) (= var20 var51))) (and (and (and (and (and (and (and (= var82 (write var27 var23 (O_sl_item (sl_item var20 (|sl_item::n2| (getsl_item (read var27 var23))) (|sl_item::n3| (getsl_item (read var27 var23))))))) (= var80 var26)) (= var78 var25)) (= var76 var24)) (= var74 var23)) (= var72 var22)) (= var70 var21)) (= var68 var20))))) (and (and (and (and (and (and (and (= var19 (write var83 var69 (O_sl_item (sl_item (|sl_item::n1| (getsl_item (read var83 var69))) var67 (|sl_item::n3| (getsl_item (read var83 var69))))))) (= var18 var81)) (= var17 var79)) (= var16 var77)) (= var15 var75)) (= var14 var73)) (= var13 var71)) (= var12 var69))) (and (and (and (and (and (and (and (= var100 (write var19 var14 (O_sl_item (sl_item (|sl_item::n1| (getsl_item (read var19 var14))) var12 (|sl_item::n3| (getsl_item (read var19 var14))))))) (= var98 var18)) (= var96 var17)) (= var94 var16)) (= var92 var15)) (= var90 var14)) (= var88 var13)) (= var86 var12))))) (and (and (and (and (and (and (and (= var11 (write var101 var87 (O_sl_item (sl_item (|sl_item::n1| (getsl_item (read var101 var87))) (|sl_item::n2| (getsl_item (read var101 var87))) var85)))) (= var10 var99)) (= var9 var97)) (= var8 var95)) (= var7 var93)) (= var6 var91)) (= var5 var89)) (= var4 var87))) (and (and (and (= var3 (write var11 var5 (O_sl_item (sl_item (|sl_item::n1| (getsl_item (read var11 var5))) (|sl_item::n2| (getsl_item (read var11 var5))) var4)))) (= var2 var10)) (= var1 var9)) (= var0 var8))))) (inv_main581_2_4 var3 var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Heap) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Heap) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Addr) (var25 Addr) (var26 Addr) (var27 Heap) (var28 Addr) (var29 Addr) (var30 Addr) (var31 Addr) (var32 Addr) (var33 Addr) (var34 Addr) (var35 Addr) (var36 Heap) (var37 Int) (var38 Int) (var39 Addr) (var40 Addr) (var41 Addr) (var42 Addr) (var43 Addr) (var44 Addr) (var45 Addr) (var46 Addr) (var47 Bool) (var48 sl_item) (var49 Heap) (var50 Addr) (var51 Addr) (var52 Addr) (var53 Addr) (var54 Addr) (var55 Addr) (var56 Addr) (var57 Addr) (var58 Addr) (var59 Addr) (var60 Addr) (var61 Addr) (var62 Addr) (var63 Addr) (var64 Addr) (var65 Heap) (var66 Heap) (var67 Int) (var68 Addr) (var69 Addr) (var70 Addr) (var71 Addr) (var72 Addr) (var73 Addr) (var74 Addr) (var75 Addr) (var76 Addr) (var77 Addr) (var78 Addr) (var79 Addr) (var80 Addr) (var81 Addr) (var82 Addr) (var83 Heap) (var84 Heap) (var85 Int) (var86 Addr) (var87 Addr) (var88 Addr) (var89 Addr) (var90 Addr) (var91 Addr) (var92 Addr) (var93 Addr) (var94 Addr) (var95 Addr) (var96 Addr) (var97 Addr) (var98 Addr) (var99 Addr) (var100 Addr) (var101 Heap) (var102 Heap) (var103 Addr) (var104 Addr) (var105 Addr) (var106 Addr) (var107 Addr) (var108 Addr) (var109 Addr) (var110 Heap)) (or (not (and (inv_main_17 var110 var109 var108 var107 var106 var105 var104 var103) (and (and (and (and (and (and (and (and (and (and (and (= var102 var101) (= var100 var99)) (= var98 var97)) (= var96 var95)) (= var94 var93)) (= var92 var91)) (= var90 var89)) (= var88 var87)) (= var86 (|sl_item::n3| (getsl_item (read var101 var89))))) (and (not (= var85 0)) (and (and (and (and (and (and (and (and (and (and (and (= var84 var83) (= var82 var81)) (= var80 var79)) (= var78 var77)) (= var76 var75)) (= var74 var73)) (= var72 var71)) (= var70 var69)) (= var68 (|sl_item::n2| (getsl_item (read var83 var73))))) (and (not (= var67 0)) (and (and (and (and (and (and (and (and (and (and (and (= var66 var65) (= var64 var63)) (= var62 var61)) (= var60 var59)) (= var58 var57)) (= var56 var55)) (= var54 var53)) (= var52 var51)) (= var50 (|sl_item::n1| (getsl_item (read var65 var57))))) (and (and (and (and (and (and (and (and (and (= var65 (newHeap (alloc var49 (O_sl_item var48)))) (or (and var47 (= var63 (newAddr (alloc var49 (O_sl_item var48))))) (and (not var47) (= var63 var46)))) (= var61 var45)) (= var59 var44)) (= var57 var43)) (= var55 var42)) (= var53 var41)) (= var40 var39)) (= var51 (newAddr (alloc var49 (O_sl_item var48))))) (and (= var38 0) (and (and (not (= var37 0)) (and (and (and (and (and (and (and (and (= var36 var110) (= var35 var109)) (= var34 var108)) (= var33 var107)) (= var32 var106)) (= var31 var105)) (= var30 var104)) (= var29 var103)) (= var28 (|sl_item::n1| (getsl_item (read var110 var106)))))) (and (and (and (and (and (and (and (and (= var49 var36) (= var46 var35)) (= var45 var34)) (= var44 var33)) (= var43 var32)) (= var42 var31)) (= var41 var30)) (= var39 var29)) (or (and (not (= var28 (|sl_item::n2| (getsl_item (read var36 var31))))) (= var37 1)) (and (= var28 (|sl_item::n2| (getsl_item (read var36 var31)))) (= var37 0)))))))) (and (and (and (and (and (and (and (= var27 (write var66 var52 (O_sl_item (sl_item var50 (|sl_item::n2| (getsl_item (read var66 var52))) (|sl_item::n3| (getsl_item (read var66 var52))))))) (= var26 var64)) (= var25 var62)) (= var24 var60)) (= var23 var58)) (= var22 var56)) (= var21 var54)) (= var20 var52))) (and (and (and (and (and (and (and (= var83 (write var27 var23 (O_sl_item (sl_item var20 (|sl_item::n2| (getsl_item (read var27 var23))) (|sl_item::n3| (getsl_item (read var27 var23))))))) (= var81 var26)) (= var79 var25)) (= var77 var24)) (= var75 var23)) (= var73 var22)) (= var71 var21)) (= var69 var20))))) (and (and (and (and (and (and (and (= var19 (write var84 var70 (O_sl_item (sl_item (|sl_item::n1| (getsl_item (read var84 var70))) var68 (|sl_item::n3| (getsl_item (read var84 var70))))))) (= var18 var82)) (= var17 var80)) (= var16 var78)) (= var15 var76)) (= var14 var74)) (= var13 var72)) (= var12 var70))) (and (and (and (and (and (and (and (= var101 (write var19 var14 (O_sl_item (sl_item (|sl_item::n1| (getsl_item (read var19 var14))) var12 (|sl_item::n3| (getsl_item (read var19 var14))))))) (= var99 var18)) (= var97 var17)) (= var95 var16)) (= var93 var15)) (= var91 var14)) (= var89 var13)) (= var87 var12))))) (and (and (and (and (and (and (and (= var11 (write var102 var88 (O_sl_item (sl_item (|sl_item::n1| (getsl_item (read var102 var88))) (|sl_item::n2| (getsl_item (read var102 var88))) var86)))) (= var10 var100)) (= var9 var98)) (= var8 var96)) (= var7 var94)) (= var6 var92)) (= var5 var90)) (= var4 var88))) (and (and (and (= var3 (write var11 var5 (O_sl_item (sl_item (|sl_item::n1| (getsl_item (read var11 var5))) (|sl_item::n2| (getsl_item (read var11 var5))) var4)))) (= var2 var10)) (= var1 var9)) (= var0 var8))))) (inv_main581_2_4 var3 var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Bool) (var4 sl) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Bool) (var10 Addr) (var11 sl_item) (var12 Heap) (var13 Heap) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Bool) (var19 Addr) (var20 sl_item) (var21 Heap) (var22 Heap) (var23 Addr) (var24 Addr) (var25 Addr) (var26 Heap) (var27 Addr) (var28 Addr) (var29 Addr) (var30 Heap) (var31 Addr) (var32 Addr) (var33 Addr) (var34 Addr) (var35 Addr) (var36 Heap) (var37 Heap) (var38 Addr) (var39 Addr) (var40 Addr) (var41 Heap) (var42 Addr) (var43 Addr) (var44 Addr) (var45 Addr) (var46 Addr) (var47 Heap) (var48 Heap) (var49 Addr) (var50 Heap)) (or (not (and (inv_main581_2 var50 var49) (and (and (and (and (and (and (and (= var48 (write var47 (|sl::tail| (getsl (read var47 var46))) (O_sl_item (sl_item nullAddr (|sl_item::n2| (getsl_item (read var47 (|sl::tail| (getsl (read var47 var46)))))) (|sl_item::n3| (getsl_item (read var47 (|sl::tail| (getsl (read var47 var46)))))))))) (= var45 var44)) (= var43 var46)) (= var42 nullAddr)) (and (and (and (= var41 (write var48 (|sl::tail| (getsl (read var48 var43))) (O_sl_item (sl_item (|sl_item::n1| (getsl_item (read var48 (|sl::tail| (getsl (read var48 var43)))))) var42 (|sl_item::n3| (getsl_item (read var48 (|sl::tail| (getsl (read var48 var43)))))))))) (= var40 var45)) (= var39 var43)) (= var38 var42))) (and (and (and (and (and (and (and (= var37 var36) (= var35 var34)) (= var33 var32)) (= var31 (|sl::tail| (getsl (read var36 var32))))) (and (and (and (= var30 (write var37 (|sl::head| (getsl (read var37 var33))) (O_sl_item (sl_item var31 (|sl_item::n2| (getsl_item (read var37 (|sl::head| (getsl (read var37 var33)))))) (|sl_item::n3| (getsl_item (read var37 (|sl::head| (getsl (read var37 var33)))))))))) (= var29 var35)) (= var28 var33)) (= var27 var31))) (and (and (and (= var26 (write var30 (|sl::head| (getsl (read var30 var28))) (O_sl_item (sl_item (|sl_item::n1| (getsl_item (read var30 (|sl::head| (getsl (read var30 var28)))))) var27 (|sl_item::n3| (getsl_item (read var30 (|sl::head| (getsl (read var30 var28)))))))))) (= var25 var29)) (= var24 var28)) (= var23 var27))) (and (and (and (and (and (= var22 (newHeap (alloc var21 (O_sl_item var20)))) (or (and var18 (= var19 (newAddr (alloc var21 (O_sl_item var20))))) (and (not var18) (= var19 var17)))) (= var16 var15)) (= var14 (newAddr (alloc var21 (O_sl_item var20))))) (and (and (and (and (= var13 (newHeap (alloc var12 (O_sl_item var11)))) (or (and var9 (= var10 (newAddr (alloc var12 (O_sl_item var11))))) (and (not var9) (= var10 var8)))) (= var7 var6)) (= var5 (newAddr (alloc var12 (O_sl_item var11))))) (and (and (= var12 (newHeap (alloc var50 (O_sl var4)))) (or (and var3 (= var8 (newAddr (alloc var50 (O_sl var4))))) (and (not var3) (= var8 var49)))) (= var6 (newAddr (alloc var50 (O_sl var4))))))) (and (and (= var21 (write var13 var7 (O_sl (sl var5 (|sl::tail| (getsl (read var13 var7))))))) (= var17 var10)) (= var15 var7)))) (and (and (= var36 (write var22 var16 (O_sl (sl (|sl::head| (getsl (read var22 var16))) var14)))) (= var34 var19)) (= var32 var16)))) (and (and (= var47 (write var26 (|sl::head| (getsl (read var26 var24))) (O_sl_item (sl_item (|sl_item::n1| (getsl_item (read var26 (|sl::head| (getsl (read var26 var24)))))) (|sl_item::n2| (getsl_item (read var26 (|sl::head| (getsl (read var26 var24)))))) var23)))) (= var44 var25)) (= var46 var24))) (and (and (= var2 (write var41 (|sl::tail| (getsl (read var41 var39))) (O_sl_item (sl_item (|sl_item::n1| (getsl_item (read var41 (|sl::tail| (getsl (read var41 var39)))))) (|sl_item::n2| (getsl_item (read var41 (|sl::tail| (getsl (read var41 var39)))))) var38)))) (= var1 var40)) (= var0 var39))))) (inv_main581_2_4 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Heap) (var18 Heap) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Heap)) (or (not (and (inv_main571_2 var23 var22 var21 var20 var19) (and (and (and (and (and (and (and (and (and (= var18 var17) (= var16 var15)) (= var14 var13)) (= var12 var11)) (= var10 var9)) (= var8 (|sl_item::n1| (getsl_item (read var17 (|sl::head| (getsl (read var17 var11)))))))) (and (and (and (and (and (and (= var17 var23) (= var15 var22)) (= var13 var21)) (= var11 var20)) (= var7 var19)) (= var9 (|sl::head| (getsl (read var23 var20))))) (not (= (|sl::head| (getsl (read var23 var20))) nullAddr)))) (and (and (and (and (= var6 (write var18 var12 (O_sl (sl var8 (|sl::tail| (getsl (read var18 var12))))))) (= var5 var16)) (= var4 var14)) (= var3 var12)) (= var2 var10))) (= var1 (write var6 var2 defObj))) (or (and (= var5 var2) (= var0 nullAddr)) (and (not (= var5 var2)) (= var0 var5)))))) (inv_main571_2 var1 var0 var4 var3 var2))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main581_2_4 var4 var3 var2) (= var1 0))) (inv_main571_2 var4 var3 var2 var2 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (inv_main571_2 var9 var8 var7 var6 var5) (and (and (= (|sl::head| (getsl (read var9 var6))) nullAddr) (and (and (and (= var4 (write var9 var6 defObj)) (or (and (= var8 var6) (= var3 nullAddr)) (and (not (= var8 var6)) (= var3 var8)))) (= var2 var7)) (= var1 var6))) (= var0 0)))) (inv_main585_9 var4 var3 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Heap) (var17 Int) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Addr) (var25 Heap)) (or (not (and (inv_main_12 var25 var24 var23 var22 var21 var20 var19 var18) (and (and (= var17 0) (and (and (and (and (and (and (and (and (= var16 var25) (= var15 var24)) (= var14 var23)) (= var13 var22)) (= var12 var21)) (= var11 var20)) (= var10 var19)) (= var9 var18)) (= var8 (|sl_item::n2| (getsl_item (read var25 var20)))))) (and (and (and (and (and (and (and (and (= var7 var16) (= var6 var15)) (= var5 var14)) (= var4 var13)) (= var3 var12)) (= var2 var11)) (= var1 var10)) (= var0 var9)) (or (and (not (= var8 (|sl_item::n3| (getsl_item (read var16 var10))))) (= var17 1)) (and (= var8 (|sl_item::n3| (getsl_item (read var16 var10)))) (= var17 0))))))) (inv_main_17 var7 var6 var5 var4 var2 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Heap) (var17 Int) (var18 Int) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Addr) (var25 Addr) (var26 Heap)) (or (not (and (inv_main_12 var26 var25 var24 var23 var22 var21 var20 var19) (and (= var18 0) (and (and (not (= var17 0)) (and (and (and (and (and (and (and (and (= var16 var26) (= var15 var25)) (= var14 var24)) (= var13 var23)) (= var12 var22)) (= var11 var21)) (= var10 var20)) (= var9 var19)) (= var8 (|sl_item::n2| (getsl_item (read var26 var21)))))) (and (and (and (and (and (and (and (and (= var7 var16) (= var6 var15)) (= var5 var14)) (= var4 var13)) (= var3 var12)) (= var2 var11)) (= var1 var10)) (= var0 var9)) (or (and (not (= var8 (|sl_item::n3| (getsl_item (read var16 var10))))) (= var17 1)) (and (= var8 (|sl_item::n3| (getsl_item (read var16 var10)))) (= var17 0)))))))) (inv_main_17 var7 var6 var5 var4 var2 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap) (var9 Int) (var10 Int) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Addr) (var25 Addr) (var26 Heap) (var27 Heap) (var28 Addr) (var29 Addr) (var30 Addr) (var31 Addr) (var32 Addr) (var33 Addr) (var34 Addr) (var35 Heap)) (or (not (and (inv_main_17 var35 var34 var33 var32 var31 var30 var29 var28) (and (and (and (and (and (and (and (and (and (= var27 var26) (= var25 var24)) (= var23 var22)) (= var21 var20)) (= var19 var18)) (= var17 var16)) (= var15 var14)) (= var13 var12)) (= var11 (|sl_item::n1| (getsl_item (read var26 var18))))) (and (not (= var10 0)) (and (and (not (= var9 0)) (and (and (and (and (and (and (and (and (= var8 var35) (= var7 var34)) (= var6 var33)) (= var5 var32)) (= var4 var31)) (= var3 var30)) (= var2 var29)) (= var1 var28)) (= var0 (|sl_item::n1| (getsl_item (read var35 var31)))))) (and (and (and (and (and (and (and (and (= var26 var8) (= var24 var7)) (= var22 var6)) (= var20 var5)) (= var18 var4)) (= var16 var3)) (= var14 var2)) (= var12 var1)) (or (and (not (= var0 (|sl_item::n2| (getsl_item (read var8 var3))))) (= var9 1)) (and (= var0 (|sl_item::n2| (getsl_item (read var8 var3)))) (= var9 0))))))))) (inv_main_17 var27 var25 var23 var21 var11 var17 var15 var13))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap) (var9 Int) (var10 Int) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Addr) (var25 Addr) (var26 Heap) (var27 Heap) (var28 Addr) (var29 Addr) (var30 Addr) (var31 Addr) (var32 Addr) (var33 Addr) (var34 Addr) (var35 Heap)) (or (not (and (inv_main_7 var35 var34 var33 var32 var31 var30 var29 var28) (and (and (and (and (and (and (and (and (and (= var27 var26) (= var25 var24)) (= var23 var22)) (= var21 var20)) (= var19 var18)) (= var17 var16)) (= var15 var14)) (= var13 var12)) (= var11 (|sl_item::n3| (getsl_item (read var26 var14))))) (and (not (= var10 0)) (and (and (not (= var9 0)) (and (and (and (and (and (and (and (and (= var8 var35) (= var7 var34)) (= var6 var33)) (= var5 var32)) (= var4 var31)) (= var3 var30)) (= var2 var29)) (= var1 var28)) (= var0 (|sl_item::n3| (getsl_item (read var35 var29)))))) (and (and (and (and (and (and (and (and (= var26 var8) (= var24 var7)) (= var22 var6)) (= var20 var5)) (= var18 var4)) (= var16 var3)) (= var14 var2)) (= var12 var1)) (or (and (not (= var0 (|sl::tail| (getsl (read var8 var5))))) (= var9 1)) (and (= var0 (|sl::tail| (getsl (read var8 var5)))) (= var9 0))))))))) (inv_main_7 var27 var25 var23 var21 var19 var17 var11 var13))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Heap) (var14 Addr) (var15 Addr) (var16 Heap)) (or (not (and (inv_main581_2_4 var16 var15 var14) (and (and (and (and (and (and (and (and (and (= var13 var16) (= var12 var15)) (= var11 var14)) (= var10 var14)) (= var9 var8)) (= var7 var6)) (= var5 var4)) (= var3 var2)) (= var1 (|sl::head| (getsl (read var16 var14))))) (not (= var0 0))))) (inv_main_7 var13 var12 var11 var10 var9 var7 var1 var3))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap)) (not (and (inv_main585_9 var2 var1 var0) (not (= var1 nullAddr))))))
(check-sat)