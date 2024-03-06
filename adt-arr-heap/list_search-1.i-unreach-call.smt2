(set-logic HORN)
(set-info :source |
    Benchmark: C_VC
    Output by Princess (http://www.philipp.ruemmer.org/princess.shtml)
|)
(set-info :status unsat)
(declare-heap Heap Addr HeapObject
 defObj
 ((HeapObject 0) (list 0)) (
  (
   (O_Int (getInt Int))
   (O_UInt (getUInt Int))
   (O_Addr (getAddr Addr))
   (O_AddrRange (getAddrRange AddrRange))
   (O_list (getlist list))
   (defObj)
  )
  (
   (list (|list::key| Int) (|list::next| Addr))
  )
))
(declare-fun inv_main14_7 (Heap Addr Int Addr Addr Int) Bool)
(declare-fun inv_main556_3 (Heap Addr Int Addr Addr) Bool)
(declare-fun inv_main_44 (Heap Addr Int Addr Addr Addr Int) Bool)
(declare-fun inv_main_47 (Heap Addr Int Addr Addr) Bool)
(declare-fun inv_main_7 (Heap Addr Int Addr Addr) Bool)
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Heap)) (or (not (and (= var4 emptyHeap) (= var3 nullAddr))) (inv_main556_3 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Int) (var7 Heap) (var8 Addr) (var9 Int) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Int) (var14 Addr) (var15 list) (var16 Heap) (var17 Addr) (var18 Int) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Int) (var23 Addr) (var24 Heap) (var25 Int) (var26 Addr) (var27 Addr) (var28 Addr) (var29 Int) (var30 Heap) (var31 Addr) (var32 Int) (var33 Addr) (var34 Addr) (var35 Addr) (var36 Addr) (var37 Addr) (var38 Int) (var39 Int) (var40 Addr) (var41 Addr) (var42 list) (var43 Heap) (var44 Heap) (var45 Addr) (var46 Addr) (var47 Addr) (var48 Int) (var49 Addr) (var50 Heap)) (or (not (and (inv_main556_3 var50 var49 var48 var47 var46) (and (and (and (and (= var45 nullAddr) (and (and (and (and (and (and (and (= var44 (newHeap (alloc var43 (O_list var42)))) (= var41 var40)) (= var39 var38)) (= var37 var36)) (= var35 var34)) (= var33 var36)) (= var32 5)) (= var31 (newAddr (alloc var43 (O_list var42)))))) (and (and (and (and (and (and (= var30 (write var44 var31 (O_list (list var32 (|list::next| (getlist (read var44 var31))))))) (= var45 var41)) (= var29 var39)) (= var28 var37)) (= var27 var35)) (= var26 var31)) (= var25 var32))) (and (and (and (and (and (and (= var24 (write var30 var26 (O_list (list (|list::key| (getlist (read var30 var26))) nullAddr)))) (= var23 var45)) (= var22 var29)) (= var21 var28)) (= var20 var27)) (= var19 var26)) (= var18 var25))) (and (and (and (= var17 nullAddr) (and (and (and (and (and (and (and (= var16 (newHeap (alloc var50 (O_list var15)))) (= var14 var49)) (= var13 var48)) (= var12 var47)) (= var11 var46)) (= var10 var47)) (= var9 2)) (= var8 (newAddr (alloc var50 (O_list var15)))))) (and (and (and (and (and (and (= var7 (write var16 var8 (O_list (list var9 (|list::next| (getlist (read var16 var8))))))) (= var17 var14)) (= var6 var13)) (= var5 var12)) (= var4 var11)) (= var3 var8)) (= var2 var9))) (and (and (and (and (and (and (= var43 (write var7 var3 (O_list (list (|list::key| (getlist (read var7 var3))) nullAddr)))) (= var1 var17)) (= var38 var6)) (= var36 var5)) (= var34 var4)) (= var40 var3)) (= var0 var2)))))) (inv_main_7 var24 var19 var22 var21 var20))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Int) (var7 Heap) (var8 Addr) (var9 Int) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Int) (var14 Addr) (var15 list) (var16 Heap) (var17 Addr) (var18 Int) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Int) (var23 Addr) (var24 Heap) (var25 Int) (var26 Addr) (var27 Addr) (var28 Addr) (var29 Int) (var30 Addr) (var31 Heap) (var32 Int) (var33 Addr) (var34 Addr) (var35 Addr) (var36 Int) (var37 Heap) (var38 Addr) (var39 Int) (var40 Addr) (var41 Addr) (var42 Addr) (var43 Addr) (var44 Addr) (var45 Int) (var46 Int) (var47 Addr) (var48 Addr) (var49 list) (var50 Heap) (var51 Heap) (var52 Addr) (var53 Addr) (var54 Addr) (var55 Int) (var56 Addr) (var57 Heap)) (or (not (and (inv_main556_3 var57 var56 var55 var54 var53) (and (and (and (and (and (not (= var52 nullAddr)) (and (and (and (and (and (and (and (= var51 (newHeap (alloc var50 (O_list var49)))) (= var48 var47)) (= var46 var45)) (= var44 var43)) (= var42 var41)) (= var40 var43)) (= var39 5)) (= var38 (newAddr (alloc var50 (O_list var49)))))) (and (and (and (and (and (and (= var37 (write var51 var38 (O_list (list var39 (|list::next| (getlist (read var51 var38))))))) (= var52 var48)) (= var36 var46)) (= var35 var44)) (= var34 var42)) (= var33 var38)) (= var32 var39))) (and (and (and (and (and (and (= var31 (write var37 var33 (O_list (list var32 (|list::next| (getlist (read var37 var33))))))) (= var30 var52)) (= var29 var36)) (= var28 var35)) (= var27 var34)) (= var26 var33)) (= var25 var32))) (and (and (and (and (and (and (= var24 (write var31 var26 (O_list (list (|list::key| (getlist (read var31 var26))) var30)))) (= var23 var30)) (= var22 var29)) (= var21 var28)) (= var20 var27)) (= var19 var26)) (= var18 var25))) (and (and (and (= var17 nullAddr) (and (and (and (and (and (and (and (= var16 (newHeap (alloc var57 (O_list var15)))) (= var14 var56)) (= var13 var55)) (= var12 var54)) (= var11 var53)) (= var10 var54)) (= var9 2)) (= var8 (newAddr (alloc var57 (O_list var15)))))) (and (and (and (and (and (and (= var7 (write var16 var8 (O_list (list var9 (|list::next| (getlist (read var16 var8))))))) (= var17 var14)) (= var6 var13)) (= var5 var12)) (= var4 var11)) (= var3 var8)) (= var2 var9))) (and (and (and (and (and (and (= var50 (write var7 var3 (O_list (list (|list::key| (getlist (read var7 var3))) nullAddr)))) (= var1 var17)) (= var45 var6)) (= var43 var5)) (= var41 var4)) (= var47 var3)) (= var0 var2)))))) (inv_main_7 var24 var19 var22 var21 var20))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Int) (var7 Addr) (var8 Heap) (var9 Int) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Int) (var14 Heap) (var15 Addr) (var16 Int) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Int) (var21 Addr) (var22 list) (var23 Heap) (var24 Addr) (var25 Int) (var26 Addr) (var27 Addr) (var28 Addr) (var29 Int) (var30 Addr) (var31 Heap) (var32 Int) (var33 Addr) (var34 Addr) (var35 Addr) (var36 Int) (var37 Heap) (var38 Addr) (var39 Int) (var40 Addr) (var41 Addr) (var42 Addr) (var43 Addr) (var44 Addr) (var45 Int) (var46 Int) (var47 Addr) (var48 Addr) (var49 list) (var50 Heap) (var51 Heap) (var52 Addr) (var53 Addr) (var54 Addr) (var55 Int) (var56 Addr) (var57 Heap)) (or (not (and (inv_main556_3 var57 var56 var55 var54 var53) (and (and (and (and (= var52 nullAddr) (and (and (and (and (and (and (and (= var51 (newHeap (alloc var50 (O_list var49)))) (= var48 var47)) (= var46 var45)) (= var44 var43)) (= var42 var41)) (= var40 var43)) (= var39 5)) (= var38 (newAddr (alloc var50 (O_list var49)))))) (and (and (and (and (and (and (= var37 (write var51 var38 (O_list (list var39 (|list::next| (getlist (read var51 var38))))))) (= var52 var48)) (= var36 var46)) (= var35 var44)) (= var34 var42)) (= var33 var38)) (= var32 var39))) (and (and (and (and (and (and (= var31 (write var37 var33 (O_list (list (|list::key| (getlist (read var37 var33))) nullAddr)))) (= var30 var52)) (= var29 var36)) (= var28 var35)) (= var27 var34)) (= var26 var33)) (= var25 var32))) (and (and (and (and (not (= var24 nullAddr)) (and (and (and (and (and (and (and (= var23 (newHeap (alloc var57 (O_list var22)))) (= var21 var56)) (= var20 var55)) (= var19 var54)) (= var18 var53)) (= var17 var54)) (= var16 2)) (= var15 (newAddr (alloc var57 (O_list var22)))))) (and (and (and (and (and (and (= var14 (write var23 var15 (O_list (list var16 (|list::next| (getlist (read var23 var15))))))) (= var24 var21)) (= var13 var20)) (= var12 var19)) (= var11 var18)) (= var10 var15)) (= var9 var16))) (and (and (and (and (and (and (= var8 (write var14 var10 (O_list (list var9 (|list::next| (getlist (read var14 var10))))))) (= var7 var24)) (= var6 var13)) (= var5 var12)) (= var4 var11)) (= var3 var10)) (= var2 var9))) (and (and (and (and (and (and (= var50 (write var8 var3 (O_list (list (|list::key| (getlist (read var8 var3))) var7)))) (= var1 var7)) (= var45 var6)) (= var43 var5)) (= var41 var4)) (= var47 var3)) (= var0 var2)))))) (inv_main_7 var31 var26 var29 var28 var27))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Int) (var7 Addr) (var8 Heap) (var9 Int) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Int) (var14 Heap) (var15 Addr) (var16 Int) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Int) (var21 Addr) (var22 list) (var23 Heap) (var24 Addr) (var25 Int) (var26 Addr) (var27 Addr) (var28 Addr) (var29 Int) (var30 Addr) (var31 Heap) (var32 Int) (var33 Addr) (var34 Addr) (var35 Addr) (var36 Int) (var37 Addr) (var38 Heap) (var39 Int) (var40 Addr) (var41 Addr) (var42 Addr) (var43 Int) (var44 Heap) (var45 Addr) (var46 Int) (var47 Addr) (var48 Addr) (var49 Addr) (var50 Addr) (var51 Addr) (var52 Int) (var53 Int) (var54 Addr) (var55 Addr) (var56 list) (var57 Heap) (var58 Heap) (var59 Addr) (var60 Addr) (var61 Addr) (var62 Int) (var63 Addr) (var64 Heap)) (or (not (and (inv_main556_3 var64 var63 var62 var61 var60) (and (and (and (and (and (not (= var59 nullAddr)) (and (and (and (and (and (and (and (= var58 (newHeap (alloc var57 (O_list var56)))) (= var55 var54)) (= var53 var52)) (= var51 var50)) (= var49 var48)) (= var47 var50)) (= var46 5)) (= var45 (newAddr (alloc var57 (O_list var56)))))) (and (and (and (and (and (and (= var44 (write var58 var45 (O_list (list var46 (|list::next| (getlist (read var58 var45))))))) (= var59 var55)) (= var43 var53)) (= var42 var51)) (= var41 var49)) (= var40 var45)) (= var39 var46))) (and (and (and (and (and (and (= var38 (write var44 var40 (O_list (list var39 (|list::next| (getlist (read var44 var40))))))) (= var37 var59)) (= var36 var43)) (= var35 var42)) (= var34 var41)) (= var33 var40)) (= var32 var39))) (and (and (and (and (and (and (= var31 (write var38 var33 (O_list (list (|list::key| (getlist (read var38 var33))) var37)))) (= var30 var37)) (= var29 var36)) (= var28 var35)) (= var27 var34)) (= var26 var33)) (= var25 var32))) (and (and (and (and (not (= var24 nullAddr)) (and (and (and (and (and (and (and (= var23 (newHeap (alloc var64 (O_list var22)))) (= var21 var63)) (= var20 var62)) (= var19 var61)) (= var18 var60)) (= var17 var61)) (= var16 2)) (= var15 (newAddr (alloc var64 (O_list var22)))))) (and (and (and (and (and (and (= var14 (write var23 var15 (O_list (list var16 (|list::next| (getlist (read var23 var15))))))) (= var24 var21)) (= var13 var20)) (= var12 var19)) (= var11 var18)) (= var10 var15)) (= var9 var16))) (and (and (and (and (and (and (= var8 (write var14 var10 (O_list (list var9 (|list::next| (getlist (read var14 var10))))))) (= var7 var24)) (= var6 var13)) (= var5 var12)) (= var4 var11)) (= var3 var10)) (= var2 var9))) (and (and (and (and (and (and (= var57 (write var8 var3 (O_list (list (|list::key| (getlist (read var8 var3))) var7)))) (= var1 var7)) (= var52 var6)) (= var50 var5)) (= var48 var4)) (= var54 var3)) (= var0 var2)))))) (inv_main_7 var31 var26 var29 var28 var27))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Int) (var6 Addr) (var7 Heap) (var8 Int) (var9 Addr) (var10 Int) (var11 Int) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Int) (var19 Int) (var20 Addr) (var21 Addr) (var22 Heap) (var23 Heap) (var24 Int) (var25 Addr) (var26 Addr) (var27 Addr) (var28 Int) (var29 Addr) (var30 Heap)) (or (not (and (inv_main_44 var30 var29 var28 var27 var26 var25 var24) (and (and (and (and (and (and (and (and (= var23 var22) (= var21 var20)) (= var19 var18)) (= var17 var16)) (= var15 var14)) (= var13 var12)) (= var11 var10)) (= var9 (|list::next| (getlist (read var22 var12))))) (and (and (not (= var8 0)) (and (not (= var25 nullAddr)) (and (and (and (and (and (and (and (= var7 var30) (= var6 var29)) (= var5 var28)) (= var4 var27)) (= var3 var26)) (= var2 var25)) (= var1 var24)) (= var0 (|list::key| (getlist (read var30 var25))))))) (and (and (and (and (and (and (and (= var22 var7) (= var20 var6)) (= var18 var5)) (= var16 var4)) (= var14 var3)) (= var12 var2)) (= var10 var1)) (or (and (not (= var0 var1)) (= var8 1)) (and (= var0 var1) (= var8 0)))))))) (inv_main_44 var23 var21 var19 var17 var15 var9 var11))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Int) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Int) (var8 Heap) (var9 Addr) (var10 Int) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Int) (var15 Addr) (var16 list) (var17 Heap) (var18 Addr) (var19 Int) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Int) (var24 Addr) (var25 Heap) (var26 Int) (var27 Addr) (var28 Addr) (var29 Addr) (var30 Int) (var31 Heap) (var32 Addr) (var33 Int) (var34 Addr) (var35 Addr) (var36 Addr) (var37 Addr) (var38 Addr) (var39 Int) (var40 Int) (var41 Addr) (var42 Addr) (var43 list) (var44 Heap) (var45 Heap) (var46 Addr) (var47 Addr) (var48 Addr) (var49 Int) (var50 Addr) (var51 Heap)) (or (not (and (inv_main_7 var51 var50 var49 var48 var47) (and (and (and (and (and (= var46 nullAddr) (and (and (and (and (and (and (and (= var45 (newHeap (alloc var44 (O_list var43)))) (= var42 var41)) (= var40 var39)) (= var38 var37)) (= var36 var35)) (= var34 var37)) (= var33 3)) (= var32 (newAddr (alloc var44 (O_list var43)))))) (and (and (and (and (and (and (= var31 (write var45 var32 (O_list (list var33 (|list::next| (getlist (read var45 var32))))))) (= var46 var42)) (= var30 var40)) (= var29 var38)) (= var28 var36)) (= var27 var32)) (= var26 var33))) (and (and (and (and (and (and (= var25 (write var31 var27 (O_list (list (|list::key| (getlist (read var31 var27))) nullAddr)))) (= var24 var46)) (= var23 var30)) (= var22 var29)) (= var21 var28)) (= var20 var27)) (= var19 var26))) (and (and (and (= var18 nullAddr) (and (and (and (and (and (and (and (= var17 (newHeap (alloc var51 (O_list var16)))) (= var15 var50)) (= var14 var49)) (= var13 var48)) (= var12 var47)) (= var11 var48)) (= var10 1)) (= var9 (newAddr (alloc var51 (O_list var16)))))) (and (and (and (and (and (and (= var8 (write var17 var9 (O_list (list var10 (|list::next| (getlist (read var17 var9))))))) (= var18 var15)) (= var7 var14)) (= var6 var13)) (= var5 var12)) (= var4 var9)) (= var3 var10))) (and (and (and (and (and (and (= var44 (write var8 var4 (O_list (list (|list::key| (getlist (read var8 var4))) nullAddr)))) (= var2 var18)) (= var39 var7)) (= var37 var6)) (= var35 var5)) (= var41 var4)) (= var1 var3)))) (= var0 2)))) (inv_main_44 var25 var20 var23 var22 var21 var20 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Int) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Int) (var8 Heap) (var9 Addr) (var10 Int) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Int) (var15 Addr) (var16 list) (var17 Heap) (var18 Addr) (var19 Int) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Int) (var24 Addr) (var25 Heap) (var26 Int) (var27 Addr) (var28 Addr) (var29 Addr) (var30 Int) (var31 Addr) (var32 Heap) (var33 Int) (var34 Addr) (var35 Addr) (var36 Addr) (var37 Int) (var38 Heap) (var39 Addr) (var40 Int) (var41 Addr) (var42 Addr) (var43 Addr) (var44 Addr) (var45 Addr) (var46 Int) (var47 Int) (var48 Addr) (var49 Addr) (var50 list) (var51 Heap) (var52 Heap) (var53 Addr) (var54 Addr) (var55 Addr) (var56 Int) (var57 Addr) (var58 Heap)) (or (not (and (inv_main_7 var58 var57 var56 var55 var54) (and (and (and (and (and (and (not (= var53 nullAddr)) (and (and (and (and (and (and (and (= var52 (newHeap (alloc var51 (O_list var50)))) (= var49 var48)) (= var47 var46)) (= var45 var44)) (= var43 var42)) (= var41 var44)) (= var40 3)) (= var39 (newAddr (alloc var51 (O_list var50)))))) (and (and (and (and (and (and (= var38 (write var52 var39 (O_list (list var40 (|list::next| (getlist (read var52 var39))))))) (= var53 var49)) (= var37 var47)) (= var36 var45)) (= var35 var43)) (= var34 var39)) (= var33 var40))) (and (and (and (and (and (and (= var32 (write var38 var34 (O_list (list var33 (|list::next| (getlist (read var38 var34))))))) (= var31 var53)) (= var30 var37)) (= var29 var36)) (= var28 var35)) (= var27 var34)) (= var26 var33))) (and (and (and (and (and (and (= var25 (write var32 var27 (O_list (list (|list::key| (getlist (read var32 var27))) var31)))) (= var24 var31)) (= var23 var30)) (= var22 var29)) (= var21 var28)) (= var20 var27)) (= var19 var26))) (and (and (and (= var18 nullAddr) (and (and (and (and (and (and (and (= var17 (newHeap (alloc var58 (O_list var16)))) (= var15 var57)) (= var14 var56)) (= var13 var55)) (= var12 var54)) (= var11 var55)) (= var10 1)) (= var9 (newAddr (alloc var58 (O_list var16)))))) (and (and (and (and (and (and (= var8 (write var17 var9 (O_list (list var10 (|list::next| (getlist (read var17 var9))))))) (= var18 var15)) (= var7 var14)) (= var6 var13)) (= var5 var12)) (= var4 var9)) (= var3 var10))) (and (and (and (and (and (and (= var51 (write var8 var4 (O_list (list (|list::key| (getlist (read var8 var4))) nullAddr)))) (= var2 var18)) (= var46 var7)) (= var44 var6)) (= var42 var5)) (= var48 var4)) (= var1 var3)))) (= var0 2)))) (inv_main_44 var25 var20 var23 var22 var21 var20 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Int) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Int) (var8 Addr) (var9 Heap) (var10 Int) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Int) (var15 Heap) (var16 Addr) (var17 Int) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Int) (var22 Addr) (var23 list) (var24 Heap) (var25 Addr) (var26 Int) (var27 Addr) (var28 Addr) (var29 Addr) (var30 Int) (var31 Addr) (var32 Heap) (var33 Int) (var34 Addr) (var35 Addr) (var36 Addr) (var37 Int) (var38 Heap) (var39 Addr) (var40 Int) (var41 Addr) (var42 Addr) (var43 Addr) (var44 Addr) (var45 Addr) (var46 Int) (var47 Int) (var48 Addr) (var49 Addr) (var50 list) (var51 Heap) (var52 Heap) (var53 Addr) (var54 Addr) (var55 Addr) (var56 Int) (var57 Addr) (var58 Heap)) (or (not (and (inv_main_7 var58 var57 var56 var55 var54) (and (and (and (and (and (= var53 nullAddr) (and (and (and (and (and (and (and (= var52 (newHeap (alloc var51 (O_list var50)))) (= var49 var48)) (= var47 var46)) (= var45 var44)) (= var43 var42)) (= var41 var44)) (= var40 3)) (= var39 (newAddr (alloc var51 (O_list var50)))))) (and (and (and (and (and (and (= var38 (write var52 var39 (O_list (list var40 (|list::next| (getlist (read var52 var39))))))) (= var53 var49)) (= var37 var47)) (= var36 var45)) (= var35 var43)) (= var34 var39)) (= var33 var40))) (and (and (and (and (and (and (= var32 (write var38 var34 (O_list (list (|list::key| (getlist (read var38 var34))) nullAddr)))) (= var31 var53)) (= var30 var37)) (= var29 var36)) (= var28 var35)) (= var27 var34)) (= var26 var33))) (and (and (and (and (not (= var25 nullAddr)) (and (and (and (and (and (and (and (= var24 (newHeap (alloc var58 (O_list var23)))) (= var22 var57)) (= var21 var56)) (= var20 var55)) (= var19 var54)) (= var18 var55)) (= var17 1)) (= var16 (newAddr (alloc var58 (O_list var23)))))) (and (and (and (and (and (and (= var15 (write var24 var16 (O_list (list var17 (|list::next| (getlist (read var24 var16))))))) (= var25 var22)) (= var14 var21)) (= var13 var20)) (= var12 var19)) (= var11 var16)) (= var10 var17))) (and (and (and (and (and (and (= var9 (write var15 var11 (O_list (list var10 (|list::next| (getlist (read var15 var11))))))) (= var8 var25)) (= var7 var14)) (= var6 var13)) (= var5 var12)) (= var4 var11)) (= var3 var10))) (and (and (and (and (and (and (= var51 (write var9 var4 (O_list (list (|list::key| (getlist (read var9 var4))) var8)))) (= var2 var8)) (= var46 var7)) (= var44 var6)) (= var42 var5)) (= var48 var4)) (= var1 var3)))) (= var0 2)))) (inv_main_44 var32 var27 var30 var29 var28 var27 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Int) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Int) (var8 Addr) (var9 Heap) (var10 Int) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Int) (var15 Heap) (var16 Addr) (var17 Int) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Int) (var22 Addr) (var23 list) (var24 Heap) (var25 Addr) (var26 Int) (var27 Addr) (var28 Addr) (var29 Addr) (var30 Int) (var31 Addr) (var32 Heap) (var33 Int) (var34 Addr) (var35 Addr) (var36 Addr) (var37 Int) (var38 Addr) (var39 Heap) (var40 Int) (var41 Addr) (var42 Addr) (var43 Addr) (var44 Int) (var45 Heap) (var46 Addr) (var47 Int) (var48 Addr) (var49 Addr) (var50 Addr) (var51 Addr) (var52 Addr) (var53 Int) (var54 Int) (var55 Addr) (var56 Addr) (var57 list) (var58 Heap) (var59 Heap) (var60 Addr) (var61 Addr) (var62 Addr) (var63 Int) (var64 Addr) (var65 Heap)) (or (not (and (inv_main_7 var65 var64 var63 var62 var61) (and (and (and (and (and (and (not (= var60 nullAddr)) (and (and (and (and (and (and (and (= var59 (newHeap (alloc var58 (O_list var57)))) (= var56 var55)) (= var54 var53)) (= var52 var51)) (= var50 var49)) (= var48 var51)) (= var47 3)) (= var46 (newAddr (alloc var58 (O_list var57)))))) (and (and (and (and (and (and (= var45 (write var59 var46 (O_list (list var47 (|list::next| (getlist (read var59 var46))))))) (= var60 var56)) (= var44 var54)) (= var43 var52)) (= var42 var50)) (= var41 var46)) (= var40 var47))) (and (and (and (and (and (and (= var39 (write var45 var41 (O_list (list var40 (|list::next| (getlist (read var45 var41))))))) (= var38 var60)) (= var37 var44)) (= var36 var43)) (= var35 var42)) (= var34 var41)) (= var33 var40))) (and (and (and (and (and (and (= var32 (write var39 var34 (O_list (list (|list::key| (getlist (read var39 var34))) var38)))) (= var31 var38)) (= var30 var37)) (= var29 var36)) (= var28 var35)) (= var27 var34)) (= var26 var33))) (and (and (and (and (not (= var25 nullAddr)) (and (and (and (and (and (and (and (= var24 (newHeap (alloc var65 (O_list var23)))) (= var22 var64)) (= var21 var63)) (= var20 var62)) (= var19 var61)) (= var18 var62)) (= var17 1)) (= var16 (newAddr (alloc var65 (O_list var23)))))) (and (and (and (and (and (and (= var15 (write var24 var16 (O_list (list var17 (|list::next| (getlist (read var24 var16))))))) (= var25 var22)) (= var14 var21)) (= var13 var20)) (= var12 var19)) (= var11 var16)) (= var10 var17))) (and (and (and (and (and (and (= var9 (write var15 var11 (O_list (list var10 (|list::next| (getlist (read var15 var11))))))) (= var8 var25)) (= var7 var14)) (= var6 var13)) (= var5 var12)) (= var4 var11)) (= var3 var10))) (and (and (and (and (and (and (= var58 (write var9 var4 (O_list (list (|list::key| (getlist (read var9 var4))) var8)))) (= var2 var8)) (= var53 var7)) (= var51 var6)) (= var49 var5)) (= var55 var4)) (= var1 var3)))) (= var0 2)))) (inv_main_44 var32 var27 var30 var29 var28 var27 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Int) (var10 Addr) (var11 Heap) (var12 Addr) (var13 Addr) (var14 Int) (var15 Addr) (var16 Heap)) (or (not (and (inv_main_47 var16 var15 var14 var13 var12) (and (and (and (and (and (and (and (= var11 var16) (= var10 var15)) (= var9 var14)) (= var8 var13)) (= var7 var12)) (= var6 (|list::next| (getlist (read var16 var15))))) (and (and (and (and (and (= var5 (write var11 var10 defObj)) (= var4 var10)) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var0 var6))) (not (= var15 nullAddr))))) (inv_main_47 var5 var0 var3 var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Heap) (var5 Int) (var6 Addr) (var7 Addr) (var8 Int) (var9 Addr) (var10 Heap) (var11 Int) (var12 Int) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Int) (var17 Addr) (var18 Heap)) (or (not (and (inv_main_44 var18 var17 var16 var15 var14 var13 var12) (and (and (and (not (= var11 0)) (and (and (and (and (and (= var10 var18) (= var9 var17)) (= var8 var16)) (= var7 var15)) (= var6 var13)) (= var5 (|list::key| (getlist (read var18 var13)))))) (and (and (and (and (and (= var4 var10) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var0 var6)) (or (and (= var5 1) (= var11 1)) (and (not (= var5 1)) (= var11 0))))) (= var13 nullAddr)))) (inv_main_47 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Int) (var8 Addr) (var9 Heap) (var10 Int) (var11 Addr) (var12 Addr) (var13 Int) (var14 Addr) (var15 Heap) (var16 Int) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Int) (var22 Int) (var23 Addr) (var24 Addr) (var25 Heap) (var26 Heap) (var27 Int) (var28 Int) (var29 Addr) (var30 Addr) (var31 Addr) (var32 Int) (var33 Addr) (var34 Heap)) (or (not (and (inv_main_44 var34 var33 var32 var31 var30 var29 var28) (and (and (and (not (= var27 0)) (and (and (and (and (and (= var26 var25) (= var24 var23)) (= var22 var21)) (= var20 var19)) (= var18 var17)) (= var16 (|list::key| (getlist (read var25 var17)))))) (and (and (and (and (and (= var15 var26) (= var14 var24)) (= var13 var22)) (= var12 var20)) (= var11 var18)) (or (and (= var16 1) (= var27 1)) (and (not (= var16 1)) (= var27 0))))) (and (and (= var10 0) (and (not (= var29 nullAddr)) (and (and (and (and (and (and (and (= var9 var34) (= var8 var33)) (= var7 var32)) (= var6 var31)) (= var5 var30)) (= var4 var29)) (= var3 var28)) (= var2 (|list::key| (getlist (read var34 var29))))))) (and (and (and (and (and (and (and (= var25 var9) (= var23 var8)) (= var21 var7)) (= var19 var6)) (= var1 var5)) (= var17 var4)) (= var0 var3)) (or (and (not (= var2 var3)) (= var10 1)) (and (= var2 var3) (= var10 0)))))))) (inv_main_47 var15 var14 var13 var12 var11))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Heap) (var5 Int) (var6 Addr) (var7 Addr) (var8 Int) (var9 Addr) (var10 Heap) (var11 Int) (var12 Int) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Int) (var17 Addr) (var18 Heap)) (or (not (and (inv_main_44 var18 var17 var16 var15 var14 var13 var12) (and (and (and (= var11 0) (and (and (and (and (and (= var10 var18) (= var9 var17)) (= var8 var16)) (= var7 var15)) (= var6 var13)) (= var5 (|list::key| (getlist (read var18 var13)))))) (and (and (and (and (and (= var4 var10) (= var3 var9)) (= var2 var8)) (= var1 var7)) (= var0 var6)) (or (and (= var5 1) (= var11 1)) (and (not (= var5 1)) (= var11 0))))) (= var13 nullAddr)))) (inv_main14_7 var4 var3 var2 var1 var0 var11))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Int) (var8 Addr) (var9 Heap) (var10 Int) (var11 Addr) (var12 Addr) (var13 Int) (var14 Addr) (var15 Heap) (var16 Int) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Int) (var22 Int) (var23 Addr) (var24 Addr) (var25 Heap) (var26 Heap) (var27 Int) (var28 Int) (var29 Addr) (var30 Addr) (var31 Addr) (var32 Int) (var33 Addr) (var34 Heap)) (or (not (and (inv_main_44 var34 var33 var32 var31 var30 var29 var28) (and (and (and (= var27 0) (and (and (and (and (and (= var26 var25) (= var24 var23)) (= var22 var21)) (= var20 var19)) (= var18 var17)) (= var16 (|list::key| (getlist (read var25 var17)))))) (and (and (and (and (and (= var15 var26) (= var14 var24)) (= var13 var22)) (= var12 var20)) (= var11 var18)) (or (and (= var16 1) (= var27 1)) (and (not (= var16 1)) (= var27 0))))) (and (and (= var10 0) (and (not (= var29 nullAddr)) (and (and (and (and (and (and (and (= var9 var34) (= var8 var33)) (= var7 var32)) (= var6 var31)) (= var5 var30)) (= var4 var29)) (= var3 var28)) (= var2 (|list::key| (getlist (read var34 var29))))))) (and (and (and (and (and (and (and (= var25 var9) (= var23 var8)) (= var21 var7)) (= var19 var6)) (= var1 var5)) (= var17 var4)) (= var0 var3)) (or (and (not (= var2 var3)) (= var10 1)) (and (= var2 var3) (= var10 0)))))))) (inv_main14_7 var15 var14 var13 var12 var11 var27))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Addr) (var5 Heap)) (not (inv_main14_7 var5 var4 var3 var2 var1 var0))))
(check-sat)
