(set-logic HORN)
(set-info :source |
    Benchmark: C_VC
    Output by Princess (http://www.philipp.ruemmer.org/princess.shtml)
|)
(set-info :status unsat)
(declare-datatype bool (
  (true)
  (false)
))
(declare-heap Heap Addr HeapObject
 defObj
 ((HeapObject 0) (item 0)) (
  (
   (O_Int (getInt Int))
   (O_UInt (getUInt Int))
   (O_Addr (getAddr Addr))
   (O_AddrRange (getAddrRange AddrRange))
   (O_item (getitem item))
   (defObj)
  )
  (
   (item (|item::next| Addr) (|item::data| Addr))
  )
))
(declare-fun inv_main541_5 (Heap Addr Int) Bool)
(declare-fun inv_main546_14 (Heap Addr Int Addr Int) Bool)
(declare-fun inv_main562_12 (Heap Addr Int Int) Bool)
(declare-fun inv_main_7 (Heap Addr Int Addr Int) Bool)
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap)) (or (not (and (and (= var2 emptyHeap) (= var1 nullAddr)) (= var0 0))) (inv_main541_5 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Int) (var4 Addr) (var5 Heap)) (or (not (and (inv_main_7 var5 var4 var3 var2 var1) (and (not (<= 0 (+ var1 (- 1)))) (= var0 0)))) (inv_main562_12 var5 var4 var3 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Int) (var4 Addr) (var5 Heap)) (or (not (and (inv_main546_14 var5 var4 var3 var2 var1) (and (not (<= 0 (+ var1 (- 1)))) (= var0 0)))) (inv_main_7 var5 var4 var3 var2 var1))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Heap) (var4 Int) (var5 Int) (var6 Int) (var7 Int) (var8 Addr) (var9 Int) (var10 Addr) (var11 Heap)) (or (not (and (inv_main546_14 var11 var10 var9 var8 var7) (and (not (<= 0 (+ var6 (- 1)))) (and (and (= var5 0) (not (= var4 0))) (and (and (and (and (and (= var3 var11) (= var2 var10)) (= var1 var9)) (= var0 var8)) (= var6 var7)) (or (and (<= 0 (+ (+ 20 (* (- 1) var9)) (- 1))) (= var5 1)) (and (not (<= 0 (+ (+ 20 (* (- 1) var9)) (- 1)))) (= var5 0)))))))) (inv_main_7 var3 var2 var1 var0 var6))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Addr) (var4 Int) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Int) (var9 Addr) (var10 Int) (var11 Addr) (var12 Heap) (var13 Int) (var14 Addr) (var15 Int) (var16 Addr) (var17 Heap)) (or (not (and (inv_main_7 var17 var16 var15 var14 var13) (and (and (and (and (and (and (and (and (= var12 var17) (= var11 var16)) (= var10 var15)) (= var9 var14)) (= var8 var13)) (= var7 (|item::next| (getitem (read var17 var14))))) (and (and (and (and (and (= var6 (write var12 var9 defObj)) (or (and (= var11 var9) (= var5 nullAddr)) (and (not (= var11 var9)) (= var5 var11)))) (= var4 var10)) (= var3 var9)) (= var2 var8)) (= var1 var7))) (<= 0 (+ var13 (- 1)))) (= var0 (+ var2 (- 1)))))) (inv_main_7 var6 var5 var4 var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Int) (var4 Addr) (var5 Int) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Int) (var10 Int) (var11 Addr) (var12 Addr) (var13 Int) (var14 Int) (var15 Addr) (var16 Addr) (var17 Heap) (var18 Heap) (var19 Int) (var20 Addr) (var21 Int) (var22 Addr) (var23 Heap)) (or (not (and (inv_main546_14 var23 var22 var21 var20 var19) (and (and (and (and (and (and (and (and (and (= var18 var17) (= var16 var15)) (= var14 var13)) (= var12 var11)) (= var10 var9)) (= var8 (|item::next| (getitem (read var17 var11))))) (and (and (and (and (and (= var7 (write var18 var12 defObj)) (or (and (= var16 var12) (= var6 nullAddr)) (and (not (= var16 var12)) (= var6 var16)))) (= var5 var14)) (= var4 var12)) (= var3 var10)) (= var2 var8))) (and (<= 0 (+ (* (- 1) var19) (- 1))) (and (<= 0 (+ var19 (- 1))) (= var1 0)))) (and (and (and (and (= var17 (write var23 (|item::data| (getitem (read var23 var20))) defObj)) (or (and (= var22 (|item::data| (getitem (read var23 var20)))) (= var15 nullAddr)) (and (not (= var22 (|item::data| (getitem (read var23 var20))))) (= var15 var22)))) (= var13 var21)) (= var11 var20)) (= var9 var19))) (= var0 (+ var3 (- 1)))))) (inv_main_7 var7 var6 var5 var2 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Addr) (var4 Heap) (var5 Int) (var6 Int) (var7 Int) (var8 Addr) (var9 Int) (var10 Addr) (var11 Int) (var12 Addr) (var13 Heap) (var14 Addr) (var15 Int) (var16 Int) (var17 Addr) (var18 Addr) (var19 Int) (var20 Int) (var21 Addr) (var22 Addr) (var23 Heap) (var24 Heap) (var25 Int) (var26 Addr) (var27 Int) (var28 Addr) (var29 Heap)) (or (not (and (inv_main546_14 var29 var28 var27 var26 var25) (and (and (and (and (and (and (and (and (and (= var24 var23) (= var22 var21)) (= var20 var19)) (= var18 var17)) (= var16 var15)) (= var14 (|item::next| (getitem (read var23 var17))))) (and (and (and (and (and (= var13 (write var24 var18 defObj)) (or (and (= var22 var18) (= var12 nullAddr)) (and (not (= var22 var18)) (= var12 var22)))) (= var11 var20)) (= var10 var18)) (= var9 var16)) (= var8 var14))) (and (<= 0 (+ (* (- 1) var7) (- 1))) (and (<= 0 (+ var7 (- 1))) (and (and (= var6 0) (not (= var5 0))) (and (and (and (and (and (= var4 var29) (= var3 var28)) (= var2 var27)) (= var1 var26)) (= var7 var25)) (or (and (<= 0 (+ (+ 20 (* (- 1) var27)) (- 1))) (= var6 1)) (and (not (<= 0 (+ (+ 20 (* (- 1) var27)) (- 1)))) (= var6 0)))))))) (and (and (and (and (= var23 (write var4 (|item::data| (getitem (read var4 var1))) defObj)) (or (and (= var3 (|item::data| (getitem (read var4 var1)))) (= var21 nullAddr)) (and (not (= var3 (|item::data| (getitem (read var4 var1))))) (= var21 var3)))) (= var19 var2)) (= var17 var1)) (= var15 var7))) (= var0 (+ var9 (- 1)))))) (inv_main_7 var13 var12 var11 var8 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Int) (var4 Addr) (var5 Int) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Int) (var10 Addr) (var11 Int) (var12 Addr) (var13 Heap) (var14 Int) (var15 Addr) (var16 Int) (var17 Addr) (var18 Heap)) (or (not (and (inv_main546_14 var18 var17 var16 var15 var14) (and (and (and (and (and (and (and (and (= var13 var18) (= var12 var17)) (= var11 var16)) (= var10 var15)) (= var9 var14)) (= var8 (|item::next| (getitem (read var18 var15))))) (and (and (and (and (and (= var7 (write var13 var10 defObj)) (or (and (= var12 var10) (= var6 nullAddr)) (and (not (= var12 var10)) (= var6 var12)))) (= var5 var11)) (= var4 var10)) (= var3 var9)) (= var2 var8))) (and (not (<= 0 (+ (* (- 1) var14) (- 1)))) (and (<= 0 (+ var14 (- 1))) (= var1 0)))) (= var0 (+ var3 (- 1)))))) (inv_main_7 var7 var6 var5 var2 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Int) (var5 Addr) (var6 Int) (var7 Addr) (var8 Heap) (var9 Addr) (var10 Int) (var11 Int) (var12 Addr) (var13 Addr) (var14 Int) (var15 Int) (var16 Addr) (var17 Addr) (var18 Heap) (var19 Heap) (var20 Int) (var21 Addr) (var22 Int) (var23 Addr) (var24 Heap)) (or (not (and (inv_main546_14 var24 var23 var22 var21 var20) (and (and (and (and (and (and (and (and (= var19 var18) (= var17 var16)) (= var15 var14)) (= var13 var12)) (= var11 var10)) (= var9 (|item::next| (getitem (read var18 var12))))) (and (and (and (and (and (= var8 (write var19 var13 defObj)) (or (and (= var17 var13) (= var7 nullAddr)) (and (not (= var17 var13)) (= var7 var17)))) (= var6 var15)) (= var5 var13)) (= var4 var11)) (= var3 var9))) (and (not (<= 0 (+ (* (- 1) var10) (- 1)))) (and (<= 0 (+ var10 (- 1))) (and (and (= var2 0) (not (= var1 0))) (and (and (and (and (and (= var18 var24) (= var16 var23)) (= var14 var22)) (= var12 var21)) (= var10 var20)) (or (and (<= 0 (+ (+ 20 (* (- 1) var22)) (- 1))) (= var2 1)) (and (not (<= 0 (+ (+ 20 (* (- 1) var22)) (- 1)))) (= var2 0)))))))) (= var0 (+ var4 (- 1)))))) (inv_main_7 var8 var7 var6 var3 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Int) (var5 Int) (var6 Addr) (var7 Int) (var8 Addr) (var9 Heap) (var10 Addr) (var11 Int) (var12 Int) (var13 Int) (var14 Addr) (var15 Addr) (var16 Int) (var17 Int) (var18 Addr) (var19 Bool) (var20 Addr) (var21 item) (var22 Heap) (var23 Heap) (var24 Addr) (var25 Addr) (var26 Int) (var27 Int) (var28 Int) (var29 Int) (var30 Addr) (var31 Addr) (var32 Int) (var33 Int) (var34 Addr) (var35 Addr) (var36 Heap) (var37 Addr) (var38 Heap) (var39 Int) (var40 Addr) (var41 Int) (var42 Addr) (var43 Heap)) (or (not (and (inv_main546_14 var43 var42 var41 var40 var39) (and (and (and (and (and (and (not (= (|item::next| (getitem (read var38 var37))) nullAddr)) (and (and (and (and (and (and (and (= var36 var38) (= var35 var34)) (= var33 var32)) (= var31 var30)) (= var29 var28)) (= var27 var26)) (= var25 var37)) (= var24 (|item::data| (getitem (read var38 (|item::next| (getitem (read var38 var37))))))))) (and (and (and (and (and (and (= var23 (newHeap (alloc var22 (O_item var21)))) (or (and var19 (= var20 (newAddr (alloc var22 (O_item var21))))) (and (not var19) (= var20 var18)))) (= var17 (+ var16 1))) (= var15 var14)) (= var13 var12)) (= var11 3)) (= var10 (newAddr (alloc var22 (O_item var21)))))) (and (and (and (and (and (and (= var38 (write var23 var10 (O_item (item var15 (|item::data| (getitem (read var23 var10))))))) (= var34 var20)) (= var32 var17)) (= var30 var15)) (= var28 var13)) (= var26 var11)) (= var37 var10))) (and (and (and (and (and (and (= var9 (write var36 var25 (O_item (item (|item::next| (getitem (read var36 var25))) var24)))) (= var8 var35)) (= var7 var33)) (= var6 var31)) (= var5 var29)) (= var4 var27)) (= var3 var25))) (and (and (not (= var2 0)) (not (= var1 0))) (and (and (and (and (and (= var22 var43) (= var18 var42)) (= var16 var41)) (= var14 var40)) (= var12 var39)) (or (and (<= 0 (+ (+ 20 (* (- 1) var41)) (- 1))) (= var2 1)) (and (not (<= 0 (+ (+ 20 (* (- 1) var41)) (- 1)))) (= var2 0)))))) (= var0 (+ var5 1))))) (inv_main546_14 var9 var8 var7 var3 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Int) (var5 Int) (var6 Addr) (var7 Int) (var8 Addr) (var9 Heap) (var10 Addr) (var11 Int) (var12 Int) (var13 Int) (var14 Addr) (var15 Addr) (var16 Int) (var17 Int) (var18 Addr) (var19 Bool) (var20 Addr) (var21 item) (var22 Heap) (var23 Heap) (var24 Addr) (var25 Addr) (var26 Int) (var27 Int) (var28 Int) (var29 Int) (var30 Addr) (var31 Addr) (var32 Int) (var33 Int) (var34 Addr) (var35 Bool) (var36 Addr) (var37 item) (var38 Heap) (var39 Addr) (var40 Heap) (var41 Int) (var42 Addr) (var43 Int) (var44 Addr) (var45 Heap)) (or (not (and (inv_main546_14 var45 var44 var43 var42 var41) (and (and (and (and (and (and (= (|item::next| (getitem (read var40 var39))) nullAddr) (and (and (and (and (and (and (and (= var38 (newHeap (alloc var40 (O_item var37)))) (or (and var35 (= var36 (newAddr (alloc var40 (O_item var37))))) (and (not var35) (= var36 var34)))) (= var33 var32)) (= var31 var30)) (= var29 var28)) (= var27 var26)) (= var25 var39)) (= var24 (newAddr (alloc var40 (O_item var37)))))) (and (and (and (and (and (and (= var23 (newHeap (alloc var22 (O_item var21)))) (or (and var19 (= var20 (newAddr (alloc var22 (O_item var21))))) (and (not var19) (= var20 var18)))) (= var17 (+ var16 1))) (= var15 var14)) (= var13 var12)) (= var11 3)) (= var10 (newAddr (alloc var22 (O_item var21)))))) (and (and (and (and (and (and (= var40 (write var23 var10 (O_item (item var15 (|item::data| (getitem (read var23 var10))))))) (= var34 var20)) (= var32 var17)) (= var30 var15)) (= var28 var13)) (= var26 var11)) (= var39 var10))) (and (and (and (and (and (and (= var9 (write var38 var25 (O_item (item (|item::next| (getitem (read var38 var25))) var24)))) (= var8 var36)) (= var7 var33)) (= var6 var31)) (= var5 var29)) (= var4 var27)) (= var3 var25))) (and (and (not (= var2 0)) (not (= var1 0))) (and (and (and (and (and (= var22 var45) (= var18 var44)) (= var16 var43)) (= var14 var42)) (= var12 var41)) (or (and (<= 0 (+ (+ 20 (* (- 1) var43)) (- 1))) (= var2 1)) (and (not (<= 0 (+ (+ 20 (* (- 1) var43)) (- 1)))) (= var2 0)))))) (= var0 (+ var5 1))))) (inv_main546_14 var9 var8 var7 var3 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Addr) (var5 Int) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Int) (var10 Int) (var11 Addr) (var12 Addr) (var13 Int) (var14 Int) (var15 Addr) (var16 Bool) (var17 Addr) (var18 item) (var19 Heap) (var20 Heap) (var21 Addr) (var22 Addr) (var23 Int) (var24 Int) (var25 Int) (var26 Int) (var27 Addr) (var28 Addr) (var29 Int) (var30 Int) (var31 Addr) (var32 Addr) (var33 Heap) (var34 Addr) (var35 Heap) (var36 Int) (var37 Addr) (var38 Heap)) (or (not (and (inv_main541_5 var38 var37 var36) (and (and (and (and (and (and (not (= (|item::next| (getitem (read var35 var34))) nullAddr)) (and (and (and (and (and (and (and (= var33 var35) (= var32 var31)) (= var30 var29)) (= var28 var27)) (= var26 var25)) (= var24 var23)) (= var22 var34)) (= var21 (|item::data| (getitem (read var35 (|item::next| (getitem (read var35 var34))))))))) (and (and (and (and (and (and (= var20 (newHeap (alloc var19 (O_item var18)))) (or (and var16 (= var17 (newAddr (alloc var19 (O_item var18))))) (and (not var16) (= var17 var15)))) (= var14 (+ var13 1))) (= var12 var11)) (= var10 0)) (= var9 3)) (= var8 (newAddr (alloc var19 (O_item var18)))))) (and (and (and (and (and (and (= var35 (write var20 var8 (O_item (item var12 (|item::data| (getitem (read var20 var8))))))) (= var31 var17)) (= var29 var14)) (= var27 var12)) (= var25 var10)) (= var23 var9)) (= var34 var8))) (and (and (and (and (and (and (= var7 (write var33 var22 (O_item (item (|item::next| (getitem (read var33 var22))) var21)))) (= var6 var32)) (= var5 var30)) (= var4 var28)) (= var3 var26)) (= var2 var24)) (= var1 var22))) (and (and (and (= var19 var38) (= var15 var37)) (= var13 var36)) (= var11 nullAddr))) (= var0 (+ var3 1))))) (inv_main546_14 var7 var6 var5 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Addr) (var5 Int) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Int) (var10 Int) (var11 Addr) (var12 Addr) (var13 Int) (var14 Int) (var15 Addr) (var16 Bool) (var17 Addr) (var18 item) (var19 Heap) (var20 Heap) (var21 Addr) (var22 Addr) (var23 Int) (var24 Int) (var25 Int) (var26 Int) (var27 Addr) (var28 Addr) (var29 Int) (var30 Int) (var31 Addr) (var32 Bool) (var33 Addr) (var34 item) (var35 Heap) (var36 Addr) (var37 Heap) (var38 Int) (var39 Addr) (var40 Heap)) (or (not (and (inv_main541_5 var40 var39 var38) (and (and (and (and (and (and (= (|item::next| (getitem (read var37 var36))) nullAddr) (and (and (and (and (and (and (and (= var35 (newHeap (alloc var37 (O_item var34)))) (or (and var32 (= var33 (newAddr (alloc var37 (O_item var34))))) (and (not var32) (= var33 var31)))) (= var30 var29)) (= var28 var27)) (= var26 var25)) (= var24 var23)) (= var22 var36)) (= var21 (newAddr (alloc var37 (O_item var34)))))) (and (and (and (and (and (and (= var20 (newHeap (alloc var19 (O_item var18)))) (or (and var16 (= var17 (newAddr (alloc var19 (O_item var18))))) (and (not var16) (= var17 var15)))) (= var14 (+ var13 1))) (= var12 var11)) (= var10 0)) (= var9 3)) (= var8 (newAddr (alloc var19 (O_item var18)))))) (and (and (and (and (and (and (= var37 (write var20 var8 (O_item (item var12 (|item::data| (getitem (read var20 var8))))))) (= var31 var17)) (= var29 var14)) (= var27 var12)) (= var25 var10)) (= var23 var9)) (= var36 var8))) (and (and (and (and (and (and (= var7 (write var35 var22 (O_item (item (|item::next| (getitem (read var35 var22))) var21)))) (= var6 var33)) (= var5 var30)) (= var4 var28)) (= var3 var26)) (= var2 var24)) (= var1 var22))) (and (and (and (= var19 var40) (= var15 var39)) (= var13 var38)) (= var11 nullAddr))) (= var0 (+ var3 1))))) (inv_main546_14 var7 var6 var5 var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Heap)) (not (and (inv_main562_12 var3 var2 var1 var0) (not (= var2 nullAddr))))))
(check-sat)
