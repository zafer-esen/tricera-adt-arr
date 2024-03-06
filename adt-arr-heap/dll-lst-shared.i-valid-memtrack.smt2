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
 ((HeapObject 0) (dll 0)) (
  (
   (O_Int (getInt Int))
   (O_UInt (getUInt Int))
   (O_Addr (getAddr Addr))
   (O_AddrRange (getAddrRange AddrRange))
   (O_dll (getdll dll))
   (defObj)
  )
  (
   (dll (|dll::data| Addr) (|dll::next| Addr) (|dll::prev| Addr))
  )
))
(declare-fun inv_main2424_5 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main2442_5 (Heap Addr) Bool)
(declare-fun inv_main2445_12 (Heap Addr Int) Bool)
(declare-fun inv_main_18 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main_3 (Heap Addr Addr Addr Addr) Bool)
(assert (forall ((var0 Addr) (var1 Heap)) (or (not (and (= var1 emptyHeap) (= var0 nullAddr))) (inv_main2442_5 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main_18 var4 var3 var2 var1) (and (= var1 nullAddr) (= var0 0)))) (inv_main2445_12 var4 var3 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Heap)) (or (not (and (inv_main_18 var13 var12 var11 var10) (and (and (and (and (and (and (= var9 var13) (= var8 var12)) (= var7 var11)) (= var6 var10)) (= var5 (|dll::next| (getdll (read var13 var10))))) (and (and (and (and (= var4 (write var9 var6 defObj)) (or (and (= var8 var6) (= var3 nullAddr)) (and (not (= var8 var6)) (= var3 var8)))) (= var2 var7)) (= var1 var6)) (= var0 var5))) (not (= var10 nullAddr))))) (inv_main_18 var4 var3 var2 var0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main2424_5 var6 var5 var4 var3 var2) (and (and (and (not (= var4 nullAddr)) (= var2 nullAddr)) (= var1 (write var6 (|dll::data| (getdll (read var6 var4))) defObj))) (or (and (= var5 (|dll::data| (getdll (read var6 var4)))) (= var0 nullAddr)) (and (not (= var5 (|dll::data| (getdll (read var6 var4))))) (= var0 var5)))))) (inv_main_18 var1 var0 var4 var4))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (and (inv_main2424_5 var4 var3 var2 var1 var0) (and (= var2 nullAddr) (= var0 nullAddr)))) (inv_main_18 var4 var3 var2 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Heap) (var11 Heap) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Heap)) (or (not (and (inv_main2424_5 var16 var15 var14 var13 var12) (and (and (and (and (and (and (= var11 var10) (= var9 var8)) (= var7 var6)) (= var5 var4)) (= var3 var2)) (= var1 (|dll::next| (getdll (read var10 var2))))) (and (and (and (and (and (and (= var10 var16) (= var8 var15)) (= var6 var14)) (= var4 var13)) (= var2 var12)) (= var0 (|dll::data| (getdll (read var16 var13))))) (not (= var12 nullAddr)))))) (inv_main2424_5 var11 var9 var7 var5 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main_3 var5 var4 var3 var2 var1) (= var0 0))) (inv_main2424_5 var5 var4 var3 var3 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap) (var10 Int) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Heap) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Heap) (var23 Addr) (var24 Addr) (var25 Addr) (var26 Addr) (var27 Bool) (var28 Addr) (var29 dll) (var30 Heap) (var31 Addr) (var32 Addr) (var33 Addr) (var34 Addr) (var35 Addr) (var36 Addr) (var37 Addr) (var38 Addr) (var39 Addr) (var40 Heap) (var41 Heap) (var42 Addr) (var43 Addr) (var44 Addr) (var45 Addr) (var46 Heap)) (or (not (and (inv_main_3 var46 var45 var44 var43 var42) (and (and (and (and (and (and (and (= var41 var40) (= var39 var38)) (= var37 var36)) (= var35 var34)) (= var33 var32)) (= var31 (|dll::next| (getdll (read var40 var34))))) (and (and (and (and (and (and (and (and (and (and (= var30 (newHeap (alloc var46 (O_dll var29)))) (or (and var27 (= var28 (newAddr (alloc var46 (O_dll var29))))) (and (not var27) (= var28 var45)))) (= var26 var44)) (= var25 var43)) (= var24 var42)) (= var23 (newAddr (alloc var46 (O_dll var29))))) (and (and (and (and (and (= var22 (write var30 var23 (O_dll (dll (|dll::data| (getdll (read var30 var23))) nullAddr (|dll::prev| (getdll (read var30 var23))))))) (= var21 var28)) (= var20 var26)) (= var19 var25)) (= var18 var24)) (= var17 var23))) (and (and (and (and (and (= var16 (write var22 var17 (O_dll (dll (|dll::data| (getdll (read var22 var17))) (|dll::next| (getdll (read var22 var17))) nullAddr)))) (= var15 var21)) (= var14 var20)) (= var13 var19)) (= var12 var18)) (= var11 var17))) (not (= var10 0))) (and (and (and (and (= var9 (write var16 var13 (O_dll (dll (|dll::data| (getdll (read var16 var13))) var11 (|dll::prev| (getdll (read var16 var13))))))) (= var8 var15)) (= var7 var14)) (= var6 var13)) (= var5 var12))) (and (and (and (and (= var4 (write var9 (|dll::next| (getdll (read var9 var6))) (O_dll (dll (|dll::data| (getdll (read var9 (|dll::next| (getdll (read var9 var6)))))) (|dll::next| (getdll (read var9 (|dll::next| (getdll (read var9 var6)))))) var6)))) (= var3 var8)) (= var2 var7)) (= var1 var6)) (= var0 var5)))) (and (and (and (and (= var40 (write var4 (|dll::next| (getdll (read var4 var1))) (O_dll (dll var0 (|dll::next| (getdll (read var4 (|dll::next| (getdll (read var4 var1)))))) (|dll::prev| (getdll (read var4 (|dll::next| (getdll (read var4 var1)))))))))) (= var38 var3)) (= var36 var2)) (= var34 var1)) (= var32 var0))))) (inv_main_3 var41 var39 var37 var31 var33))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Bool) (var6 Addr) (var7 dll) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Int) (var14 Heap) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Bool) (var21 Addr) (var22 Int) (var23 Heap) (var24 Heap) (var25 Addr) (var26 Heap)) (or (not (and (inv_main2442_5 var26 var25) (and (and (and (and (and (and (and (= var24 (newHeap (alloc var23 (O_Int var22)))) (or (and var20 (= var21 (newAddr (alloc var23 (O_Int var22))))) (and (not var20) (= var21 var19)))) (= var18 var17)) (= var16 var17)) (= var15 (newAddr (alloc var23 (O_Int var22))))) (and (and (and (and (= var14 (write var24 var15 (O_Int var13))) (= var12 var21)) (= var11 var18)) (= var10 var16)) (= var9 var15))) (and (and (and (and (= var8 (newHeap (alloc var26 (O_dll var7)))) (or (and var5 (= var6 (newAddr (alloc var26 (O_dll var7))))) (and (not var5) (= var6 var25)))) (= var4 (newAddr (alloc var26 (O_dll var7))))) (and (and (= var3 (write var8 var4 (O_dll (dll (|dll::data| (getdll (read var8 var4))) nullAddr (|dll::prev| (getdll (read var8 var4))))))) (= var2 var6)) (= var1 var4))) (and (and (= var23 (write var3 var1 (O_dll (dll (|dll::data| (getdll (read var3 var1))) (|dll::next| (getdll (read var3 var1))) nullAddr)))) (= var19 var2)) (= var17 var1)))) (= var0 (write var14 var10 (O_dll (dll var9 (|dll::next| (getdll (read var14 var10))) (|dll::prev| (getdll (read var14 var10)))))))))) (inv_main_3 var0 var12 var11 var10 var9))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap)) (not (and (inv_main2445_12 var2 var1 var0) (not (= var1 nullAddr))))))
(check-sat)
