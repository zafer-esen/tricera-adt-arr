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
 ((HeapObject 0) (TData 0)) (
  (
   (O_Int (getInt Int))
   (O_UInt (getUInt Int))
   (O_Addr (getAddr Addr))
   (O_AddrRange (getAddrRange AddrRange))
   (O_TData (getTData TData))
   (defObj)
  )
  (
   (TData (|TData::lo| Addr) (|TData::hi| Addr))
  )
))
(declare-fun inv_main545_5 (Heap Addr TData) Bool)
(declare-fun inv_main547_12 (Heap Addr Int) Bool)
(assert (forall ((var0 TData) (var1 Addr) (var2 Heap)) (or (not (and (= var2 emptyHeap) (= var1 nullAddr))) (inv_main545_5 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 TData) (var4 Addr) (var5 Heap) (var6 Int) (var7 TData) (var8 Addr) (var9 Heap) (var10 Addr) (var11 Int) (var12 TData) (var13 Bool) (var14 Addr) (var15 Int) (var16 Heap) (var17 Addr) (var18 Int) (var19 Int) (var20 TData) (var21 TData) (var22 Addr) (var23 Bool) (var24 Addr) (var25 Int) (var26 Heap) (var27 Heap) (var28 TData) (var29 Addr) (var30 Heap) (var31 Addr) (var32 TData) (var33 TData) (var34 Addr) (var35 Heap) (var36 Addr) (var37 Addr) (var38 Addr) (var39 TData) (var40 TData) (var41 TData) (var42 TData) (var43 Addr) (var44 Addr) (var45 Heap) (var46 Addr) (var47 Heap) (var48 Int) (var49 TData) (var50 Addr) (var51 Heap)) (or (not (and (inv_main545_5 var51 var50 var49) (and (and (and (and (and (<= 0 (+ (+ var48 (* (- 1) (getInt (read var47 var46)))) (- 1))) (and (and (and (and (and (and (= var47 var45) (= var44 var43)) (= var42 var41)) (= var40 var39)) (= var38 var37)) (= var46 var36)) (= var48 (getInt (read var45 var37))))) (and (and (and (and (and (= var45 var35) (= var43 var34)) (= var41 var33)) (= var39 var32)) (= var37 var31)) (= var36 (|TData::hi| var32)))) (and (and (and (and (= var35 var30) (= var34 var29)) (= var33 var28)) (= var32 var28)) (= var31 (|TData::lo| var28)))) (and (and (and (and (and (and (and (and (and (= var27 (newHeap (alloc var26 (O_Int var25)))) (or (and var23 (= var24 (newAddr (alloc var26 (O_Int var25))))) (and (not var23) (= var24 var22)))) (= var21 var20)) (= var19 var18)) (= var17 (newAddr (alloc var26 (O_Int var25))))) (and (and (and (and (= var16 (newHeap (alloc var51 (O_Int var15)))) (or (and var13 (= var14 (newAddr (alloc var51 (O_Int var15))))) (and (not var13) (= var14 var50)))) (= var12 var49)) (= var11 2)) (= var10 (newAddr (alloc var51 (O_Int var15)))))) (and (and (and (= var26 var16) (= var22 var14)) (= var20 (TData var10 (|TData::hi| var12)))) (= var18 var11))) (and (and (and (= var9 var27) (= var8 var24)) (= var7 (TData (|TData::lo| var21) var17))) (= var6 var19))) (and (and (and (= var5 (write var9 (|TData::lo| var7) (O_Int 4))) (= var4 var8)) (= var3 var7)) (= var2 var6))) (and (and (and (= var30 (write var5 (|TData::hi| var3) (O_Int 8))) (= var29 var4)) (= var28 var3)) (= var1 var2)))) (= var0 0)))) (inv_main547_12 var47 var44 var0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 TData) (var4 Addr) (var5 Heap) (var6 Int) (var7 TData) (var8 Addr) (var9 Heap) (var10 Addr) (var11 Int) (var12 TData) (var13 Bool) (var14 Addr) (var15 Int) (var16 Heap) (var17 Addr) (var18 Int) (var19 Int) (var20 TData) (var21 TData) (var22 Addr) (var23 Bool) (var24 Addr) (var25 Int) (var26 Heap) (var27 Heap) (var28 TData) (var29 TData) (var30 Addr) (var31 Heap) (var32 TData) (var33 Addr) (var34 Heap) (var35 Addr) (var36 Addr) (var37 TData) (var38 TData) (var39 Addr) (var40 Heap) (var41 Addr) (var42 TData) (var43 TData) (var44 Addr) (var45 Heap) (var46 Addr) (var47 Addr) (var48 Addr) (var49 TData) (var50 TData) (var51 TData) (var52 TData) (var53 Addr) (var54 Addr) (var55 Heap) (var56 Addr) (var57 Heap) (var58 Int) (var59 TData) (var60 Addr) (var61 Heap)) (or (not (and (inv_main545_5 var61 var60 var59) (and (and (and (and (and (and (and (not (<= 0 (+ (+ var58 (* (- 1) (getInt (read var57 var56)))) (- 1)))) (and (and (and (and (and (and (= var57 var55) (= var54 var53)) (= var52 var51)) (= var50 var49)) (= var48 var47)) (= var56 var46)) (= var58 (getInt (read var55 var47))))) (and (and (and (and (and (= var55 var45) (= var53 var44)) (= var51 var43)) (= var49 var42)) (= var47 var41)) (= var46 (|TData::hi| var42)))) (and (and (and (and (and (= var40 (write var57 var48 defObj)) (or (and (= var54 var48) (= var39 nullAddr)) (and (not (= var54 var48)) (= var39 var54)))) (= var38 var52)) (= var37 var50)) (= var36 var48)) (= var35 var56))) (and (and (and (and (= var45 var34) (= var44 var33)) (= var43 var32)) (= var42 var32)) (= var41 (|TData::lo| var32)))) (and (and (and (= var31 (write var40 var35 defObj)) (or (and (= var39 var35) (= var30 nullAddr)) (and (not (= var39 var35)) (= var30 var39)))) (= var29 var38)) (= var28 var37))) (and (and (and (and (and (and (and (and (and (= var27 (newHeap (alloc var26 (O_Int var25)))) (or (and var23 (= var24 (newAddr (alloc var26 (O_Int var25))))) (and (not var23) (= var24 var22)))) (= var21 var20)) (= var19 var18)) (= var17 (newAddr (alloc var26 (O_Int var25))))) (and (and (and (and (= var16 (newHeap (alloc var61 (O_Int var15)))) (or (and var13 (= var14 (newAddr (alloc var61 (O_Int var15))))) (and (not var13) (= var14 var60)))) (= var12 var59)) (= var11 2)) (= var10 (newAddr (alloc var61 (O_Int var15)))))) (and (and (and (= var26 var16) (= var22 var14)) (= var20 (TData var10 (|TData::hi| var12)))) (= var18 var11))) (and (and (and (= var9 var27) (= var8 var24)) (= var7 (TData (|TData::lo| var21) var17))) (= var6 var19))) (and (and (and (= var5 (write var9 (|TData::lo| var7) (O_Int 4))) (= var4 var8)) (= var3 var7)) (= var2 var6))) (and (and (and (= var34 (write var5 (|TData::hi| var3) (O_Int 8))) (= var33 var4)) (= var32 var3)) (= var1 var2)))) (= var0 0)))) (inv_main547_12 var31 var30 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap)) (not (and (inv_main547_12 var2 var1 var0) (not (= var1 nullAddr))))))
(check-sat)
