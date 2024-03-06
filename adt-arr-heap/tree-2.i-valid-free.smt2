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
   (O_AddrRange (getAddrRange AddrRange))
   (O_node (getnode node))
   (defObj)
  )
  (
   (node (|node::left| Addr) (|node::right| Addr) (|node::parent| Addr) (|node::value| Int))
  )
))
(declare-fun inv_main (Heap Addr Addr) Bool)
(declare-fun inv_main586_5 (Heap Addr Addr) Bool)
(declare-fun inv_main612_5 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main619_13 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main621_13 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main630_5 (Heap) Bool)
(declare-fun inv_main_23 (Heap Addr Addr) Bool)
(declare-fun inv_main_39 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main_44 (Heap Addr Addr Addr) Bool)
(assert (forall ((var0 Heap)) (or (not (= var0 emptyHeap)) (inv_main630_5 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main_39 var3 var2 var1 var0) (and (not (= (|node::left| (getnode (read var3 var1))) nullAddr)) (not (= var1 nullAddr))))) (inv_main619_13 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Heap)) (or (not (and (inv_main612_5 var13 var12 var11 var10) (and (and (and (and (and (= var9 var8) (= var7 var6)) (= var5 var4)) (= var3 var2)) (= var1 (|node::right| (getnode (read var8 var4))))) (and (not (= var0 nullAddr)) (and (and (and (and (= var8 var13) (= var6 var12)) (= var4 var11)) (= var2 var10)) (= var0 (|node::right| (getnode (read var13 var11))))))))) (inv_main612_5 var9 var7 var1 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main_23 var3 var2 var1) (and (= var1 nullAddr) (= var0 nullAddr)))) (inv_main612_5 var3 var2 var2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main_23 var6 var5 var4) (and (and (and (and (= var3 var6) (= var2 var5)) (= var1 var4)) (= var0 (|node::parent| (getnode (read var6 var4))))) (and (not (= (|node::value| (getnode (read var6 var4))) 0)) (and (= (|node::left| (getnode (read var6 var4))) nullAddr) (not (= var4 nullAddr))))))) (inv_main_23 var3 var2 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Heap)) (or (not (and (inv_main_23 var10 var9 var8) (and (and (and (and (= var7 var6) (= var5 var4)) (= var3 var2)) (= var1 (|node::parent| (getnode (read var6 var2))))) (and (not (= (|node::value| (getnode (read var6 var2))) 0)) (and (and (= var0 42) (and (and (and (= var6 var10) (= var4 var9)) (= var2 var8)) (= var0 (|node::value| (getnode (read var10 (|node::left| (getnode (read var10 var8))))))))) (and (not (= (|node::left| (getnode (read var10 var8))) nullAddr)) (not (= var8 nullAddr)))))))) (inv_main_23 var7 var5 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (and (inv_main var2 var1 var0) (and (not (= var1 nullAddr)) (and (not (= var1 nullAddr)) (= var0 nullAddr))))) (inv_main_23 var2 var1 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main586_5 var3 var2 var1) (= var0 0))) (inv_main var3 var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Heap) (var9 Addr) (var10 Heap) (var11 Addr) (var12 Addr) (var13 Addr) (var14 node) (var15 Heap) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Heap) (var23 Heap) (var24 Addr) (var25 Addr) (var26 Heap)) (or (not (and (inv_main var26 var25 var24) (and (and (and (and (and (= var23 var22) (= var21 var20)) (= var19 var18)) (= var17 (|node::right| (getnode (read var22 var18))))) (and (and (and (and (and (not (= var16 nullAddr)) (and (and (and (and (= var15 (newHeap (alloc var26 (O_node var14)))) (= var13 var25)) (= var12 var24)) (= var11 (newAddr (alloc var26 (O_node var14))))) (not (= var24 nullAddr)))) (and (and (= var10 (write var15 var12 (O_node (node var11 (|node::right| (getnode (read var15 var12))) (|node::parent| (getnode (read var15 var12))) (|node::value| (getnode (read var15 var12))))))) (= var9 var13)) (= var16 var12))) (and (and (= var8 (write var10 (|node::left| (getnode (read var10 var16))) (O_node (node nullAddr (|node::right| (getnode (read var10 (|node::left| (getnode (read var10 var16)))))) (|node::parent| (getnode (read var10 (|node::left| (getnode (read var10 var16)))))) (|node::value| (getnode (read var10 (|node::left| (getnode (read var10 var16)))))))))) (= var7 var9)) (= var6 var16))) (and (and (= var5 (write var8 (|node::left| (getnode (read var8 var6))) (O_node (node (|node::left| (getnode (read var8 (|node::left| (getnode (read var8 var6)))))) nullAddr (|node::parent| (getnode (read var8 (|node::left| (getnode (read var8 var6)))))) (|node::value| (getnode (read var8 (|node::left| (getnode (read var8 var6)))))))))) (= var4 var7)) (= var3 var6))) (and (and (= var2 (write var5 (|node::left| (getnode (read var5 var3))) (O_node (node (|node::left| (getnode (read var5 (|node::left| (getnode (read var5 var3)))))) (|node::right| (getnode (read var5 (|node::left| (getnode (read var5 var3)))))) (|node::parent| (getnode (read var5 (|node::left| (getnode (read var5 var3)))))) 42)))) (= var1 var4)) (= var0 var3)))) (and (and (= var22 (write var2 (|node::left| (getnode (read var2 var0))) (O_node (node (|node::left| (getnode (read var2 (|node::left| (getnode (read var2 var0)))))) (|node::right| (getnode (read var2 (|node::left| (getnode (read var2 var0)))))) var0 (|node::value| (getnode (read var2 (|node::left| (getnode (read var2 var0)))))))))) (= var20 var1)) (= var18 var0))))) (inv_main var23 var21 var17))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main619_13 var7 var6 var5 var4) (and (not (= (|node::right| (getnode (read var3 var2))) nullAddr)) (and (and (and (= var3 (write var7 (|node::left| (getnode (read var7 var5))) defObj)) (= var1 var6)) (= var2 var5)) (= var0 var4))))) (inv_main621_13 var3 var1 var2 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main_39 var3 var2 var1 var0) (and (not (= (|node::right| (getnode (read var3 var1))) nullAddr)) (and (= (|node::left| (getnode (read var3 var1))) nullAddr) (not (= var1 nullAddr)))))) (inv_main621_13 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main612_5 var8 var7 var6 var5) (and (= var4 nullAddr) (and (and (and (and (= var3 var8) (= var2 var7)) (= var1 var6)) (= var0 var5)) (= var4 (|node::right| (getnode (read var8 var6)))))))) (inv_main_39 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Heap)) (or (not (and (inv_main621_13 var12 var11 var10 var9) (and (and (and (and (and (= var8 var7) (= var6 var5)) (= var4 var3)) (= var2 var3)) (= var1 (|node::parent| (getnode (read var7 var3))))) (and (and (and (= var7 (write var12 (|node::right| (getnode (read var12 var10))) defObj)) (= var5 var11)) (= var3 var10)) (= var0 var9))))) (inv_main_39 var8 var6 var1 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Heap)) (or (not (and (inv_main619_13 var12 var11 var10 var9) (and (and (and (and (and (= var8 var7) (= var6 var5)) (= var4 var3)) (= var2 var3)) (= var1 (|node::parent| (getnode (read var7 var3))))) (and (= (|node::right| (getnode (read var7 var3))) nullAddr) (and (and (and (= var7 (write var12 (|node::left| (getnode (read var12 var10))) defObj)) (= var5 var11)) (= var3 var10)) (= var0 var9)))))) (inv_main_39 var8 var6 var1 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main_39 var8 var7 var6 var5) (and (and (and (and (and (= var4 var8) (= var3 var7)) (= var2 var6)) (= var1 var6)) (= var0 (|node::parent| (getnode (read var8 var6))))) (and (= (|node::right| (getnode (read var8 var6))) nullAddr) (and (= (|node::left| (getnode (read var8 var6))) nullAddr) (not (= var6 nullAddr))))))) (inv_main_39 var4 var3 var0 var1))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Int) (var6 Addr) (var7 Addr) (var8 node) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Int) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Int) (var17 Addr) (var18 Heap) (var19 Heap) (var20 Addr) (var21 Addr) (var22 Heap)) (or (not (and (inv_main586_5 var22 var21 var20) (and (and (and (and (and (= var19 (write var18 var17 (O_node (node (|node::left| (getnode (read var18 var17))) (|node::right| (getnode (read var18 var17))) (|node::parent| (getnode (read var18 var17))) var16)))) (= var15 var14)) (= var13 var17)) (= var12 var16)) (and (and (not (= var11 nullAddr)) (and (and (not (= var10 nullAddr)) (and (and (and (and (= var9 (newHeap (alloc var22 (O_node var8)))) (= var7 var21)) (= var6 var20)) (= var10 (newAddr (alloc var22 (O_node var8))))) (not (= var5 0)))) (and (and (= var4 (write var9 var10 (O_node (node nullAddr (|node::right| (getnode (read var9 var10))) (|node::parent| (getnode (read var9 var10))) (|node::value| (getnode (read var9 var10))))))) (= var3 var7)) (= var2 var10)))) (and (and (= var1 (write var4 var2 (O_node (node (|node::left| (getnode (read var4 var2))) var3 (|node::parent| (getnode (read var4 var2))) (|node::value| (getnode (read var4 var2))))))) (= var11 var3)) (= var0 var2)))) (and (and (= var18 (write var1 var11 (O_node (node (|node::left| (getnode (read var1 var11))) (|node::right| (getnode (read var1 var11))) var0 (|node::value| (getnode (read var1 var11))))))) (= var14 var11)) (= var17 var0))))) (inv_main586_5 var19 var13 var13))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Int) (var4 Addr) (var5 Addr) (var6 node) (var7 Heap) (var8 Addr) (var9 Int) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Int) (var14 Addr) (var15 Heap) (var16 Heap) (var17 Addr) (var18 Addr) (var19 Heap)) (or (not (and (inv_main586_5 var19 var18 var17) (and (and (and (and (= var16 (write var15 var14 (O_node (node (|node::left| (getnode (read var15 var14))) (|node::right| (getnode (read var15 var14))) (|node::parent| (getnode (read var15 var14))) var13)))) (= var12 var11)) (= var10 var14)) (= var9 var13)) (and (and (= var11 nullAddr) (and (and (not (= var8 nullAddr)) (and (and (and (and (= var7 (newHeap (alloc var19 (O_node var6)))) (= var5 var18)) (= var4 var17)) (= var8 (newAddr (alloc var19 (O_node var6))))) (not (= var3 0)))) (and (and (= var2 (write var7 var8 (O_node (node nullAddr (|node::right| (getnode (read var7 var8))) (|node::parent| (getnode (read var7 var8))) (|node::value| (getnode (read var7 var8))))))) (= var1 var5)) (= var0 var8)))) (and (and (= var15 (write var2 var0 (O_node (node (|node::left| (getnode (read var2 var0))) var1 (|node::parent| (getnode (read var2 var0))) (|node::value| (getnode (read var2 var0))))))) (= var11 var1)) (= var14 var0)))))) (inv_main586_5 var16 var10 var10))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Heap)) (or (not (and (inv_main630_5 var3) (and (and (= var2 var3) (= var1 nullAddr)) (= var0 nullAddr)))) (inv_main586_5 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main_39 var3 var2 var1 var0) (= var1 nullAddr))) (inv_main_44 var3 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main619_13 var3 var2 var1 var0) (and (not (= (|node::left| (getnode (read var3 var1))) nullAddr)) (= (read var3 (|node::left| (getnode (read var3 var1)))) defObj))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main621_13 var3 var2 var1 var0) (and (not (= (|node::right| (getnode (read var3 var1))) nullAddr)) (= (read var3 (|node::right| (getnode (read var3 var1)))) defObj))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_44 var3 var2 var1 var0) (and (not (= var0 nullAddr)) (= (read var3 var0) defObj))))))
(check-sat)
