(set-logic HORN)
(set-info :source |
    Benchmark: 
    Output by Princess (http://www.philipp.ruemmer.org/princess.shtml)
|)
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
   (node (|node::h| Int) (|node::n| Addr))
  )
))
(declare-fun inv_main_16 (Heap Int Addr Addr) Bool)
(declare-fun inv_main536_3 (Heap Int Addr Addr) Bool)
(declare-fun _Glue2 (Heap Addr HeapObject) Bool)
(declare-fun _Glue12 (Addr Addr Addr Heap HeapObject) Bool)
(declare-fun _Glue1 (Heap Addr HeapObject) Bool)
(declare-fun inv_main_29 (Heap Addr Addr) Bool)
(declare-fun _Glue9_exp_exp (Addr Int Addr Addr Heap Addr HeapObject) Bool)
(declare-fun Inv_Heap (Addr HeapObject) Bool)
(declare-fun _Glue6 (Addr Int Addr Addr Heap HeapObject) Bool)
(declare-fun _Glue3_exp_exp (Addr Int Addr Addr Int Heap Addr HeapObject) Bool)
(declare-fun inv_main_27 (Heap Addr) Bool)
(declare-fun _Glue8 (Addr Addr Heap Addr HeapObject) Bool)
(assert (forall ((var0 Addr) (var1 Int) (var2 Heap) (var3 HeapObject) (var4 Addr)) (or (not (and (and (Inv_Heap var4 var3) (inv_main_16 var2 var1 var0 var4)) (and (= (read var2 var4) var3) (valid var2 var4)))) (_Glue1 var2 var0 var3))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap)) (or (not (and (inv_main_16 var4 var3 var2 var1) (and (= (read var4 var1) var0) (not (valid var4 var1))))) (_Glue1 var4 var2 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 node) (var3 node) (var4 HeapObject) (var5 Heap) (var6 HeapObject) (var7 Addr)) (or (not (and (and (Inv_Heap var7 var6) (_Glue1 var5 var7 var4)) (and (and (and (and (and (and (and (= (getnode var4) var3) (= (|node::h| var3) 3)) (= (read var5 var7) var6)) (= (getnode var6) var2)) (= (|node::n| var2) var1)) (= (|node::h| var2) var0)) (not (= var0 3))) (valid var5 var7)))) (inv_main_29 var5 var1 var7))))
(assert (forall ((var0 Int) (var1 Addr) (var2 node) (var3 HeapObject) (var4 node) (var5 HeapObject) (var6 Addr) (var7 Heap)) (or (not (and (_Glue1 var7 var6 var5) (and (and (and (and (and (and (and (= (getnode var5) var4) (= (|node::h| var4) 3)) (= (read var7 var6) var3)) (= (getnode var3) var2)) (= (|node::n| var2) var1)) (= (|node::h| var2) var0)) (not (= var0 3))) (not (valid var7 var6))))) (inv_main_29 var7 var1 var6))))
(assert (forall ((var0 Int) (var1 Addr) (var2 node) (var3 Addr) (var4 Int) (var5 Heap) (var6 HeapObject) (var7 Addr)) (or (not (and (and (Inv_Heap var7 var6) (inv_main_16 var5 var4 var3 var7)) (and (and (and (and (and (and (= (read var5 var7) var6) (= (getnode var6) var2)) (= (|node::h| var2) 1)) (= (|node::n| var2) var1)) (not (= var4 0))) (valid var5 var7)) (= var0 0)))) (inv_main_16 var5 var0 var3 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 node) (var3 HeapObject) (var4 Addr) (var5 Addr) (var6 Int) (var7 Heap)) (or (not (and (inv_main_16 var7 var6 var5 var4) (and (and (and (and (and (and (= (read var7 var4) var3) (= (getnode var3) var2)) (= (|node::h| var2) 1)) (= (|node::n| var2) var1)) (not (= var6 0))) (not (valid var7 var4))) (= var0 0)))) (inv_main_16 var7 var0 var5 var1))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 HeapObject) (var3 Addr)) (not (and (and (Inv_Heap var3 var2) (inv_main_27 var1 var3)) (and (and (and (and (not (= var3 var0)) (= (read var1 var3) var2)) (= defObj var2)) (= nullAddr var0)) (valid var1 var3))))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Heap)) (not (and (inv_main_27 var3 var2) (and (and (and (and (not (= var2 var1)) (= (read var3 var2) var0)) (= defObj var0)) (= nullAddr var1)) (not (valid var3 var2)))))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main_29 var3 var2 var1) (and (= defObj var0) (valid var3 var1)))) (Inv_Heap var1 var0))))
(assert (forall ((var0 HeapObject) (var1 Int) (var2 Addr) (var3 node) (var4 Heap) (var5 Addr) (var6 Heap) (var7 HeapObject) (var8 Addr)) (or (not (and (and (Inv_Heap var8 var7) (inv_main_29 var6 var8 var5)) (and (and (and (and (and (and (and (and (= (read var4 var8) var7) (= (getnode var7) var3)) (= (|node::n| var3) var2)) (= (|node::h| var3) var1)) (not (= var1 3))) (valid var4 var8)) true) (= defObj var0)) (= (write var6 var5 var0) var4)))) (inv_main_29 var4 var2 var8))))
(assert (forall ((var0 HeapObject) (var1 Int) (var2 Addr) (var3 node) (var4 HeapObject) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main_29 var8 var7 var6) (and (and (and (and (and (and (and (= (read var5 var7) var4) (= (getnode var4) var3)) (= (|node::n| var3) var2)) (= (|node::h| var3) var1)) (not (= var1 3))) (not (valid var5 var7))) (= defObj var0)) (= (write var8 var6 var0) var5)))) (inv_main_29 var5 var2 var7))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Heap)) (or (not (and (inv_main_29 var3 var2 var1) (and (= defObj var0) (valid var3 var1)))) (Inv_Heap var1 var0))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Heap) (var3 Addr) (var4 Heap) (var5 HeapObject) (var6 Addr)) (or (not (and (and (Inv_Heap var6 var5) (inv_main_29 var4 var6 var3)) (and (and (and (and (and (and (= (read var2 var6) var5) (= (getnode var5) var1)) (= (|node::h| var1) 3)) (valid var2 var6)) true) (= defObj var0)) (= (write var4 var3 var0) var2)))) (inv_main_27 var2 var6))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 HeapObject) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main_29 var6 var5 var4) (and (and (and (and (and (= (read var3 var5) var2) (= (getnode var2) var1)) (= (|node::h| var1) 3)) (not (valid var3 var5))) (= defObj var0)) (= (write var6 var4 var0) var3)))) (inv_main_27 var3 var5))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 HeapObject) (var4 Addr)) (not (and (and (Inv_Heap var4 var3) (inv_main_29 var2 var1 var4)) (and (and (and (and (not (= var4 var0)) (= (read var2 var4) var3)) (= defObj var3)) (= nullAddr var0)) (valid var2 var4))))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main_29 var4 var3 var2) (and (and (and (and (not (= var2 var1)) (= (read var4 var2) var0)) (= defObj var0)) (= nullAddr var1)) (not (valid var4 var2)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Heap) (var3 HeapObject) (var4 Addr)) (or (not (and (and (Inv_Heap var4 var3) (inv_main_16 var2 var1 var0 var4)) (and (= (read var2 var4) var3) (valid var2 var4)))) (_Glue2 var2 var0 var3))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap)) (or (not (and (inv_main_16 var4 var3 var2 var1) (and (= (read var4 var1) var0) (not (valid var4 var1))))) (_Glue2 var4 var2 var0))))
(assert (forall ((var0 node) (var1 node) (var2 HeapObject) (var3 Heap) (var4 HeapObject) (var5 Addr)) (or (not (and (and (Inv_Heap var5 var4) (_Glue2 var3 var5 var2)) (and (and (and (and (and (= (getnode var2) var1) (= (|node::h| var1) 3)) (= (read var3 var5) var4)) (= (getnode var4) var0)) (= (|node::h| var0) 3)) (valid var3 var5)))) (inv_main_27 var3 var5))))
(assert (forall ((var0 node) (var1 HeapObject) (var2 node) (var3 HeapObject) (var4 Addr) (var5 Heap)) (or (not (and (_Glue2 var5 var4 var3) (and (and (and (and (and (= (getnode var3) var2) (= (|node::h| var2) 3)) (= (read var5 var4) var1)) (= (getnode var1) var0)) (= (|node::h| var0) 3)) (not (valid var5 var4))))) (inv_main_27 var5 var4))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap) (var4 HeapObject) (var5 Addr)) (or (not (and (and (Inv_Heap var5 var4) (inv_main536_3 var3 var2 var1 var5)) (and (= (read var3 var5) var4) (valid var3 var5)))) (_Glue8 var0 var1 var3 var5 var4))))
(assert (forall ((var0 Addr) (var1 HeapObject) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap)) (or (not (and (inv_main536_3 var5 var4 var3 var2) (and (= (read var5 var2) var1) (not (valid var5 var2))))) (_Glue8 var0 var3 var5 var2 var1))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Addr) (var3 node) (var4 HeapObject) (var5 Addr) (var6 Heap) (var7 Addr)) (or (not (and (_Glue8 var7 var7 var6 var5 var4) (and (and (and (and (= (getnode var4) var3) (= (|node::n| var3) var2)) (= (node 3 var2) var1)) (= (O_node var1) var0)) (valid var6 var5)))) (Inv_Heap var5 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 HeapObject) (var4 node) (var5 Addr) (var6 node) (var7 HeapObject) (var8 Addr) (var9 Heap) (var10 Addr)) (or (not (and (_Glue8 var10 var10 var9 var8 var7) (and (and (and (and (and (and (= (getnode var7) var6) (= (|node::n| var6) var5)) (= (node 3 var5) var4)) (= (O_node var4) var3)) (= (write var9 var8 var3) var2)) (= var1 var10)) (= var0 1)))) (inv_main_16 var2 var0 var1 var10))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 AllocResHeap) (var3 Heap) (var4 HeapObject) (var5 node)) (or (not (and (and (and (and (and (= (O_node var5) var4) (= (alloc var3 var4) var2)) (= (newAddr var2) var1)) (not (= var1 var0))) (= nullAddr var0)) (= emptyHeap var3))) (Inv_Heap (newAddr var2) var4))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 AllocResHeap) (var6 Heap) (var7 HeapObject) (var8 node)) (or (not (and (and (and (and (and (and (and (and (= (O_node var8) var7) (= (alloc var6 var7) var5)) (= (newHeap var5) var4)) (= (newAddr var5) var3)) (not (= var3 var2))) (= nullAddr var2)) (= emptyHeap var6)) (= var1 var3)) (= var0 1))) (inv_main536_3 var4 var0 var1 var3))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Int) (var5 Heap) (var6 HeapObject) (var7 Addr)) (or (not (and (and (Inv_Heap var7 var6) (inv_main536_3 var5 var4 var3 var7)) (and (and (= nullAddr var2) (= (read var5 var7) var6)) (valid var5 var7)))) (_Glue3_exp_exp var2 var1 var0 var3 var4 var5 var7 var6))))
(assert (forall ((var0 Addr) (var1 Int) (var2 HeapObject) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Int) (var7 Heap)) (or (not (and (inv_main536_3 var7 var6 var5 var4) (and (and (= nullAddr var3) (= (read var7 var4) var2)) (not (valid var7 var4))))) (_Glue3_exp_exp var3 var1 var0 var5 var6 var7 var4 var2))))
(assert (forall ((var0 node) (var1 HeapObject) (var2 node) (var3 Addr) (var4 HeapObject) (var5 Addr) (var6 Heap) (var7 Int) (var8 Addr) (var9 Addr) (var10 Int) (var11 Addr)) (or (not (and (_Glue3_exp_exp var11 var10 var9 var8 var7 var6 var5 var4) (and (and (and (and (= (node 1 var3) var2) (= (O_node var2) var1)) (= (getnode var4) var0)) (= (|node::n| var0) var3)) (valid var6 var5)))) (Inv_Heap var5 var1))))
(assert (forall ((var0 node) (var1 AllocResHeap) (var2 Heap) (var3 HeapObject) (var4 node) (var5 Addr) (var6 HeapObject) (var7 node) (var8 HeapObject) (var9 Addr) (var10 Heap) (var11 Int) (var12 Addr) (var13 Addr) (var14 Int) (var15 Addr)) (or (not (and (_Glue3_exp_exp var15 var14 var13 var12 var11 var10 var9 var8) (and (and (and (and (and (and (and (= (O_node var7) var6) (= (node 1 var5) var4)) (= (O_node var4) var3)) (= (node var14 var13) var7)) (= (alloc var2 var6) var1)) (= (getnode var8) var0)) (= (|node::n| var0) var5)) (= (write var10 var9 var3) var2)))) (Inv_Heap (newAddr var1) var6))))
(assert (forall ((var0 node) (var1 Heap) (var2 HeapObject) (var3 node) (var4 Addr) (var5 HeapObject) (var6 node) (var7 AllocResHeap) (var8 Addr) (var9 Heap) (var10 HeapObject) (var11 Heap) (var12 Int) (var13 Addr) (var14 Addr) (var15 Int) (var16 Addr) (var17 HeapObject) (var18 Addr)) (or (not (and (and (Inv_Heap var18 var17) (_Glue3_exp_exp var16 var15 var14 var13 var12 var11 var18 var10)) (and (and (and (and (and (and (and (and (and (and (and (= (AllocResHeap var9 var8) var7) (= (O_node var6) var5)) (= (node 1 var4) var3)) (= (O_node var3) var2)) (= (node var15 var14) var6)) (not (= var8 var16))) (= (read var9 var18) var17)) (valid var9 var18)) (= (alloc var1 var5) var7)) (= (getnode var10) var0)) (= (|node::n| var0) var4)) (= (write var11 var18 var2) var1)))) (_Glue6 var18 var12 var13 var8 var9 var17))))
(assert (forall ((var0 node) (var1 Heap) (var2 HeapObject) (var3 HeapObject) (var4 node) (var5 Addr) (var6 HeapObject) (var7 node) (var8 AllocResHeap) (var9 Addr) (var10 Heap) (var11 HeapObject) (var12 Addr) (var13 Heap) (var14 Int) (var15 Addr) (var16 Addr) (var17 Int) (var18 Addr)) (or (not (and (_Glue3_exp_exp var18 var17 var16 var15 var14 var13 var12 var11) (and (and (and (and (and (and (and (and (and (and (and (= (AllocResHeap var10 var9) var8) (= (O_node var7) var6)) (= (node 1 var5) var4)) (= (O_node var4) var3)) (= (node var17 var16) var7)) (not (= var9 var18))) (= (read var10 var12) var2)) (not (valid var10 var12))) (= (alloc var1 var6) var8)) (= (getnode var11) var0)) (= (|node::n| var0) var5)) (= (write var13 var12 var3) var1)))) (_Glue6 var12 var14 var15 var9 var10 var2))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Int) (var3 node) (var4 HeapObject) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Int) (var9 Addr)) (or (not (and (_Glue6 var9 var8 var7 var6 var5 var4) (and (and (and (and (= (getnode var4) var3) (= (|node::h| var3) var2)) (= (node var2 var6) var1)) (= (O_node var1) var0)) (valid var5 var9)))) (Inv_Heap var9 var0))))
(assert (forall ((var0 Int) (var1 HeapObject) (var2 node) (var3 Int) (var4 node) (var5 Addr) (var6 node) (var7 Heap) (var8 HeapObject) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Int) (var13 HeapObject) (var14 Addr)) (or (not (and (and (Inv_Heap var14 var13) (_Glue6 var14 var12 var11 var10 var9 var8)) (and (and (and (and (and (and (and (and (and (and (= (read var7 var14) var13) (= (getnode var13) var6)) (= (|node::n| var6) var5)) (not (= var12 0))) (valid var7 var14)) (= (getnode var8) var4)) (= (|node::h| var4) var3)) (= (node var3 var10) var2)) (= (O_node var2) var1)) (= (write var9 var14 var1) var7)) (= var0 0)))) (inv_main536_3 var7 var0 var11 var5))))
(assert (forall ((var0 Int) (var1 HeapObject) (var2 node) (var3 Int) (var4 node) (var5 Addr) (var6 node) (var7 HeapObject) (var8 Heap) (var9 HeapObject) (var10 Heap) (var11 Addr) (var12 Addr) (var13 Int) (var14 Addr)) (or (not (and (_Glue6 var14 var13 var12 var11 var10 var9) (and (and (and (and (and (and (and (and (and (and (= (read var8 var14) var7) (= (getnode var7) var6)) (= (|node::n| var6) var5)) (not (= var13 0))) (not (valid var8 var14))) (= (getnode var9) var4)) (= (|node::h| var4) var3)) (= (node var3 var11) var2)) (= (O_node var2) var1)) (= (write var10 var14 var1) var8)) (= var0 0)))) (inv_main536_3 var8 var0 var12 var5))))
(assert (forall ((var0 Int) (var1 Addr) (var2 node) (var3 Addr) (var4 Heap) (var5 HeapObject) (var6 Addr)) (or (not (and (and (Inv_Heap var6 var5) (inv_main_16 var4 0 var3 var6)) (and (and (and (and (and (= (read var4 var6) var5) (= (getnode var5) var2)) (= (|node::h| var2) 2)) (= (|node::n| var2) var1)) (valid var4 var6)) (= var0 1)))) (inv_main_16 var4 var0 var3 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 node) (var3 HeapObject) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main_16 var6 0 var5 var4) (and (and (and (and (and (= (read var6 var4) var3) (= (getnode var3) var2)) (= (|node::h| var2) 2)) (= (|node::n| var2) var1)) (not (valid var6 var4))) (= var0 1)))) (inv_main_16 var6 var0 var5 var1))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap) (var5 HeapObject) (var6 Addr)) (or (not (and (and (Inv_Heap var6 var5) (inv_main536_3 var4 0 var3 var6)) (and (and (= nullAddr var2) (= (read var4 var6) var5)) (valid var4 var6)))) (_Glue9_exp_exp var2 var1 var0 var3 var4 var6 var5))))
(assert (forall ((var0 Addr) (var1 Int) (var2 HeapObject) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main536_3 var6 0 var5 var4) (and (and (= nullAddr var3) (= (read var6 var4) var2)) (not (valid var6 var4))))) (_Glue9_exp_exp var3 var1 var0 var5 var6 var4 var2))))
(assert (forall ((var0 node) (var1 HeapObject) (var2 node) (var3 Addr) (var4 HeapObject) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Int) (var10 Addr)) (or (not (and (_Glue9_exp_exp var10 var9 var8 var7 var6 var5 var4) (and (and (and (and (= (node 2 var3) var2) (= (O_node var2) var1)) (= (getnode var4) var0)) (= (|node::n| var0) var3)) (valid var6 var5)))) (Inv_Heap var5 var1))))
(assert (forall ((var0 node) (var1 AllocResHeap) (var2 Heap) (var3 HeapObject) (var4 node) (var5 Addr) (var6 HeapObject) (var7 node) (var8 HeapObject) (var9 Addr) (var10 Heap) (var11 Addr) (var12 Addr) (var13 Int) (var14 Addr)) (or (not (and (_Glue9_exp_exp var14 var13 var12 var11 var10 var9 var8) (and (and (and (and (and (and (and (= (O_node var7) var6) (= (node 2 var5) var4)) (= (O_node var4) var3)) (= (node var13 var12) var7)) (= (alloc var2 var6) var1)) (= (getnode var8) var0)) (= (|node::n| var0) var5)) (= (write var10 var9 var3) var2)))) (Inv_Heap (newAddr var1) var6))))
(assert (forall ((var0 node) (var1 Heap) (var2 HeapObject) (var3 node) (var4 Addr) (var5 HeapObject) (var6 node) (var7 AllocResHeap) (var8 Addr) (var9 Heap) (var10 HeapObject) (var11 Heap) (var12 Addr) (var13 Addr) (var14 Int) (var15 Addr) (var16 HeapObject) (var17 Addr)) (or (not (and (and (Inv_Heap var17 var16) (_Glue9_exp_exp var15 var14 var13 var12 var11 var17 var10)) (and (and (and (and (and (and (and (and (and (and (and (= (AllocResHeap var9 var8) var7) (= (O_node var6) var5)) (= (node 2 var4) var3)) (= (O_node var3) var2)) (= (node var14 var13) var6)) (not (= var8 var15))) (= (read var9 var17) var16)) (valid var9 var17)) (= (alloc var1 var5) var7)) (= (getnode var10) var0)) (= (|node::n| var0) var4)) (= (write var11 var17 var2) var1)))) (_Glue12 var17 var12 var8 var9 var16))))
(assert (forall ((var0 node) (var1 Heap) (var2 HeapObject) (var3 HeapObject) (var4 node) (var5 Addr) (var6 HeapObject) (var7 node) (var8 AllocResHeap) (var9 Addr) (var10 Heap) (var11 HeapObject) (var12 Addr) (var13 Heap) (var14 Addr) (var15 Addr) (var16 Int) (var17 Addr)) (or (not (and (_Glue9_exp_exp var17 var16 var15 var14 var13 var12 var11) (and (and (and (and (and (and (and (and (and (and (and (= (AllocResHeap var10 var9) var8) (= (O_node var7) var6)) (= (node 2 var5) var4)) (= (O_node var4) var3)) (= (node var16 var15) var7)) (not (= var9 var17))) (= (read var10 var12) var2)) (not (valid var10 var12))) (= (alloc var1 var6) var8)) (= (getnode var11) var0)) (= (|node::n| var0) var5)) (= (write var13 var12 var3) var1)))) (_Glue12 var12 var14 var9 var10 var2))))
(assert (forall ((var0 HeapObject) (var1 node) (var2 Int) (var3 node) (var4 HeapObject) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr)) (or (not (and (_Glue12 var8 var7 var6 var5 var4) (and (and (and (and (= (getnode var4) var3) (= (|node::h| var3) var2)) (= (node var2 var6) var1)) (= (O_node var1) var0)) (valid var5 var8)))) (Inv_Heap var8 var0))))
(assert (forall ((var0 Int) (var1 HeapObject) (var2 node) (var3 Int) (var4 node) (var5 Addr) (var6 node) (var7 Heap) (var8 HeapObject) (var9 Heap) (var10 Addr) (var11 Addr) (var12 HeapObject) (var13 Addr)) (or (not (and (and (Inv_Heap var13 var12) (_Glue12 var13 var11 var10 var9 var8)) (and (and (and (and (and (and (and (and (and (= (read var7 var13) var12) (= (getnode var12) var6)) (= (|node::n| var6) var5)) (valid var7 var13)) (= (getnode var8) var4)) (= (|node::h| var4) var3)) (= (node var3 var10) var2)) (= (O_node var2) var1)) (= (write var9 var13 var1) var7)) (= var0 1)))) (inv_main536_3 var7 var0 var11 var5))))
(assert (forall ((var0 Int) (var1 HeapObject) (var2 node) (var3 Int) (var4 node) (var5 Addr) (var6 node) (var7 HeapObject) (var8 Heap) (var9 HeapObject) (var10 Heap) (var11 Addr) (var12 Addr) (var13 Addr)) (or (not (and (_Glue12 var13 var12 var11 var10 var9) (and (and (and (and (and (and (and (and (and (= (read var8 var13) var7) (= (getnode var7) var6)) (= (|node::n| var6) var5)) (not (valid var8 var13))) (= (getnode var9) var4)) (= (|node::h| var4) var3)) (= (node var3 var11) var2)) (= (O_node var2) var1)) (= (write var10 var13 var1) var8)) (= var0 1)))) (inv_main536_3 var8 var0 var12 var5))))
(check-sat)
