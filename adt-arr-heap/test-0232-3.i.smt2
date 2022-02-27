(set-logic HORN)
(set-info :source |
    Benchmark: C_VC
    Output by Princess (http://www.philipp.ruemmer.org/princess.shtml)
|)
(set-info :status unsat)
(declare-heap Heap Addr HeapObject
 defObj
 ((HeapObject 0) (item 0)) (
  (
   (O_Int (getInt Int))
   (O_Addr (getAddr Addr))
   (O_item (getitem item))
   (defObj)
  )
  (
   (item (next Addr) (data Addr))
  )
))
(declare-fun inv_main10 (Heap Addr Int Addr) Bool)
(declare-fun inv_main12 (Heap Addr Int Addr Addr) Bool)
(declare-fun inv_main15 (Heap Addr) Bool)
(declare-fun inv_main17 (Heap Addr Addr) Bool)
(declare-fun inv_main2 (Heap) Bool)
(declare-fun inv_main21 (Heap Addr) Bool)
(declare-fun inv_main24 (Heap Addr Addr) Bool)
(declare-fun inv_main9 (Heap Addr Int Addr) Bool)
(assert (inv_main2 emptyHeap))
(assert (forall ((var0 Heap) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Int) (var6 Addr) (var7 Heap) (var8 Int) (var9 Addr)) (or (not (and (inv_main12 var0 var9 var8 var4 var2) (and (not (= var6 nullAddr)) (and (= var5 0) (and (and (and (= var7 (write var0 var4 (O_item (item (next (getitem (read var0 var4))) var2)))) (= var3 var9)) (= var1 var8)) (= var6 var4)))))) (inv_main15 var7 var6))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Heap) (var3 Addr) (var4 Addr)) (or (not (and (inv_main21 var1 var4) (and (= var0 nullAddr) (and (and (= var2 var1) (= var3 var4)) (= var0 (next (getitem (read var1 var4)))))))) (inv_main24 var2 var3 var0))))
(assert (forall ((var0 item) (var1 Heap) (var2 Addr) (var3 Heap)) (or (not (and (inv_main2 var1) (and (= var3 var1) (= var2 nullAddr)))) (inv_main9 (newHeap (alloc var3 (O_item var0))) var2 1 (newAddr (alloc var3 (O_item var0)))))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Addr) (var3 Addr) (var4 Int) (var5 Addr) (var6 Addr) (var7 item) (var8 Heap) (var9 Int) (var10 Addr)) (or (not (and (inv_main12 var0 var10 var9 var5 var2) (and (not (= var4 0)) (and (and (and (= var8 (write var0 var5 (O_item (item (next (getitem (read var0 var5))) var2)))) (= var3 var10)) (= var1 var9)) (= var6 var5))))) (inv_main9 (newHeap (alloc var8 (O_item var7))) var6 1 (newAddr (alloc var8 (O_item var7)))))))
(assert (forall ((var0 Heap) (var1 Addr)) (or (not (inv_main15 var0 var1)) (inv_main17 var0 var1 (next (getitem (read var0 var1)))))))
(assert (forall ((var0 Heap) (var1 Heap) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr)) (or (not (and (inv_main17 var0 var8 var7) (and (not (= var4 nullAddr)) (and (and (and (= var2 (write var0 (data (getitem (read var0 var8))) defObj)) (= var3 var8)) (= var5 var7)) (and (and (= var1 (write var2 var3 defObj)) (= var6 var3)) (= var4 var5)))))) (inv_main21 var1 var4))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Heap) (var8 Addr)) (or (not (and (inv_main24 var0 var8 var5) (and (not (= var4 nullAddr)) (and (and (and (= var6 (write var7 var3 defObj)) (= var1 var3)) (= var4 var2)) (and (and (= var7 (write var0 (data (getitem (read var0 var8))) defObj)) (= var3 var8)) (= var2 var5)))))) (inv_main21 var6 var4))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr)) (or (not (and (inv_main21 var0 var7) (and (not (= var1 nullAddr)) (and (and (and (= var4 (write var3 var6 defObj)) (= var2 var6)) (= var1 var5)) (and (not (= var5 nullAddr)) (and (and (= var3 var0) (= var6 var7)) (= var5 (next (getitem (read var0 var7)))))))))) (inv_main21 var4 var1))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Int) (var6 Addr) (var7 Heap) (var8 Int) (var9 Addr)) (or (not (and (inv_main12 var0 var9 var8 var4 var2) (and (not (= var6 nullAddr)) (and (= var6 nullAddr) (and (= var5 0) (and (and (and (= var7 (write var0 var4 (O_item (item (next (getitem (read var0 var4))) var2)))) (= var3 var9)) (= var1 var8)) (= var6 var4))))))) (inv_main21 var7 var6))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Int) (var3 Addr)) (or (not (and (inv_main10 var0 var3 var2 var1) (not (= (next (getitem (read var0 var1))) nullAddr)))) (inv_main12 var0 var3 var2 var1 (data (getitem (read var0 (next (getitem (read var0 var1))))))))))
(assert (forall ((var0 Heap) (var1 item) (var2 Addr) (var3 Int) (var4 Addr)) (or (not (and (inv_main10 var0 var4 var3 var2) (= (next (getitem (read var0 var2))) nullAddr))) (inv_main12 (newHeap (alloc var0 (O_item var1))) var4 var3 var2 (newAddr (alloc var0 (O_item var1)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Int) (var3 Addr)) (or (not (inv_main9 var0 var3 var2 var1)) (inv_main10 (write var0 var1 (O_item (item var3 (data (getitem (read var0 var1)))))) var3 var2 var1))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Int) (var3 Addr)) (not (and (inv_main9 var0 var3 var2 var1) (not (is-O_item (read var0 var1)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Int) (var3 Addr)) (not (and (inv_main10 var0 var3 var2 var1) (not (is-O_item (read var0 var1)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Int) (var3 Addr)) (not (and (inv_main10 var0 var3 var2 var1) (and (not (= (next (getitem (read var0 var1))) nullAddr)) (not (is-O_item (read var0 var1))))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Int) (var3 Addr)) (not (and (inv_main10 var0 var3 var2 var1) (and (not (= (next (getitem (read var0 var1))) nullAddr)) (not (is-O_item (read var0 (next (getitem (read var0 var1)))))))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Int) (var4 Addr)) (not (and (inv_main12 var0 var4 var3 var2 var1) (not (is-O_item (read var0 var2)))))))
(assert (forall ((var0 Heap) (var1 Addr)) (not (and (inv_main15 var0 var1) (not (is-O_item (read var0 var1)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr)) (not (and (inv_main17 var0 var2 var1) (not (is-O_item (read var0 var2)))))))
(assert (forall ((var0 Heap) (var1 Addr)) (not (and (inv_main21 var0 var1) (not (is-O_item (read var0 var1)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr)) (not (and (inv_main24 var0 var2 var1) (not (is-O_item (read var0 var2)))))))
(check-sat)
