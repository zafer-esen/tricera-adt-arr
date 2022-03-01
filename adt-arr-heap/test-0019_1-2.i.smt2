(set-logic HORN)
(set-info :source |
    Benchmark: C_VC
    Output by Princess (http://www.philipp.ruemmer.org/princess.shtml)
|)
(set-info :status sat)
(declare-heap Heap Addr HeapObject
 defObj
 ((HeapObject 0) (TData 0)) (
  (
   (O_Int (getInt Int))
   (O_UInt (getUInt Int))
   (O_Addr (getAddr Addr))
   (O_TData (getTData TData))
   (defObj)
  )
  (
   (TData (lo Addr) (hi Addr))
  )
))
(declare-fun inv_main10 (Heap TData Int) Bool)
(declare-fun inv_main12 (Heap TData Int) Bool)
(declare-fun inv_main18 (Heap TData TData Addr Addr) Bool)
(declare-fun inv_main22 (Heap TData TData Addr Addr Int) Bool)
(declare-fun inv_main3 (Heap TData) Bool)
(assert (forall ((var0 TData) (var1 Heap)) (or (not (= var1 emptyHeap)) (inv_main3 var1 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 TData) (var3 Int) (var4 Heap) (var5 Addr) (var6 Int) (var7 Int) (var8 TData) (var9 TData) (var10 Int) (var11 Heap) (var12 Heap) (var13 TData) (var14 Heap)) (or (not (and (inv_main3 var14 var13) (and (and (and (and (and (= var12 (newHeap (alloc var11 (O_Int var10)))) (= var9 var8)) (= var7 var6)) (= var5 (newAddr (alloc var11 (O_Int var10))))) (and (and (and (= var4 (newHeap (alloc var14 (O_Int var3)))) (= var2 var13)) (= var1 1)) (= var0 (newAddr (alloc var14 (O_Int var3)))))) (and (and (= var11 var4) (= var8 (TData var0 (hi var2)))) (= var6 var1))))) (inv_main10 var12 (TData (lo var9) var5) var7))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 TData) (var3 TData) (var4 Heap)) (or (not (and (inv_main18 var4 var3 var2 var1 var0) (is-O_Int (read var4 var1)))) (inv_main22 var4 var3 var2 var1 var0 (getInt (read var4 var1))))))
(assert (forall ((var0 Int) (var1 TData) (var2 Heap)) (or (not (and (inv_main10 var2 var1 var0) (is-O_Int (read var2 (lo var1))))) (inv_main12 (write var2 (lo var1) (O_Int 4)) var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 TData) (var3 TData) (var4 TData) (var5 Heap) (var6 Heap) (var7 Int) (var8 TData) (var9 Heap)) (or (not (and (inv_main12 var9 var8 var7) (and (and (and (and (= var6 var5) (= var4 var3)) (= var2 var3)) (= var1 (lo var3))) (and (is-O_Int (read var9 (hi var8))) (and (and (= var5 (write var9 (hi var8) (O_Int 8))) (= var3 var8)) (= var0 var7)))))) (inv_main18 var6 var4 var2 var1 (hi var2)))))
(assert (forall ((var0 Int) (var1 TData) (var2 Heap)) (not (and (inv_main10 var2 var1 var0) (not (is-O_Int (read var2 (lo var1))))))))
(assert (forall ((var0 Int) (var1 TData) (var2 Heap)) (not (and (inv_main12 var2 var1 var0) (not (is-O_Int (read var2 (hi var1))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 TData) (var3 TData) (var4 Heap)) (not (and (inv_main18 var4 var3 var2 var1 var0) (not (is-O_Int (read var4 var1)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 TData) (var4 TData) (var5 Heap)) (not (and (inv_main22 var5 var4 var3 var2 var1 var0) (not (is-O_Int (read var5 var1)))))))
(check-sat)
