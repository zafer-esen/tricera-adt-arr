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
   (O_AddrRange (getAddrRange AddrRange))
   (O_TData (getTData TData))
   (defObj)
  )
  (
   (TData (|TData::lo| Addr) (|TData::hi| Addr))
  )
))
(declare-fun inv_main537_5 (Heap TData Int Addr Addr) Bool)
(declare-fun inv_main538_9 (Heap TData Int Addr Addr Int) Bool)
(declare-fun inv_main547_5 (Heap TData) Bool)
(declare-fun inv_main_3 (Heap TData Int) Bool)
(declare-fun inv_main_4 (Heap TData Int) Bool)
(assert (forall ((var0 TData) (var1 Heap)) (or (not (= var1 emptyHeap)) (inv_main547_5 var1 var0))))
(assert (forall ((var0 TData) (var1 Addr) (var2 Int) (var3 TData) (var4 Int) (var5 Heap) (var6 Addr) (var7 Int) (var8 Int) (var9 TData) (var10 TData) (var11 Int) (var12 Heap) (var13 Heap) (var14 TData) (var15 Heap)) (or (not (and (inv_main547_5 var15 var14) (and (and (and (and (and (and (= var13 (newHeap (alloc var12 (O_Int var11)))) (= var10 var9)) (= var8 var7)) (= var6 (newAddr (alloc var12 (O_Int var11))))) (and (and (and (= var5 (newHeap (alloc var15 (O_Int var4)))) (= var3 var14)) (= var2 1)) (= var1 (newAddr (alloc var15 (O_Int var4)))))) (and (and (= var12 var5) (= var9 (TData var1 (|TData::hi| var3)))) (= var7 var2))) (= var0 (TData (|TData::lo| var10) var6))))) (inv_main_3 var13 var0 var8))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 TData) (var5 Heap)) (or (not (and (inv_main537_5 var5 var4 var3 var2 var1) (and (is-O_Int (read var5 var2)) (= var0 (getInt (read var5 var2)))))) (inv_main538_9 var5 var4 var3 var2 var1 var0))))
(assert (forall ((var0 Heap) (var1 Int) (var2 TData) (var3 Heap)) (or (not (and (inv_main_3 var3 var2 var1) (and (and (is-O_Int (read var3 (|TData::lo| var2))) (is-O_Int (read var3 (|TData::lo| var2)))) (= var0 (write var3 (|TData::lo| var2) (O_Int 4)))))) (inv_main_4 var0 var2 var1))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Int) (var4 TData) (var5 TData) (var6 Heap) (var7 Heap) (var8 Int) (var9 TData) (var10 Heap)) (or (not (and (inv_main_4 var10 var9 var8) (and (and (and (and (and (= var7 var6) (= var5 var4)) (= var3 1)) (= var2 (|TData::lo| var4))) (and (and (is-O_Int (read var10 (|TData::hi| var9))) (is-O_Int (read var10 (|TData::hi| var9)))) (and (and (= var6 (write var10 (|TData::hi| var9) (O_Int 8))) (= var4 var9)) (= var1 var8)))) (= var0 (|TData::hi| var5))))) (inv_main537_5 var7 var5 var3 var2 var0))))
(assert (forall ((var0 Int) (var1 TData) (var2 Heap)) (not (and (inv_main_3 var2 var1 var0) (not (is-O_Int (read var2 (|TData::lo| var1))))))))
(assert (forall ((var0 Int) (var1 TData) (var2 Heap)) (not (and (inv_main_3 var2 var1 var0) (and (is-O_Int (read var2 (|TData::lo| var1))) (not (is-O_Int (read var2 (|TData::lo| var1)))))))))
(assert (forall ((var0 Int) (var1 TData) (var2 Heap)) (not (and (inv_main_4 var2 var1 var0) (not (is-O_Int (read var2 (|TData::hi| var1))))))))
(assert (forall ((var0 Int) (var1 TData) (var2 Heap)) (not (and (inv_main_4 var2 var1 var0) (and (is-O_Int (read var2 (|TData::hi| var1))) (not (is-O_Int (read var2 (|TData::hi| var1)))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 TData) (var4 Heap)) (not (and (inv_main537_5 var4 var3 var2 var1 var0) (not (is-O_Int (read var4 var1)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 TData) (var5 Heap)) (not (and (inv_main538_9 var5 var4 var3 var2 var1 var0) (not (is-O_Int (read var5 var1)))))))
(check-sat)
