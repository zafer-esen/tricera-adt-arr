(set-logic HORN)
(set-info :source |
    Benchmark: 
    Output by Princess (http://www.philipp.ruemmer.org/princess.shtml)
|)
(declare-heap Heap Addr HeapObject
 defObj
 ((HeapObject 0) (process_node 0)) (
  (
   (O_Int (getInt Int))
   (O_UInt (getUInt Int))
   (O_Addr (getAddr Addr))
   (O_AddrRange (getAddrRange AddrRange))
   (O_process_node (getprocess_node process_node))
   (defObj)
  )
  (
   (process_node (|process_node::process_id| Int) (|process_node::time_to_wait| Int) (|process_node::next| Addr))
  )
))
(declare-fun _Glue7 (Heap Int Addr Addr HeapObject) Bool)
(declare-fun inv_main604_5 (Heap Addr Int) Bool)
(declare-fun _Glue3 (Int Addr Int Addr Heap HeapObject) Bool)
(declare-fun inv_main598_73 (Heap Addr Int Addr) Bool)
(declare-fun _Glue9 (Heap Addr Addr Int Addr Int Int HeapObject) Bool)
(declare-fun _Glue0 (Int Addr Addr Heap HeapObject) Bool)
(declare-fun _Glue8 (Addr Addr Addr Int Addr Addr Heap HeapObject) Bool)
(declare-fun _Glue5 (Heap Int Addr Addr HeapObject) Bool)
(declare-fun inv_main581_5 (Heap Addr Int Addr Addr) Bool)
(declare-fun Inv_Heap_exp_exp (Addr Int Int Addr) Bool)
(assert (forall ((var0 Int) (var1 Heap) (var2 Addr)) (or (not (and (and (= nullAddr var2) (= emptyHeap var1)) (= var0 1))) (inv_main604_5 var1 var2 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Heap)) (or (not (and (inv_main604_5 var3 var2 var1) (and (and (<= 0 (+ (+ 1000 (* (- 1) var1)) (- 1))) (not (<= 0 (+ (+ (- 1) var1) (- 1))))) (= var0 var2)))) (inv_main598_73 var3 var0 var1 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Heap)) (or (not (and (inv_main604_5 var4 var3 var2) (and (and (and (not (<= 0 (+ (+ 1000 (* (- 1) var2)) (- 1)))) (<= 0 (+ (+ (- 1) var2) (- 1)))) (= nullAddr var1)) (= var0 var3)))) (inv_main581_5 var4 var0 var2 var3 var1))))
(assert (forall ((var0 AllocResHeap) (var1 Addr) (var2 Int) (var3 Int) (var4 HeapObject) (var5 process_node) (var6 Int) (var7 Addr) (var8 Heap)) (or (not (and (inv_main604_5 var8 var7 (+ var6 (- 1))) (and (and (and (= (O_process_node var5) var4) (= (process_node var3 var2 var1) var5)) (<= 0 (+ (+ 1000 (* (- 1) (+ var6 (- 1)))) (- 1)))) (= (alloc var8 var4) var0)))) (Inv_Heap_exp_exp (newAddr var0) var3 var2 var1))))
(assert (forall ((var0 Int) (var1 AllocResHeap) (var2 Heap) (var3 HeapObject) (var4 process_node) (var5 HeapObject) (var6 process_node) (var7 Int) (var8 Addr) (var9 Heap) (var10 Addr) (var11 Int) (var12 Int) (var13 Addr)) (or (not (and (and (Inv_Heap_exp_exp var13 var12 var11 var10) (inv_main604_5 var9 var8 (+ var7 (- 1)))) (and (and (and (and (and (and (and (= (O_process_node var6) var5) (= (O_process_node var4) var3)) (= (AllocResHeap var2 var13) var1)) (= (process_node var12 var11 var10) var6)) (= (read var2 var13) var5)) (valid var2 var13)) (<= 0 (+ (+ 1000 (* (- 1) (+ var7 (- 1)))) (- 1)))) (= (alloc var9 var3) var1)))) (_Glue3 var7 var8 var0 var13 var2 var5))))
(assert (forall ((var0 Int) (var1 AllocResHeap) (var2 HeapObject) (var3 process_node) (var4 HeapObject) (var5 Addr) (var6 Heap) (var7 Int) (var8 Addr) (var9 Heap)) (or (not (and (inv_main604_5 var9 var8 (+ var7 (- 1))) (and (and (and (and (and (= (read var6 var5) var4) (not (valid var6 var5))) (= (O_process_node var3) var2)) (= (AllocResHeap var6 var5) var1)) (<= 0 (+ (+ 1000 (* (- 1) (+ var7 (- 1)))) (- 1)))) (= (alloc var9 var2) var1)))) (_Glue3 var7 var8 var0 var5 var6 var4))))
(assert (forall ((var0 Addr) (var1 Int) (var2 process_node) (var3 HeapObject) (var4 Heap) (var5 Addr) (var6 Int) (var7 Addr) (var8 Int)) (or (not (and (_Glue3 var8 var7 var6 var5 var4 var3) (and (and (and (= (getprocess_node var3) var2) (= (|process_node::time_to_wait| var2) var1)) (= (|process_node::next| var2) var0)) (valid var4 var5)))) (Inv_Heap_exp_exp var5 var6 var1 var0))))
(assert (forall ((var0 process_node) (var1 Heap) (var2 HeapObject) (var3 process_node) (var4 Addr) (var5 Int) (var6 HeapObject) (var7 process_node) (var8 HeapObject) (var9 Heap) (var10 Int) (var11 Addr) (var12 Int) (var13 Addr) (var14 Int) (var15 Int) (var16 Addr)) (or (not (and (and (Inv_Heap_exp_exp var16 var15 var14 var13) (_Glue3 var12 var11 var10 var16 var9 var8)) (and (and (and (and (and (and (and (and (and (= (O_process_node var7) var6) (= (process_node var10 var5 var4) var3)) (= (O_process_node var3) var2)) (= (process_node var15 var14 var13) var7)) (= (read var1 var16) var6)) (valid var1 var16)) (= (getprocess_node var8) var0)) (= (|process_node::time_to_wait| var0) var5)) (= (|process_node::next| var0) var4)) (= (write var9 var16 var2) var1)))) (_Glue5 var1 var12 var11 var16 var6))))
(assert (forall ((var0 HeapObject) (var1 process_node) (var2 Addr) (var3 Int) (var4 process_node) (var5 HeapObject) (var6 Heap) (var7 HeapObject) (var8 Heap) (var9 Addr) (var10 Int) (var11 Addr) (var12 Int)) (or (not (and (_Glue3 var12 var11 var10 var9 var8 var7) (and (and (and (and (and (and (and (= (read var6 var9) var5) (not (valid var6 var9))) (= (getprocess_node var7) var4)) (= (|process_node::time_to_wait| var4) var3)) (= (|process_node::next| var4) var2)) (= (process_node var10 var3 var2) var1)) (= (O_process_node var1) var0)) (= (write var8 var9 var0) var6)))) (_Glue5 var6 var12 var11 var9 var5))))
(assert (forall ((var0 Addr) (var1 Int) (var2 process_node) (var3 HeapObject) (var4 Addr) (var5 Addr) (var6 Int) (var7 Heap)) (or (not (and (_Glue5 var7 (+ var6 1) var5 var4 var3) (and (and (and (= (getprocess_node var3) var2) (= (|process_node::process_id| var2) var1)) (= (|process_node::next| var2) var0)) (valid var7 var4)))) (Inv_Heap_exp_exp var4 var1 var6 var0))))
(assert (forall ((var0 process_node) (var1 Heap) (var2 HeapObject) (var3 process_node) (var4 Addr) (var5 Int) (var6 HeapObject) (var7 process_node) (var8 HeapObject) (var9 Addr) (var10 Int) (var11 Heap) (var12 Addr) (var13 Int) (var14 Int) (var15 Addr)) (or (not (and (and (Inv_Heap_exp_exp var15 var14 var13 var12) (_Glue5 var11 var10 var9 var15 var8)) (and (and (and (and (and (and (and (and (and (= (O_process_node var7) var6) (= (process_node var5 (+ var10 (- 1)) var4) var3)) (= (O_process_node var3) var2)) (= (process_node var14 var13 var12) var7)) (= (read var1 var15) var6)) (valid var1 var15)) (= (getprocess_node var8) var0)) (= (|process_node::process_id| var0) var5)) (= (|process_node::next| var0) var4)) (= (write var11 var15 var2) var1)))) (_Glue7 var1 var10 var9 var15 var6))))
(assert (forall ((var0 HeapObject) (var1 process_node) (var2 Addr) (var3 Int) (var4 process_node) (var5 HeapObject) (var6 Heap) (var7 HeapObject) (var8 Addr) (var9 Addr) (var10 Int) (var11 Heap)) (or (not (and (_Glue5 var11 var10 var9 var8 var7) (and (and (and (and (and (and (and (= (read var6 var8) var5) (not (valid var6 var8))) (= (getprocess_node var7) var4)) (= (|process_node::process_id| var4) var3)) (= (|process_node::next| var4) var2)) (= (process_node var3 (+ var10 (- 1)) var2) var1)) (= (O_process_node var1) var0)) (= (write var11 var8 var0) var6)))) (_Glue7 var6 var10 var9 var8 var5))))
(assert (forall ((var0 Int) (var1 Int) (var2 process_node) (var3 HeapObject) (var4 Addr) (var5 Addr) (var6 Int) (var7 Heap)) (or (not (and (_Glue7 var7 var6 var5 var4 var3) (and (and (and (= (getprocess_node var3) var2) (= (|process_node::process_id| var2) var1)) (= (|process_node::time_to_wait| var2) var0)) (valid var7 var4)))) (Inv_Heap_exp_exp var4 var1 var0 var5))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 HeapObject) (var3 process_node) (var4 Int) (var5 Int) (var6 process_node) (var7 HeapObject) (var8 Addr) (var9 Addr) (var10 Int) (var11 Heap)) (or (not (and (_Glue7 var11 var10 var9 var8 var7) (and (and (and (and (and (and (= (getprocess_node var7) var6) (= (|process_node::process_id| var6) var5)) (= (|process_node::time_to_wait| var6) var4)) (= (process_node var5 var4 var9) var3)) (= (O_process_node var3) var2)) (= (write var11 var8 var2) var1)) (= var0 var8)))) (inv_main598_73 var1 var8 var10 var0))))
(assert (forall ((var0 Addr) (var1 HeapObject) (var2 process_node) (var3 Addr) (var4 Int) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Int) (var9 Addr)) (or (not (and (and (Inv_Heap_exp_exp var9 var8 1 var7) (inv_main581_5 var6 var5 var4 var9 var3)) (and (and (and (and (and (and (= (O_process_node var2) var1) (= (process_node var8 1 var7) var2)) (= nullAddr var3)) (= (read var6 var9) var1)) (not (= var9 var3))) (valid var6 var9)) (= var0 var7)))) (inv_main581_5 var6 var0 var4 var7 var9))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 process_node) (var3 HeapObject) (var4 Addr) (var5 Addr) (var6 Int) (var7 Addr) (var8 Heap)) (or (not (and (inv_main581_5 var8 var7 var6 var5 var4) (and (and (and (and (and (and (and (= nullAddr var4) (= (read var8 var5) var3)) (= (getprocess_node var3) var2)) (= (|process_node::time_to_wait| var2) 1)) (= (|process_node::next| var2) var1)) (not (= var5 var4))) (not (valid var8 var5))) (= var0 var1)))) (inv_main581_5 var8 var0 var6 var1 var5))))
(assert (forall ((var0 Addr) (var1 HeapObject) (var2 process_node) (var3 Int) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Int) (var8 Int) (var9 Addr)) (or (not (and (and (Inv_Heap_exp_exp var9 var8 var7 var6) (inv_main598_73 var5 var4 var3 var9)) (and (and (and (and (and (and (= (O_process_node var2) var1) (= (process_node var8 var7 var6) var2)) (= nullAddr var0)) (= (read var5 var9) var1)) (not (= var9 var0))) (<= 0 (+ var7 (- 1)))) (valid var5 var9)))) (inv_main598_73 var5 var4 var3 var6))))
(assert (forall ((var0 Addr) (var1 Int) (var2 process_node) (var3 HeapObject) (var4 Addr) (var5 Addr) (var6 Int) (var7 Addr) (var8 Heap)) (or (not (and (inv_main598_73 var8 var7 var6 var5) (and (and (and (and (and (and (and (= nullAddr var4) (= (read var8 var5) var3)) (= (getprocess_node var3) var2)) (= (|process_node::time_to_wait| var2) var1)) (= (|process_node::next| var2) var0)) (not (= var5 var4))) (<= 0 (+ var1 (- 1)))) (not (valid var8 var5))))) (inv_main598_73 var8 var7 var6 var0))))
(assert (forall ((var0 Addr) (var1 HeapObject) (var2 process_node) (var3 Addr) (var4 Int) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Int) (var9 Int) (var10 Addr)) (or (not (and (and (Inv_Heap_exp_exp var10 var9 var8 var7) (inv_main581_5 var6 var5 var4 var10 var3)) (and (and (and (and (and (= (O_process_node var2) var1) (= (process_node var9 var8 var7) var2)) (= nullAddr var0)) (not (= var10 var0))) (= (read var6 var10) var1)) (valid var6 var10)))) (_Glue0 var4 var5 var10 var6 var1))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Addr) (var6 Heap)) (or (not (and (inv_main581_5 var6 var5 var4 var3 var2) (and (and (and (= nullAddr var1) (not (= var3 var1))) (= (read var6 var3) var0)) (not (valid var6 var3))))) (_Glue0 var4 var5 var3 var6 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 process_node) (var4 HeapObject) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Int)) (or (not (and (_Glue0 var8 var7 var6 var5 var4) (and (and (and (and (and (= (getprocess_node var4) var3) (= (|process_node::process_id| var3) var2)) (= (|process_node::next| var3) var1)) (= (|process_node::time_to_wait| var3) (+ var0 1))) (not (= (+ var0 1) 1))) (valid var5 var6)))) (Inv_Heap_exp_exp var6 var2 var0 var1))))
(assert (forall ((var0 process_node) (var1 Heap) (var2 HeapObject) (var3 process_node) (var4 Addr) (var5 Int) (var6 Int) (var7 HeapObject) (var8 process_node) (var9 HeapObject) (var10 Heap) (var11 Addr) (var12 Int) (var13 Addr) (var14 Int) (var15 Int) (var16 Addr)) (or (not (and (and (Inv_Heap_exp_exp var16 var15 var14 var13) (_Glue0 var12 var11 var16 var10 var9)) (and (and (and (and (and (and (and (and (and (and (and (= (O_process_node var8) var7) (= (process_node var6 (+ var5 (- 1)) var4) var3)) (= (O_process_node var3) var2)) (= (process_node var15 var14 var13) var8)) (= (read var1 var16) var7)) (valid var1 var16)) (= (getprocess_node var9) var0)) (= (|process_node::process_id| var0) var6)) (= (|process_node::next| var0) var4)) (= (|process_node::time_to_wait| var0) var5)) (not (= var5 1))) (= (write var10 var16 var2) var1)))) (inv_main581_5 var1 var11 var12 var13 var16))))
(assert (forall ((var0 HeapObject) (var1 process_node) (var2 Int) (var3 Addr) (var4 Int) (var5 process_node) (var6 Addr) (var7 process_node) (var8 HeapObject) (var9 Heap) (var10 HeapObject) (var11 Heap) (var12 Addr) (var13 Addr) (var14 Int)) (or (not (and (_Glue0 var14 var13 var12 var11 var10) (and (and (and (and (and (and (and (and (and (and (and (= (read var9 var12) var8) (= (getprocess_node var8) var7)) (= (|process_node::next| var7) var6)) (not (valid var9 var12))) (= (getprocess_node var10) var5)) (= (|process_node::process_id| var5) var4)) (= (|process_node::next| var5) var3)) (= (|process_node::time_to_wait| var5) var2)) (not (= var2 1))) (= (process_node var4 (+ var2 (- 1)) var3) var1)) (= (O_process_node var1) var0)) (= (write var11 var12 var0) var9)))) (inv_main581_5 var9 var13 var14 var6 var12))))
(assert (forall ((var0 Addr) (var1 HeapObject) (var2 process_node) (var3 Int) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Int) (var8 Int) (var9 Addr)) (not (and (and (Inv_Heap_exp_exp var9 var8 var7 var6) (inv_main598_73 var5 var4 var3 var9)) (and (and (and (and (and (and (= (O_process_node var2) var1) (= (process_node var8 var7 var6) var2)) (not (= var9 var0))) (not (<= 0 (+ var7 (- 1))))) (= nullAddr var0)) (= (read var5 var9) var1)) (valid var5 var9))))))
(assert (forall ((var0 process_node) (var1 HeapObject) (var2 Int) (var3 Addr) (var4 Addr) (var5 Int) (var6 Addr) (var7 Heap)) (not (and (inv_main598_73 var7 var6 var5 var4) (and (and (and (and (and (and (not (= var4 var3)) (not (<= 0 (+ var2 (- 1))))) (= nullAddr var3)) (= (read var7 var4) var1)) (= (getprocess_node var1) var0)) (= (|process_node::time_to_wait| var0) var2)) (not (valid var7 var4)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Heap)) (or (not (and (inv_main598_73 var3 var2 var1 var0) (= nullAddr var0))) (inv_main604_5 var3 var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Heap)) (or (not (and (inv_main604_5 var4 var3 var2) (and (and (and (<= 0 (+ (+ 1000 (* (- 1) var2)) (- 1))) (<= 0 (+ (+ (- 1) var2) (- 1)))) (= nullAddr var1)) (= var0 var3)))) (inv_main581_5 var4 var0 var2 var3 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 HeapObject) (var3 process_node) (var4 Addr) (var5 Int) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Int) (var10 Int) (var11 Addr)) (or (not (and (and (Inv_Heap_exp_exp var11 var10 var9 var8) (inv_main581_5 var7 var6 var5 var4 var11)) (and (and (and (and (and (= (O_process_node var3) var2) (= (process_node var10 var9 var8) var3)) (= nullAddr var1)) (not (= var11 var1))) (= (read var7 var11) var2)) (valid var7 var11)))) (_Glue8 var0 var1 var6 var5 var4 var11 var7 var2))))
(assert (forall ((var0 Addr) (var1 HeapObject) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Int) (var6 Addr) (var7 Heap)) (or (not (and (inv_main581_5 var7 var6 var5 var4 var3) (and (and (and (= nullAddr var2) (not (= var3 var2))) (= (read var7 var3) var1)) (not (valid var7 var3))))) (_Glue8 var0 var2 var6 var5 var4 var3 var7 var1))))
(assert (forall ((var0 Int) (var1 Int) (var2 process_node) (var3 HeapObject) (var4 process_node) (var5 HeapObject) (var6 Heap) (var7 Addr) (var8 Int) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Int) (var13 Int) (var14 Addr)) (or (not (and (and (Inv_Heap_exp_exp var14 var13 var12 var11) (_Glue8 var14 var10 var9 var8 var14 var7 var6 var5)) (and (and (and (and (and (and (and (= (O_process_node var4) var3) (= (process_node var13 var12 var11) var4)) (= (getprocess_node var5) var2)) (= (|process_node::process_id| var2) var1)) (= (|process_node::time_to_wait| var2) var0)) (not (= var14 var10))) (= (read var6 var14) var3)) (valid var6 var14)))) (_Glue9 var6 var7 var14 var8 var9 var1 var0 var3))))
(assert (forall ((var0 HeapObject) (var1 Int) (var2 Int) (var3 process_node) (var4 HeapObject) (var5 Heap) (var6 Addr) (var7 Int) (var8 Addr) (var9 Addr) (var10 Addr)) (or (not (and (_Glue8 var10 var9 var8 var7 var10 var6 var5 var4) (and (and (and (and (and (= (getprocess_node var4) var3) (= (|process_node::process_id| var3) var2)) (= (|process_node::time_to_wait| var3) var1)) (not (= var10 var9))) (= (read var5 var10) var0)) (not (valid var5 var10))))) (_Glue9 var5 var6 var10 var7 var8 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 process_node) (var2 HeapObject) (var3 Int) (var4 Int) (var5 Addr) (var6 Int) (var7 Addr) (var8 Addr) (var9 Heap)) (or (not (and (_Glue9 var9 var8 var7 var6 var5 var4 var3 var2) (and (and (and (= (getprocess_node var2) var1) (= (|process_node::time_to_wait| var1) 1)) (= (|process_node::next| var1) var0)) (valid var9 var8)))) (Inv_Heap_exp_exp var8 var4 var3 var0))))
(assert (forall ((var0 process_node) (var1 Heap) (var2 HeapObject) (var3 process_node) (var4 Addr) (var5 HeapObject) (var6 process_node) (var7 HeapObject) (var8 Int) (var9 Int) (var10 Addr) (var11 Int) (var12 Addr) (var13 Heap) (var14 Addr) (var15 Int) (var16 Int) (var17 Addr)) (or (not (and (and (Inv_Heap_exp_exp var17 var16 var15 var14) (_Glue9 var13 var12 var17 var11 var10 var9 var8 var7)) (and (and (and (and (and (and (and (and (and (= (O_process_node var6) var5) (= (process_node var9 var8 var4) var3)) (= (O_process_node var3) var2)) (= (process_node var16 var15 var14) var6)) (= (read var1 var17) var5)) (valid var1 var17)) (= (getprocess_node var7) var0)) (= (|process_node::time_to_wait| var0) 1)) (= (|process_node::next| var0) var4)) (= (write var13 var12 var2) var1)))) (inv_main581_5 var1 var10 var11 var14 var17))))
(assert (forall ((var0 HeapObject) (var1 process_node) (var2 Addr) (var3 process_node) (var4 Addr) (var5 process_node) (var6 HeapObject) (var7 Heap) (var8 HeapObject) (var9 Int) (var10 Int) (var11 Addr) (var12 Int) (var13 Addr) (var14 Addr) (var15 Heap)) (or (not (and (_Glue9 var15 var14 var13 var12 var11 var10 var9 var8) (and (and (and (and (and (and (and (and (and (= (read var7 var13) var6) (= (getprocess_node var6) var5)) (= (|process_node::next| var5) var4)) (not (valid var7 var13))) (= (getprocess_node var8) var3)) (= (|process_node::time_to_wait| var3) 1)) (= (|process_node::next| var3) var2)) (= (process_node var10 var9 var2) var1)) (= (O_process_node var1) var0)) (= (write var15 var14 var0) var7)))) (inv_main581_5 var7 var11 var12 var4 var13))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Heap)) (or (not (and (inv_main604_5 var3 var2 var1) (and (and (not (<= 0 (+ (+ 1000 (* (- 1) var1)) (- 1)))) (not (<= 0 (+ (+ (- 1) var1) (- 1))))) (= var0 var2)))) (inv_main598_73 var3 var0 var1 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Addr) (var5 Heap)) (or (not (and (inv_main581_5 var5 var4 (+ var3 1) var2 var1) (and (= nullAddr var2) (= var0 var4)))) (inv_main598_73 var5 var0 var3 var4))))
(assert (forall ((var0 Addr) (var1 HeapObject) (var2 process_node) (var3 Int) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Int) (var8 Int) (var9 Addr)) (or (not (and (and (Inv_Heap_exp_exp var9 var8 var7 var6) (inv_main598_73 var5 var4 var3 var9)) (and (and (and (and (and (and (= (O_process_node var2) var1) (= (process_node var8 var7 var6) var2)) (= (read var5 var9) var1)) (= nullAddr var0)) (not (= var9 var0))) (not (<= 0 (+ var7 (- 1))))) (valid var5 var9)))) (inv_main598_73 var5 var4 var3 var6))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 process_node) (var4 HeapObject) (var5 Addr) (var6 Int) (var7 Addr) (var8 Heap)) (or (not (and (inv_main598_73 var8 var7 var6 var5) (and (and (and (and (and (and (and (= (read var8 var5) var4) (= (getprocess_node var4) var3)) (= (|process_node::next| var3) var2)) (= nullAddr var1)) (= (|process_node::time_to_wait| var3) var0)) (not (= var5 var1))) (not (<= 0 (+ var0 (- 1))))) (not (valid var8 var5))))) (inv_main598_73 var8 var7 var6 var2))))
(check-sat)
