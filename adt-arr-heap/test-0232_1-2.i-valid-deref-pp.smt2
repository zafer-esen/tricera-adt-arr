(set-logic HORN)
(set-info :source |
    Benchmark: 
    Output by Princess (http://www.philipp.ruemmer.org/princess.shtml)
|)
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
(declare-fun _Glue8_exp_exp (Heap Addr Addr Addr Int Int Addr HeapObject) Bool)
(declare-fun _Glue0 (Addr Heap Addr HeapObject) Bool)
(declare-fun Inv_Heap (Addr HeapObject) Bool)
(declare-fun _Glue13 (Int Heap Addr HeapObject) Bool)
(declare-fun _Glue15 (Addr Int Int Addr Heap Addr HeapObject) Bool)
(declare-fun _Glue20 (Addr Addr Addr Heap HeapObject) Bool)
(declare-fun inv_main_13 (Heap Addr Int) Bool)
(declare-fun inv_main532_5 (Heap Int Addr Int Addr) Bool)
(declare-fun inv_main547_9 (Heap Addr Int) Bool)
(declare-fun _Glue12 (Int Heap Addr Addr HeapObject) Bool)
(declare-fun _Glue22 (Heap Addr HeapObject) Bool)
(declare-fun _Glue17 (Heap Addr Int Int Addr HeapObject) Bool)
(declare-fun inv_main534_18 (Heap Int Int Addr Addr) Bool)
(declare-fun _Glue2_exp_exp (Int Addr Addr Int Int Addr Heap Addr HeapObject) Bool)
(declare-fun _Glue19 (Int Int Addr Heap Addr HeapObject) Bool)
(declare-fun _Glue18 (Int Int Heap Addr Addr HeapObject) Bool)
(declare-fun _Glue10 (Addr Addr Addr Heap HeapObject) Bool)
(declare-fun _Glue6_exp_exp (Addr Addr Addr Int Int Addr Heap Addr HeapObject) Bool)
(declare-fun _Glue9 (Int Addr Addr Heap HeapObject) Bool)
(declare-fun _Glue5 (Int Heap Addr HeapObject) Bool)
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Heap) (var4 HeapObject) (var5 Addr)) (or (not (and (and (Inv_Heap var5 var4) (inv_main534_18 var3 var2 (+ var1 (- 1)) var5 var0)) (and (= (read var3 var5) var4) (valid var3 var5)))) (_Glue18 var2 var1 var3 var5 var0 var4))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Heap)) (or (not (and (inv_main534_18 var5 var4 (+ var3 (- 1)) var2 var1) (and (= (read var5 var2) var0) (not (valid var5 var2))))) (_Glue18 var4 var3 var5 var2 var1 var0))))
(assert (forall ((var0 HeapObject) (var1 item) (var2 Addr) (var3 item) (var4 HeapObject) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Int) (var9 Int)) (or (not (and (_Glue18 var9 var8 var7 var6 var5 var4) (and (and (and (and (and (and (and (and (is-O_item var4) (= (getitem var4) var3)) (= (|item::next| var3) var2)) (= (item var2 var5) var1)) (= (O_item var1) var0)) (<= 0 (+ var8 (- 1)))) (not (<= 0 (+ var8 (- 1))))) (not (<= 0 (+ (+ 20 (* (- 1) var9)) (- 1))))) (valid var7 var6)))) (Inv_Heap var6 var0))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 item) (var3 Addr) (var4 item) (var5 HeapObject) (var6 Addr) (var7 Addr) (var8 Heap) (var9 Int) (var10 Int)) (or (not (and (_Glue18 var10 var9 var8 var7 var6 var5) (and (and (and (and (and (and (and (and (is-O_item var5) (= (getitem var5) var4)) (= (|item::next| var4) var3)) (= (item var3 var6) var2)) (= (O_item var2) var1)) (= (write var8 var7 var1) var0)) (<= 0 (+ var9 (- 1)))) (not (<= 0 (+ var9 (- 1))))) (not (<= 0 (+ (+ 20 (* (- 1) var10)) (- 1))))))) (inv_main_13 var0 var7 var9))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Heap) (var4 HeapObject) (var5 Addr)) (or (not (and (and (Inv_Heap var5 var4) (inv_main534_18 var3 var2 (+ var1 (- 1)) var5 var0)) (and (= (read var3 var5) var4) (valid var3 var5)))) (_Glue12 var1 var3 var0 var5 var4))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Heap)) (or (not (and (inv_main534_18 var5 var4 (+ var3 (- 1)) var2 var1) (and (= (read var5 var2) var0) (not (valid var5 var2))))) (_Glue12 var3 var5 var1 var2 var0))))
(assert (forall ((var0 HeapObject) (var1 item) (var2 Addr) (var3 item) (var4 HeapObject) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Int)) (or (not (and (_Glue12 var8 var7 var6 var5 var4) (and (and (and (and (and (and (and (is-O_item var4) (= (getitem var4) var3)) (= (|item::next| var3) var2)) (= (item var2 var6) var1)) (= (O_item var1) var0)) (<= 0 (+ (+ 1 (+ var8 (- 1))) (- 1)))) (not (<= 0 (+ (+ 1 (+ var8 (- 1))) (- 1))))) (valid var7 var5)))) (Inv_Heap var5 var0))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 item) (var3 Addr) (var4 item) (var5 HeapObject) (var6 Addr) (var7 Addr) (var8 Heap) (var9 Int)) (or (not (and (_Glue12 var9 var8 var7 var6 var5) (and (and (and (and (and (and (and (is-O_item var5) (= (getitem var5) var4)) (= (|item::next| var4) var3)) (= (item var3 var7) var2)) (= (O_item var2) var1)) (= (write var8 var6 var1) var0)) (<= 0 (+ (+ 1 (+ var9 (- 1))) (- 1)))) (not (<= 0 (+ (+ 1 (+ var9 (- 1))) (- 1))))))) (inv_main_13 var0 var6 var9))))
(assert (forall ((var0 Int) (var1 Heap) (var2 HeapObject) (var3 Addr)) (not (and (and (Inv_Heap var3 var2) (inv_main547_9 var1 var3 var0)) (and (and (and (= (read var1 var3) var2) (is-O_item var2)) (not (= 4 4))) (valid var1 var3))))))
(assert (forall ((var0 HeapObject) (var1 Int) (var2 Addr) (var3 Heap)) (not (and (inv_main547_9 var3 var2 var1) (and (and (and (= (read var3 var2) var0) (is-O_item var0)) (not (= 4 4))) (not (valid var3 var2)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Heap) (var4 HeapObject) (var5 Addr)) (or (not (and (and (Inv_Heap var5 var4) (inv_main534_18 var3 var2 (+ var1 (- 1)) var5 var0)) (and (= (read var3 var5) var4) (valid var3 var5)))) (_Glue9 var1 var5 var0 var3 var4))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Heap)) (or (not (and (inv_main534_18 var5 var4 (+ var3 (- 1)) var2 var1) (and (= (read var5 var2) var0) (not (valid var5 var2))))) (_Glue9 var3 var2 var1 var5 var0))))
(assert (forall ((var0 HeapObject) (var1 item) (var2 Addr) (var3 item) (var4 HeapObject) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Int)) (or (not (and (_Glue9 var8 var7 var6 var5 var4) (and (and (and (and (and (and (is-O_item var4) (= (getitem var4) var3)) (= (|item::next| var3) var2)) (= (item var2 var6) var1)) (= (O_item var1) var0)) (<= 0 (+ (+ 1 (+ var8 (- 1))) (- 1)))) (valid var5 var7)))) (Inv_Heap var7 var0))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 item) (var3 Addr) (var4 item) (var5 HeapObject) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Int)) (or (not (and (_Glue9 var9 var8 var7 var6 var5) (and (and (and (and (and (and (is-O_item var5) (= (getitem var5) var4)) (= (|item::next| var4) var3)) (= (item var3 var7) var2)) (= (O_item var2) var1)) (= (write var6 var8 var1) var0)) (<= 0 (+ (+ 1 (+ var9 (- 1))) (- 1)))))) (inv_main547_9 var0 var8 var9))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Int) (var4 Heap) (var5 HeapObject) (var6 Addr)) (or (not (and (and (Inv_Heap var6 var5) (inv_main532_5 var4 var3 var2 var1 var6)) (and (and (and (not (= 4 4)) (= nullAddr var0)) (= (read var4 var6) var5)) (valid var4 var6)))) (_Glue10 var0 var2 var6 var4 var5))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Int) (var4 Addr) (var5 Int) (var6 Heap)) (or (not (and (inv_main532_5 var6 var5 var4 var3 var2) (and (and (and (not (= 4 4)) (= nullAddr var1)) (= (read var6 var2) var0)) (not (valid var6 var2))))) (_Glue10 var1 var4 var2 var6 var0))))
(assert (forall ((var0 HeapObject) (var1 item) (var2 Addr) (var3 item) (var4 HeapObject) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr)) (or (not (and (_Glue10 var8 var7 var6 var5 var4) (and (and (and (and (and (is-O_item var4) (= (getitem var4) var3)) (= (|item::data| var3) var2)) (= (item var7 var2) var1)) (= (O_item var1) var0)) (valid var5 var6)))) (Inv_Heap var6 var0))))
(assert (forall ((var0 HeapObject) (var1 item) (var2 Addr) (var3 item) (var4 Addr) (var5 item) (var6 Heap) (var7 HeapObject) (var8 Heap) (var9 Addr) (var10 Addr) (var11 HeapObject) (var12 Addr)) (not (and (and (Inv_Heap var12 var11) (_Glue10 var10 var9 var12 var8 var7)) (and (and (and (and (and (and (and (and (and (and (and (and (= (read var6 var12) var11) (is-O_item var11)) (= (getitem var11) var5)) (= (|item::next| var5) var4)) (not (= var4 var10))) (valid var6 var12)) true) (is-O_item var7)) (= (getitem var7) var3)) (= (|item::data| var3) var2)) (= (item var9 var2) var1)) (= (O_item var1) var0)) (= (write var8 var12 var0) var6))))))
(assert (forall ((var0 HeapObject) (var1 item) (var2 Addr) (var3 item) (var4 Addr) (var5 item) (var6 HeapObject) (var7 Heap) (var8 HeapObject) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Addr)) (not (and (_Glue10 var12 var11 var10 var9 var8) (and (and (and (and (and (and (and (and (and (and (and (= (read var7 var10) var6) (is-O_item var6)) (= (getitem var6) var5)) (= (|item::next| var5) var4)) (not (= var4 var12))) (not (valid var7 var10))) (is-O_item var8)) (= (getitem var8) var3)) (= (|item::data| var3) var2)) (= (item var11 var2) var1)) (= (O_item var1) var0)) (= (write var9 var10 var0) var7))))))
(assert (forall ((var0 Int) (var1 Heap) (var2 HeapObject) (var3 Addr)) (or (not (and (and (Inv_Heap var3 var2) (inv_main_13 var1 var3 (+ var0 1))) (and (= (read var1 var3) var2) (valid var1 var3)))) (_Glue5 var0 var1 var3 var2))))
(assert (forall ((var0 HeapObject) (var1 Int) (var2 Addr) (var3 Heap)) (or (not (and (inv_main_13 var3 var2 (+ var1 1)) (and (= (read var3 var2) var0) (not (valid var3 var2))))) (_Glue5 var1 var3 var2 var0))))
(assert (forall ((var0 HeapObject) (var1 HeapObject) (var2 Addr) (var3 Heap) (var4 Int)) (or (not (and (_Glue5 var4 var3 var2 var1) (and (and (and (is-O_item var1) (<= 0 (+ (+ (- 1) (+ var4 1)) (- 1)))) (= defObj var0)) (valid var3 var2)))) (Inv_Heap var2 var0))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 Addr) (var3 item) (var4 HeapObject) (var5 Addr) (var6 Heap) (var7 Int)) (or (not (and (_Glue5 var7 var6 var5 var4) (and (and (and (and (and (is-O_item var4) (= (getitem var4) var3)) (= (|item::next| var3) var2)) (<= 0 (+ (+ (- 1) (+ var7 1)) (- 1)))) (= defObj var1)) (= (write var6 var5 var1) var0)))) (inv_main_13 var0 var2 var7))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Heap) (var4 HeapObject) (var5 Addr)) (not (and (and (Inv_Heap var5 var4) (inv_main534_18 var3 var2 var1 var5 var0)) (and (and (not (is-O_item var4)) (= (read var3 var5) var4)) (valid var3 var5))))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Heap)) (not (and (inv_main534_18 var5 var4 var3 var2 var1) (and (and (not (is-O_item var0)) (= (read var5 var2) var0)) (not (valid var5 var2)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Int) (var4 Heap) (var5 HeapObject) (var6 Addr)) (or (not (and (and (Inv_Heap var6 var5) (inv_main532_5 var4 var3 var2 var1 var6)) (and (and (= nullAddr var0) (= (read var4 var6) var5)) (valid var4 var6)))) (_Glue15 var0 var3 var1 var2 var4 var6 var5))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Int) (var4 Addr) (var5 Int) (var6 Heap)) (or (not (and (inv_main532_5 var6 var5 var4 var3 var2) (and (and (= nullAddr var1) (= (read var6 var2) var0)) (not (valid var6 var2))))) (_Glue15 var1 var5 var3 var4 var6 var2 var0))))
(assert (forall ((var0 HeapObject) (var1 item) (var2 Addr) (var3 item) (var4 HeapObject) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Int) (var9 Int) (var10 Addr)) (or (not (and (_Glue15 var10 var9 var8 var7 var6 var5 var4) (and (and (and (and (and (is-O_item var4) (= (getitem var4) var3)) (= (|item::data| var3) var2)) (= (item var7 var2) var1)) (= (O_item var1) var0)) (valid var6 var5)))) (Inv_Heap var5 var0))))
(assert (forall ((var0 HeapObject) (var1 item) (var2 Addr) (var3 item) (var4 Heap) (var5 HeapObject) (var6 Heap) (var7 Addr) (var8 Int) (var9 Int) (var10 Addr) (var11 HeapObject) (var12 Addr)) (or (not (and (and (Inv_Heap var12 var11) (_Glue15 var10 var9 var8 var7 var6 var12 var5)) (and (and (and (and (and (and (and (and (= (read var4 var12) var11) (valid var4 var12)) true) (is-O_item var5)) (= (getitem var5) var3)) (= (|item::data| var3) var2)) (= (item var7 var2) var1)) (= (O_item var1) var0)) (= (write var6 var12 var0) var4)))) (_Glue17 var4 var10 var9 var8 var12 var11))))
(assert (forall ((var0 HeapObject) (var1 item) (var2 Addr) (var3 item) (var4 HeapObject) (var5 Heap) (var6 HeapObject) (var7 Addr) (var8 Heap) (var9 Addr) (var10 Int) (var11 Int) (var12 Addr)) (or (not (and (_Glue15 var12 var11 var10 var9 var8 var7 var6) (and (and (and (and (and (and (and (= (read var5 var7) var4) (not (valid var5 var7))) (is-O_item var6)) (= (getitem var6) var3)) (= (|item::data| var3) var2)) (= (item var9 var2) var1)) (= (O_item var1) var0)) (= (write var8 var7 var0) var5)))) (_Glue17 var5 var12 var11 var10 var7 var4))))
(assert (forall ((var0 Addr) (var1 item) (var2 item) (var3 HeapObject) (var4 Addr) (var5 Int) (var6 Int) (var7 Addr) (var8 Heap) (var9 HeapObject) (var10 Addr)) (or (not (and (and (Inv_Heap var10 var9) (_Glue17 var8 var7 var6 var5 var4 var3)) (and (and (and (and (and (and (and (and (is-O_item var3) (= (getitem var3) var2)) (= (|item::next| var2) var10)) (not (= var10 var7))) (= (read var8 var10) var9)) (is-O_item var9)) (= (getitem var9) var1)) (= (|item::data| var1) var0)) (valid var8 var10)))) (inv_main534_18 var8 var6 var5 var4 var0))))
(assert (forall ((var0 Addr) (var1 item) (var2 HeapObject) (var3 Addr) (var4 item) (var5 HeapObject) (var6 Addr) (var7 Int) (var8 Int) (var9 Addr) (var10 Heap)) (or (not (and (_Glue17 var10 var9 var8 var7 var6 var5) (and (and (and (and (and (and (and (and (is-O_item var5) (= (getitem var5) var4)) (= (|item::next| var4) var3)) (not (= var3 var9))) (= (read var10 var3) var2)) (is-O_item var2)) (= (getitem var2) var1)) (= (|item::data| var1) var0)) (not (valid var10 var3))))) (inv_main534_18 var10 var8 var7 var6 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Heap) (var4 HeapObject) (var5 Addr)) (or (not (and (and (Inv_Heap var5 var4) (inv_main532_5 var3 var2 var1 var0 var5)) (and (= (read var3 var5) var4) (valid var3 var5)))) (_Glue0 var5 var3 var1 var4))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Int) (var3 Addr) (var4 Int) (var5 Heap)) (or (not (and (inv_main532_5 var5 var4 var3 var2 var1) (and (= (read var5 var1) var0) (not (valid var5 var1))))) (_Glue0 var1 var5 var3 var0))))
(assert (forall ((var0 HeapObject) (var1 item) (var2 Addr) (var3 item) (var4 HeapObject) (var5 Addr) (var6 Heap) (var7 Addr)) (or (not (and (_Glue0 var7 var6 var5 var4) (and (and (and (and (and (is-O_item var4) (= (getitem var4) var3)) (= (|item::data| var3) var2)) (= (item var5 var2) var1)) (= (O_item var1) var0)) (valid var6 var7)))) (Inv_Heap var7 var0))))
(assert (forall ((var0 HeapObject) (var1 item) (var2 Addr) (var3 item) (var4 Heap) (var5 HeapObject) (var6 Addr) (var7 Heap) (var8 HeapObject) (var9 Addr)) (not (and (and (Inv_Heap var9 var8) (_Glue0 var9 var7 var6 var5)) (and (and (and (and (and (and (and (and (and (= (read var4 var9) var8) (not (is-O_item var8))) (valid var4 var9)) true) (is-O_item var5)) (= (getitem var5) var3)) (= (|item::data| var3) var2)) (= (item var6 var2) var1)) (= (O_item var1) var0)) (= (write var7 var9 var0) var4))))))
(assert (forall ((var0 HeapObject) (var1 item) (var2 Addr) (var3 item) (var4 HeapObject) (var5 Heap) (var6 HeapObject) (var7 Addr) (var8 Heap) (var9 Addr)) (not (and (_Glue0 var9 var8 var7 var6) (and (and (and (and (and (and (and (and (= (read var5 var9) var4) (not (is-O_item var4))) (not (valid var5 var9))) (is-O_item var6)) (= (getitem var6) var3)) (= (|item::data| var3) var2)) (= (item var7 var2) var1)) (= (O_item var1) var0)) (= (write var8 var9 var0) var5))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Addr) (var5 Int) (var6 Heap) (var7 HeapObject) (var8 Addr)) (or (not (and (and (Inv_Heap var8 var7) (inv_main532_5 var6 var5 var4 var3 var8)) (and (and (= nullAddr var2) (= (read var6 var8) var7)) (valid var6 var8)))) (_Glue6_exp_exp var2 var1 var0 var3 var5 var4 var6 var8 var7))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 HeapObject) (var3 Addr) (var4 Addr) (var5 Int) (var6 Addr) (var7 Int) (var8 Heap)) (or (not (and (inv_main532_5 var8 var7 var6 var5 var4) (and (and (= nullAddr var3) (= (read var8 var4) var2)) (not (valid var8 var4))))) (_Glue6_exp_exp var3 var1 var0 var5 var7 var6 var8 var4 var2))))
(assert (forall ((var0 item) (var1 HeapObject) (var2 item) (var3 Addr) (var4 HeapObject) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Int) (var9 Int) (var10 Addr) (var11 Addr) (var12 Addr)) (or (not (and (_Glue6_exp_exp var12 var11 var10 var9 var8 var7 var6 var5 var4) (and (and (and (and (and (= (item var7 var3) var2) (= (O_item var2) var1)) (is-O_item var4)) (= (getitem var4) var0)) (= (|item::data| var0) var3)) (valid var6 var5)))) (Inv_Heap var5 var1))))
(assert (forall ((var0 item) (var1 Heap) (var2 HeapObject) (var3 item) (var4 Addr) (var5 HeapObject) (var6 Heap) (var7 Addr) (var8 Int) (var9 Int) (var10 Addr) (var11 Addr) (var12 Addr) (var13 HeapObject) (var14 Addr)) (or (not (and (and (Inv_Heap var14 var13) (_Glue6_exp_exp var12 var11 var10 var9 var8 var7 var6 var14 var5)) (and (and (and (and (and (and (and (= (item var7 var4) var3) (= (O_item var3) var2)) (= (read var1 var14) var13)) (is-O_item var5)) (= (getitem var5) var0)) (= (|item::data| var0) var4)) (= (write var6 var14 var2) var1)) (valid var1 var14)))) (_Glue8_exp_exp var1 var12 var11 var10 var9 var8 var14 var13))))
(assert (forall ((var0 item) (var1 HeapObject) (var2 Heap) (var3 HeapObject) (var4 item) (var5 Addr) (var6 HeapObject) (var7 Addr) (var8 Heap) (var9 Addr) (var10 Int) (var11 Int) (var12 Addr) (var13 Addr) (var14 Addr)) (or (not (and (_Glue6_exp_exp var14 var13 var12 var11 var10 var9 var8 var7 var6) (and (and (and (and (and (and (and (= (item var9 var5) var4) (= (O_item var4) var3)) (= (read var2 var7) var1)) (is-O_item var6)) (= (getitem var6) var0)) (= (|item::data| var0) var5)) (= (write var8 var7 var3) var2)) (not (valid var2 var7))))) (_Glue8_exp_exp var2 var14 var13 var12 var11 var10 var7 var1))))
(assert (forall ((var0 AllocResHeap) (var1 item) (var2 HeapObject) (var3 item) (var4 HeapObject) (var5 Addr) (var6 Int) (var7 Int) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Heap)) (or (not (and (_Glue8_exp_exp var11 var10 var9 var8 var7 var6 var5 var4) (and (and (and (and (and (= (O_item var3) var2) (= (item var9 var8) var3)) (is-O_item var4)) (= (getitem var4) var1)) (= (|item::next| var1) var10)) (= (alloc var11 var2) var0)))) (Inv_Heap (newAddr var0) var2))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 AllocResHeap) (var3 item) (var4 HeapObject) (var5 item) (var6 HeapObject) (var7 Addr) (var8 Int) (var9 Int) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Heap)) (or (not (and (_Glue8_exp_exp var13 var12 var11 var10 var9 var8 var7 var6) (and (and (and (and (and (and (and (= (O_item var5) var4) (= (item var11 var10) var5)) (is-O_item var6)) (= (getitem var6) var3)) (= (|item::next| var3) var12)) (= (alloc var13 var4) var2)) (= (newHeap var2) var1)) (= (newAddr var2) var0)))) (inv_main534_18 var1 var8 var9 var7 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Heap) (var4 HeapObject) (var5 Addr)) (not (and (and (Inv_Heap var5 var4) (inv_main532_5 var3 var2 var1 var0 var5)) (and (and (and (is-O_item var4) (= (read var3 var5) var4)) (not (= 4 4))) (valid var3 var5))))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Int) (var3 Addr) (var4 Int) (var5 Heap)) (not (and (inv_main532_5 var5 var4 var3 var2 var1) (and (and (and (is-O_item var0) (= (read var5 var1) var0)) (not (= 4 4))) (not (valid var5 var1)))))))
(assert (forall ((var0 AllocResHeap) (var1 Heap) (var2 HeapObject) (var3 item)) (or (not (and (and (= (O_item var3) var2) (= (alloc var1 var2) var0)) (= emptyHeap var1))) (Inv_Heap (newAddr var0) var2))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap) (var5 AllocResHeap) (var6 Heap) (var7 HeapObject) (var8 item)) (or (not (and (and (and (and (and (and (and (= (O_item var8) var7) (= (alloc var6 var7) var5)) (= (newHeap var5) var4)) (= (newAddr var5) var3)) (= nullAddr var2)) (= emptyHeap var6)) (= var1 0)) (= (+ var0 (- 1)) 0))) (inv_main532_5 var4 var0 var2 var1 var3))))
(assert (forall ((var0 Int) (var1 Heap) (var2 HeapObject) (var3 Addr)) (not (and (and (Inv_Heap var3 var2) (inv_main_13 var1 var3 var0)) (and (and (not (is-O_item var2)) (= (read var1 var3) var2)) (valid var1 var3))))))
(assert (forall ((var0 HeapObject) (var1 Int) (var2 Addr) (var3 Heap)) (not (and (inv_main_13 var3 var2 var1) (and (and (not (is-O_item var0)) (= (read var3 var2) var0)) (not (valid var3 var2)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Heap) (var4 HeapObject) (var5 Addr)) (or (not (and (and (Inv_Heap var5 var4) (inv_main534_18 var3 var2 (+ var1 (- 1)) var5 var0)) (and (= (read var3 var5) var4) (valid var3 var5)))) (_Glue19 var2 var1 var5 var3 var0 var4))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Heap)) (or (not (and (inv_main534_18 var5 var4 (+ var3 (- 1)) var2 var1) (and (= (read var5 var2) var0) (not (valid var5 var2))))) (_Glue19 var4 var3 var2 var5 var1 var0))))
(assert (forall ((var0 HeapObject) (var1 item) (var2 Addr) (var3 item) (var4 HeapObject) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Int) (var9 Int)) (or (not (and (_Glue19 var9 var8 var7 var6 var5 var4) (and (and (and (and (and (and (and (is-O_item var4) (= (getitem var4) var3)) (= (|item::next| var3) var2)) (= (item var2 var5) var1)) (= (O_item var1) var0)) (<= 0 (+ var8 (- 1)))) (not (<= 0 (+ (+ 20 (* (- 1) var9)) (- 1))))) (valid var6 var7)))) (Inv_Heap var7 var0))))
(assert (forall ((var0 Heap) (var1 HeapObject) (var2 item) (var3 Addr) (var4 item) (var5 HeapObject) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Int) (var10 Int)) (or (not (and (_Glue19 var10 var9 var8 var7 var6 var5) (and (and (and (and (and (and (and (is-O_item var5) (= (getitem var5) var4)) (= (|item::next| var4) var3)) (= (item var3 var6) var2)) (= (O_item var2) var1)) (= (write var7 var8 var1) var0)) (<= 0 (+ var9 (- 1)))) (not (<= 0 (+ (+ 20 (* (- 1) var10)) (- 1))))))) (inv_main547_9 var0 var8 var9))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Int) (var5 Int) (var6 Heap) (var7 HeapObject) (var8 Addr)) (or (not (and (and (Inv_Heap var8 var7) (inv_main534_18 var6 (+ var5 (- 1)) (+ var4 (- 1)) var8 var3)) (and (and (not (= var2 0)) (= (read var6 var8) var7)) (valid var6 var8)))) (_Glue2_exp_exp var2 var1 var0 var4 var5 var8 var6 var3 var7))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 HeapObject) (var3 Int) (var4 Addr) (var5 Addr) (var6 Int) (var7 Int) (var8 Heap)) (or (not (and (inv_main534_18 var8 (+ var7 (- 1)) (+ var6 (- 1)) var5 var4) (and (and (not (= var3 0)) (= (read var8 var5) var2)) (not (valid var8 var5))))) (_Glue2_exp_exp var3 var1 var0 var6 var7 var5 var8 var4 var2))))
(assert (forall ((var0 item) (var1 HeapObject) (var2 item) (var3 Addr) (var4 HeapObject) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Int) (var9 Int) (var10 Addr) (var11 Addr) (var12 Int)) (or (not (and (_Glue2_exp_exp var12 var11 var10 var9 var8 var7 var6 var5 var4) (and (and (and (and (and (= (item var3 var5) var2) (= (O_item var2) var1)) (is-O_item var4)) (= (getitem var4) var0)) (= (|item::next| var0) var3)) (valid var6 var7)))) (Inv_Heap var7 var1))))
(assert (forall ((var0 item) (var1 AllocResHeap) (var2 Heap) (var3 HeapObject) (var4 item) (var5 Addr) (var6 HeapObject) (var7 item) (var8 HeapObject) (var9 Addr) (var10 Heap) (var11 Addr) (var12 Int) (var13 Int) (var14 Addr) (var15 Addr)) (or (not (and (_Glue2_exp_exp 1 var15 var14 var13 var12 var11 var10 var9 var8) (and (and (and (and (and (and (and (and (and (<= 0 (+ (* (- 1) var12) 20)) (= (O_item var7) var6)) (= (item var5 var9) var4)) (= (O_item var4) var3)) (= (item var15 var14) var7)) (= (alloc var2 var6) var1)) (is-O_item var8)) (= (getitem var8) var0)) (= (|item::next| var0) var5)) (= (write var10 var11 var3) var2)))) (Inv_Heap (newAddr var1) var6))))
(assert (forall ((var0 item) (var1 AllocResHeap) (var2 Heap) (var3 HeapObject) (var4 item) (var5 Addr) (var6 HeapObject) (var7 item) (var8 HeapObject) (var9 Addr) (var10 Heap) (var11 Addr) (var12 Int) (var13 Int) (var14 Addr) (var15 Addr)) (or (not (and (_Glue2_exp_exp 0 var15 var14 var13 var12 var11 var10 var9 var8) (and (and (and (and (and (and (and (and (and (<= 0 (+ var12 (- 21))) (= (O_item var7) var6)) (= (item var5 var9) var4)) (= (O_item var4) var3)) (= (item var15 var14) var7)) (= (alloc var2 var6) var1)) (is-O_item var8)) (= (getitem var8) var0)) (= (|item::next| var0) var5)) (= (write var10 var11 var3) var2)))) (Inv_Heap (newAddr var1) var6))))
(assert (forall ((var0 item) (var1 Addr) (var2 Heap) (var3 AllocResHeap) (var4 Heap) (var5 HeapObject) (var6 item) (var7 Addr) (var8 HeapObject) (var9 item) (var10 HeapObject) (var11 Addr) (var12 Heap) (var13 Addr) (var14 Int) (var15 Int) (var16 Addr) (var17 Addr)) (or (not (and (_Glue2_exp_exp 1 var17 var16 var15 var14 var13 var12 var11 var10) (and (and (and (and (and (and (and (and (and (and (and (<= 0 (+ (* (- 1) var14) 20)) (= (O_item var9) var8)) (= (item var7 var11) var6)) (= (O_item var6) var5)) (= (item var17 var16) var9)) (= (alloc var4 var8) var3)) (= (newHeap var3) var2)) (= (newAddr var3) var1)) (is-O_item var10)) (= (getitem var10) var0)) (= (|item::next| var0) var7)) (= (write var12 var13 var5) var4)))) (inv_main532_5 var2 var14 var13 var15 var1))))
(assert (forall ((var0 item) (var1 Addr) (var2 Heap) (var3 AllocResHeap) (var4 Heap) (var5 HeapObject) (var6 item) (var7 Addr) (var8 HeapObject) (var9 item) (var10 HeapObject) (var11 Addr) (var12 Heap) (var13 Addr) (var14 Int) (var15 Int) (var16 Addr) (var17 Addr)) (or (not (and (_Glue2_exp_exp 0 var17 var16 var15 var14 var13 var12 var11 var10) (and (and (and (and (and (and (and (and (and (and (and (<= 0 (+ var14 (- 21))) (= (O_item var9) var8)) (= (item var7 var11) var6)) (= (O_item var6) var5)) (= (item var17 var16) var9)) (= (alloc var4 var8) var3)) (= (newHeap var3) var2)) (= (newAddr var3) var1)) (is-O_item var10)) (= (getitem var10) var0)) (= (|item::next| var0) var7)) (= (write var12 var13 var5) var4)))) (inv_main532_5 var2 var14 var13 var15 var1))))
(assert (forall ((var0 Int) (var1 Heap) (var2 HeapObject) (var3 Addr)) (not (and (and (Inv_Heap var3 var2) (inv_main547_9 var1 var3 var0)) (and (and (not (is-O_item var2)) (= (read var1 var3) var2)) (valid var1 var3))))))
(assert (forall ((var0 HeapObject) (var1 Int) (var2 Addr) (var3 Heap)) (not (and (inv_main547_9 var3 var2 var1) (and (and (not (is-O_item var0)) (= (read var3 var2) var0)) (not (valid var3 var2)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Heap) (var4 HeapObject) (var5 Addr)) (not (and (and (Inv_Heap var5 var4) (inv_main534_18 var3 var2 var1 var5 var0)) (and (and (and (is-O_item var4) (= (read var3 var5) var4)) (not (= 4 4))) (valid var3 var5))))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Heap)) (not (and (inv_main534_18 var5 var4 var3 var2 var1) (and (and (and (is-O_item var0) (= (read var5 var2) var0)) (not (= 4 4))) (not (valid var5 var2)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Int) (var4 Heap) (var5 HeapObject) (var6 Addr)) (or (not (and (and (Inv_Heap var6 var5) (inv_main532_5 var4 var3 var2 var1 var6)) (and (and (= nullAddr var0) (= (read var4 var6) var5)) (valid var4 var6)))) (_Glue20 var0 var2 var6 var4 var5))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Addr) (var3 Int) (var4 Addr) (var5 Int) (var6 Heap)) (or (not (and (inv_main532_5 var6 var5 var4 var3 var2) (and (and (= nullAddr var1) (= (read var6 var2) var0)) (not (valid var6 var2))))) (_Glue20 var1 var4 var2 var6 var0))))
(assert (forall ((var0 HeapObject) (var1 item) (var2 Addr) (var3 item) (var4 HeapObject) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr)) (or (not (and (_Glue20 var8 var7 var6 var5 var4) (and (and (and (and (and (is-O_item var4) (= (getitem var4) var3)) (= (|item::data| var3) var2)) (= (item var7 var2) var1)) (= (O_item var1) var0)) (valid var5 var6)))) (Inv_Heap var6 var0))))
(assert (forall ((var0 HeapObject) (var1 item) (var2 Addr) (var3 item) (var4 Heap) (var5 HeapObject) (var6 Heap) (var7 Addr) (var8 Addr) (var9 HeapObject) (var10 Addr)) (or (not (and (and (Inv_Heap var10 var9) (_Glue20 var8 var7 var10 var6 var5)) (and (and (and (and (and (and (and (and (= (read var4 var10) var9) (valid var4 var10)) true) (is-O_item var5)) (= (getitem var5) var3)) (= (|item::data| var3) var2)) (= (item var7 var2) var1)) (= (O_item var1) var0)) (= (write var6 var10 var0) var4)))) (_Glue22 var4 var8 var9))))
(assert (forall ((var0 HeapObject) (var1 item) (var2 Addr) (var3 item) (var4 HeapObject) (var5 Heap) (var6 HeapObject) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Addr)) (or (not (and (_Glue20 var10 var9 var8 var7 var6) (and (and (and (and (and (and (and (= (read var5 var8) var4) (not (valid var5 var8))) (is-O_item var6)) (= (getitem var6) var3)) (= (|item::data| var3) var2)) (= (item var9 var2) var1)) (= (O_item var1) var0)) (= (write var7 var8 var0) var5)))) (_Glue22 var5 var10 var4))))
(assert (forall ((var0 item) (var1 HeapObject) (var2 Addr) (var3 Heap) (var4 HeapObject) (var5 Addr)) (not (and (and (Inv_Heap var5 var4) (_Glue22 var3 var2 var1)) (and (and (and (and (and (and (is-O_item var1) (= (getitem var1) var0)) (= (|item::next| var0) var5)) (not (= var5 var2))) (= (read var3 var5) var4)) (not (is-O_item var4))) (valid var3 var5))))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 item) (var3 HeapObject) (var4 Addr) (var5 Heap)) (not (and (_Glue22 var5 var4 var3) (and (and (and (and (and (and (is-O_item var3) (= (getitem var3) var2)) (= (|item::next| var2) var1)) (not (= var1 var4))) (= (read var5 var1) var0)) (not (is-O_item var0))) (not (valid var5 var1)))))))
(assert (forall ((var0 Int) (var1 Heap) (var2 HeapObject) (var3 Addr)) (or (not (and (and (Inv_Heap var3 var2) (inv_main547_9 var1 var3 (+ var0 1))) (and (= (read var1 var3) var2) (valid var1 var3)))) (_Glue13 var0 var1 var3 var2))))
(assert (forall ((var0 HeapObject) (var1 Int) (var2 Addr) (var3 Heap)) (or (not (and (inv_main547_9 var3 var2 (+ var1 1)) (and (= (read var3 var2) var0) (not (valid var3 var2))))) (_Glue13 var1 var3 var2 var0))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 item) (var3 HeapObject) (var4 Addr) (var5 Heap) (var6 Int)) (or (not (and (_Glue13 var6 var5 var4 var3) (and (and (and (and (and (is-O_item var3) (= (getitem var3) var2)) (= (|item::data| var2) var1)) (<= 0 (+ (+ (- 1) (+ var6 1)) (- 1)))) (= defObj var0)) (valid var5 var1)))) (Inv_Heap var1 var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 item) (var3 HeapObject) (var4 HeapObject) (var5 Addr) (var6 Heap) (var7 Int)) (or (not (and (_Glue13 var7 var6 var5 var4) (and (and (and (and (and (and (= defObj var3) (is-O_item var4)) (= (getitem var4) var2)) (= (|item::data| var2) var1)) (= (write var6 var1 var3) var0)) (valid var0 var5)) (<= 0 (+ (+ (- 1) (+ var7 1)) (- 1)))))) (Inv_Heap var5 var3))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 item) (var3 Heap) (var4 HeapObject) (var5 Heap) (var6 HeapObject) (var7 Addr) (var8 Heap) (var9 Int)) (or (not (and (_Glue13 var9 var8 var7 var6) (and (and (and (and (and (and (and (= (write var5 var7 var4) var3) (= defObj var4)) (is-O_item var6)) (= (getitem var6) var2)) (= (|item::next| var2) var1)) (= (|item::data| var2) var0)) (= (write var8 var0 var4) var5)) (<= 0 (+ (+ (- 1) (+ var9 1)) (- 1)))))) (inv_main_13 var3 var1 var9))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Heap) (var4 HeapObject) (var5 Addr)) (not (and (and (Inv_Heap var5 var4) (inv_main532_5 var3 var2 var1 var0 var5)) (and (and (not (is-O_item var4)) (= (read var3 var5) var4)) (valid var3 var5))))))
(assert (forall ((var0 HeapObject) (var1 Addr) (var2 Int) (var3 Addr) (var4 Int) (var5 Heap)) (not (and (inv_main532_5 var5 var4 var3 var2 var1) (and (and (not (is-O_item var0)) (= (read var5 var1) var0)) (not (valid var5 var1)))))))
(check-sat)
