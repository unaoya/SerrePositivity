module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.SubdivisionMaximum

/-!
# 前側の面と複雑度の吸収

概要：前側の面に拡張退化と複雑度作用素を合成した像を初期区間として計算する。
方針：singleton の像と最大元の保存で、閾値以上の最大元を持つ全ての集合を扱う。
規約：Moss 2020 Lemma 26 (2)。原典の join の計算を最大元の単調性で補う。
使われ方：pairing の前側の面の複雑度が下がること。

対応節は Kerodon 3.3（Tag 00XF）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
open CategoryTheory PartialOrder

/--
概要：面、拡張退化、複雑度作用素を順に適用する有限鎖の単調写像。
方針：既存の三つの単調写像を合成する。
規約：Moss 2020 Lemma 26 (2) の主要な合成。
使われ方：前の複雑度作用素を吸収する比較。
-/
def finiteChainFrontImage (n : ℕ) (k : Fin (n + 1)) (i : Fin (n + 2)) :
    NonemptyFiniteChains (ULift.{u} (Fin (n + 1))) →o
      NonemptyFiniteChains (ULift.{u} (Fin (n + 1))) :=
  (finiteChainCut n (ULift.up k)).comp ((finiteChainDegeneracy n k).comp
    (NonemptyFiniteChains.orderHomMap (liftedFace n i)))

/--
概要：前側の面の合成の最大元は通常の面・退化で最大元を送って計算できる。
方針：各作用素の最大元の計算を順に適用する。
規約：Moss 2020 Lemma 26 (2) の補助。
使われ方：像が初期区間に含まれること。
-/
theorem finiteChainFrontImage_maximum (n : ℕ) (k : Fin (n + 1)) (i : Fin (n + 2))
    (s : NonemptyFiniteChains (ULift.{u} (Fin (n + 1)))) :
    finiteChainMaximum (finiteChainFrontImage n k i s) =
      liftedDegeneracy n k (liftedFace n i (finiteChainMaximum s)) := by
  change finiteChainMaximum (finiteChainCut n (ULift.up k)
    (finiteChainDegeneracy n k (s.map (liftedFace n i)))) = _
  rw [finiteChainCut_maximum, finiteChainDegeneracy_maximum, finiteChainMaximum_map]

/--
概要：閾値以上の singleton は前側の面の合成でその頂点までの初期区間に送られる。
方針：閾値と等しい場合は拡張退化の特別な頂点、それより大きい場合は複雑度作用素を使う。
規約：Moss 2020 Lemma 26 (2) の singleton 上の計算。
使われ方：任意の入力集合の像の下界。
-/
theorem finiteChainFrontImage_singleton_ge (n : ℕ) (k : Fin (n + 1)) (i : Fin (n + 2))
    (hi : i ≤ k.castSucc) (x : ULift.{u} (Fin (n + 1))) (hx : ULift.up k ≤ x) :
    finiteChainFrontImage n k i (finiteChainSingleton x) = finiteChainInitialSegment n x := by
  change finiteChainCut n (ULift.up k)
    (finiteChainDegeneracy n k ((finiteChainSingleton x).map (liftedFace n i))) = _
  rw [finiteChainMap_singleton]
  have hf : liftedFace n i x = ULift.up x.down.succ := by
    apply ULift.ext
    exact Fin.succAbove_of_le_castSucc i x.down (hi.trans (Fin.castSucc_le_castSucc_iff.mpr hx))
  rw [hf, finiteChainDegeneracy_singleton]
  by_cases he : x = ULift.up k
  · subst x
    rw [ite_eq_left rfl, finiteChainCut_initialSegment]
  · have hn : (ULift.up x.down.succ : ULift.{u} (Fin (n + 2))) ≠ ULift.up k.succ := by
      intro h
      exact he (ULift.ext (Fin.succ_inj.mp (congrArg ULift.down h)))
    rw [ite_eq_right hn]
    have hd : liftedDegeneracy n k (ULift.up x.down.succ) = x :=
      ULift.ext (Fin.predAbove_succ_of_le k x.down hx)
    rw [hd, finiteChainCut_singleton, ite_eq_right (not_le_of_gt (lt_of_le_of_ne hx (Ne.symm he)))]

/--
概要：最大元が閾値以上の有限鎖は、その最大元までの初期区間に送られる。
方針：最大元の singleton が入力に含まれることと、像の最大元の上界を組み合わせる。
規約：Moss 2020 Lemma 26 (2) の最大元を使う補助証明。
使われ方：前に挿入した複雑度作用素が吸収されること。
-/
theorem finiteChainFrontImage_of_max_ge (n : ℕ) (k : Fin (n + 1)) (i : Fin (n + 2))
    (hi : i ≤ k.castSucc) (s : NonemptyFiniteChains (ULift.{u} (Fin (n + 1))))
    (hs : ULift.up k ≤ finiteChainMaximum s) :
    finiteChainFrontImage n k i s = finiteChainInitialSegment n (finiteChainMaximum s) := by
  have hm : finiteChainMaximum (finiteChainFrontImage n k i s) = finiteChainMaximum s := by
    rw [finiteChainFrontImage_maximum]
    exact liftedDegeneracy_face_ge n k i hi _ hs
  apply le_antisymm
  · have h := finiteChain_le_initialSegment n (finiteChainFrontImage n k i s)
    rw [hm] at h
    exact h
  · have hsingle : finiteChainSingleton (finiteChainMaximum s) ≤ s := by
      intro x hx
      have hx' : x = finiteChainMaximum s := Finset.mem_singleton.mp hx
      exact hx' ▸ Finset.max'_mem s.finset s.nonempty
    have h := (finiteChainFrontImage n k i).monotone hsingle
    rw [finiteChainFrontImage_singleton_ge n k i hi _ hs] at h
    exact h

/--
概要：前側の面の合成の前で一つ小さい閾値に切っても像は変わらない。
方針：切断が入力を変える場合には最大元が次の閾値以上であり、両辺が同じ初期区間に入る。
規約：Moss 2020 Lemma 26 (2) の有限鎖上の式。
使われ方：前側の面の複雑度の減少。
-/
theorem finiteChainFrontImage_absorb (n : ℕ) (h : Fin (n + 1)) (i : Fin (n + 3))
    (hi : i ≤ h.succ.castSucc)
    (s : NonemptyFiniteChains (ULift.{u} (Fin (n + 2)))) :
    finiteChainFrontImage (n + 1) h.succ i (finiteChainCut (n + 1) (ULift.up h.castSucc) s) =
      finiteChainFrontImage (n + 1) h.succ i s := by
  change finiteChainFrontImage (n + 1) h.succ i
    (if finiteChainMaximum s ≤ ULift.up h.castSucc then s else
      finiteChainInitialSegment (n + 1) (finiteChainMaximum s)) = _
  by_cases hs : finiteChainMaximum s ≤ ULift.up h.castSucc
  · rw [ite_eq_left hs]
  · rw [ite_eq_right hs]
    have hge : ULift.up h.succ ≤ finiteChainMaximum s :=
      Fin.castSucc_lt_iff_succ_le.mp (lt_of_not_ge hs)
    rw [finiteChainFrontImage_of_max_ge (n + 1) h.succ i hi s hge,
      finiteChainFrontImage_of_max_ge (n + 1) h.succ i hi _
        (by rw [finiteChainMaximum_initialSegment]; exact hge), finiteChainMaximum_initialSegment]

/--
概要：前側の面の後の拡張退化と複雑度作用素は、前の一つ小さい切断を吸収する。
方針：有限鎖上の最大元による吸収則を nerve の各頂点へ移す。
規約：Moss 2020 Lemma 26 (2)、k=h+1。
使われ方：pairing の指定面より前の面の複雑度の上界。
-/
@[reassoc] theorem subdivisionDegeneracyAt_front_absorb (n : ℕ) (h : Fin (n + 1))
    (i : Fin (n + 3)) (hi : i ≤ h.succ.castSucc) :
    subdivisionCutAt.{u} (SimplexCategory.mk (n + 1)) h.castSucc ≫
      SimplexCategory.sd.map (SimplexCategory.δ i) ≫ subdivisionDegeneracyAt (n + 1) h.succ ≫
        subdivisionCutAt (SimplexCategory.mk (n + 1)) h.succ =
    SimplexCategory.sd.map (SimplexCategory.δ i) ≫ subdivisionDegeneracyAt (n + 1) h.succ ≫
      subdivisionCutAt (SimplexCategory.mk (n + 1)) h.succ := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro s
  apply nerve.ext_of_isThin
  funext j
  exact finiteChainFrontImage_absorb n h i hi (s.obj j)

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
