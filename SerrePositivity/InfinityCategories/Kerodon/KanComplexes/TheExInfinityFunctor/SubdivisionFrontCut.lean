module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.SubdivisionFaceCut

/-!
# 前側の面での閾値の減少

概要：前側の面の前の切断を、次元を上げた閾値の切断に吸収する。
方針：閾値より先の頂点は前側の面によって一つ増えることを使う。
規約：Moss 2020 Lemma 28 の退化単体の計算に用いる補助。
使われ方：通常の退化の元の単体の複雑度の上界。

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
概要：前側の面は、閾値を超える頂点を一つ大きい閾値の先へ送る。
方針：succAbove の前側の面に対する値を使う。
規約：Moss 2020 Lemma 28 の補助、i≤k。
使われ方：切断の一般的な吸収則の仮定。
-/
theorem liftedFace_front_above (n : ℕ) (k : Fin (n + 1)) (i : Fin (n + 2))
    (hi : i ≤ k.castSucc) (x : ULift.{u} (Fin (n + 1))) (hx : ULift.up k < x) :
    ULift.up k.succ < liftedFace n i x := by
  change k.succ < i.succAbove x.down
  rw [Fin.succAbove_of_le_castSucc _ _ (hi.trans
    (Fin.castSucc_le_castSucc_iff.mpr (le_of_lt hx)))]
  exact Fin.succ_lt_succ_iff.mpr hx

/--
概要：前側の面の前の切断は、後の一つ大きい閾値の切断へ吸収される。
方針：有限鎖の吸収則を、前側の面の頂点の不等式で適用する。
規約：Moss 2020 Lemma 28 の退化の元の複雑度を下げる補助。
使われ方：Ex の前側の面の複雑度の計算。
-/
@[reassoc] theorem subdivisionCutAt_front_face_absorb (n : ℕ) (k : Fin (n + 1))
    (i : Fin (n + 2)) (hi : i ≤ k.castSucc) :
    subdivisionCutAt.{u} (SimplexCategory.mk n) k ≫
      SimplexCategory.sd.map (SimplexCategory.δ i) ≫
        subdivisionCutAt (SimplexCategory.mk (n + 1)) k.succ =
    SimplexCategory.sd.map (SimplexCategory.δ i) ≫
      subdivisionCutAt (SimplexCategory.mk (n + 1)) k.succ := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro s
  apply nerve.ext_of_isThin
  funext j
  exact finiteChainCut_map_absorb (liftedFace n i) (ULift.up k) (ULift.up k.succ)
    (liftedFace_front_above n k i hi) (s.obj j)

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
