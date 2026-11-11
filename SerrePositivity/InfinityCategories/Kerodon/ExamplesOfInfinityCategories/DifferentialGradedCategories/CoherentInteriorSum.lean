module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CoherentVertexCoordinates

/-!
# 内部座標の和と有限頂点番号の和

概要：native な内部点の和を、元の有限頂点集合上の内部点以外が零となる和へ移す。
方針：内部座標を元の頂点番号へ単射で送り、その像の外を零にする。
規約：宇宙の異なる二つの有限型の間で再添字付けする。
使われ方：HA 1.3.1.16、Kerodon 2.5.9（Tag 00SC） の既存 dg 単体の rhs の和への移送。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

/-- 概要：内部にある有限頂点を native な内部座標にする。
方針：ULift と開区間の証明を付け、有限集合の像への所属を示す。
規約：元の頂点番号の値を保つ。
使われ方：Kerodon 2.5.9（Tag 00SC） の rhs の各内部点の座標。 -/
def coherentInteriorVertexPoint {n : ℕ} (I : Finset (Fin (n + 1)))
    {a b : Fin (n + 1)} (j : Fin (n + 1)) (hj : j ∈ I) (haj : a < j) (hjb : j < b) :
    ↥(_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentVertexInterior.{u} I a b) :=
  ⟨⟨ULift.up j, haj, hjb⟩, (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.mem_coherentInteriorSet _ _ _ _).mpr
    (Finset.mem_image.mpr ⟨j, hj, rfl⟩)⟩

/-- 概要：native な内部座標を元の有限頂点の部分型へ単射で戻す。
方針：ULift.down で番号を取り、像への所属から元の所属を得る。
規約：内部点の開区間の条件は忘れる。
使われ方：HA 1.3.1.16 の内部点の和と頂点の和の比較。 -/
def coherentInteriorVertexEmbedding {n : ℕ} (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) :
    ↥(_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentVertexInterior.{u} I a b) ↪ ↥I where
  toFun t := ⟨t.val.val.down, by
    have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.mem_coherentInteriorSet _ _ _ _).mp t.property
    obtain ⟨j, hj, he⟩ := Finset.mem_image.mp h
    have he' := congrArg ULift.down he
    exact he' ▸ hj⟩
  inj' := by
    intro t s h
    apply Subtype.ext
    apply Subtype.ext
    apply ULift.ext
    exact congrArg Subtype.val h

/-- 概要：内部座標の和は有限頂点集合上で内部点だけを足す和に等しい。
方針：内部座標からの単射を使い、その像の外での零を確認する。
規約：値は任意の可換加法モノイドに取れる。
使われ方：Kerodon 2.5.9（Tag 00SC） の立方体の微分公式を既存の rhs に合わせる。 -/
lemma coherentInteriorVertex_sum {M : Type*} [AddCommMonoid M] {n : ℕ}
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1))
    (F : ↥(_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentVertexInterior.{u} I a b) → M) :
    (∑ t, F t) = ∑ j : I, if h : a < j.val ∧ j.val < b then
      F (coherentInteriorVertexPoint I j.val j.property h.1 h.2) else 0 := by
  let e := coherentInteriorVertexEmbedding.{u} I a b
  let G (j : I) := if h : a < j.val ∧ j.val < b then
    F (coherentInteriorVertexPoint I j.val j.property h.1 h.2) else 0
  refine Fintype.sum_of_injective e e.injective F G ?_ ?_
  · intro j hj
    dsimp only [G]
    split_ifs with h
    · exfalso
      exact hj ⟨coherentInteriorVertexPoint I j.val j.property h.1 h.2, rfl⟩
    · rfl
  · intro t
    dsimp only [G]
    rw [dite_eq_left (show a < (e t).val ∧ (e t).val < b from t.val.property)]
    apply congrArg F
    apply Subtype.ext
    apply Subtype.ext
    apply ULift.ext
    rfl

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
