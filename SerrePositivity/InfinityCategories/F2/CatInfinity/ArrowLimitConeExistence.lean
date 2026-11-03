module

public import SerrePositivity.InfinityCategories.F2.CatInfinity.TensorConeComponentCriterion
public import SerrePositivity.InfinityCategories.Core.CatInfinity.ConeValEquality
public import SerrePositivity.InfinityCategories.F1B.CatInfinity.ArrowEndpointPair
public import SerrePositivity.InfinityCategories.Core.FunctorPointwiseLimitExistence

/-!
概要：両端の極限の存在から、両端評価の像も極限である矢印圏の極限錐を作る。
方針：関手圏の点ごとの極限錐を選び、両端の直積で像の極限性を証明する。
規約：区間の両端は元の source・target 評価。
使われ方：lax pullback の入力を固定する錐の存在構成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：両端で極限である矢印圏の錐の両端評価の像は極限錐。
方針：元の両端評価と直積射影の一致で成分の錐を照合する。
規約：元の指定錐 c の像を扱う。
使われ方：両端を指定錐へ合わせる厳密化の像の極限性。 -/
lemma isLimitCone_arrowEndpointPair_of_pointwise {J C : SSet.{u}} [Quasicategory C]
    {r : J ⟶ (ihom (Δ[1] : SSet.{u})).obj C} (c : JoinCone r)
    (hc : IsPointwiseLimitCone c) : IsLimitCone (mapJoinCone (arrowEndpointPair C) c) := by
  apply isLimitCone_tensor_of_components
  · apply (isLimitCone_iff_of_cone_val_eq _ _ ?_).2 (hc (stdSimplex.obj₀Equiv.symm 0))
    change (c.val ≫ arrowEndpointPair C) ≫ fst C C =
      c.val ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0)
    rw [Category.assoc, arrowEndpointPair, lift_fst]
  · apply (isLimitCone_iff_of_cone_val_eq _ _ ?_).2 (hc (stdSimplex.obj₀Equiv.symm 1))
    change (c.val ≫ arrowEndpointPair C) ≫ snd C C =
      c.val ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 1)
    rw [Category.assoc, arrowEndpointPair, lift_snd]

/-- 概要：両端が極限を持つ図式は、両端評価の像も極限となる極限錐を持つ。
方針：区間の全頂点を列挙して点ごとの極限の存在定理を使う。
規約：元の矢印圏内の図式 r を固定する。
使われ方：lax pullback の錐の第一成分の存在。 -/
lemma exists_limitCone_arrow_with_limit_image {J C : SSet.{u}} [Quasicategory C]
    (r : J ⟶ (ihom (Δ[1] : SSet.{u})).obj C)
    (h0 : HasLimit (evaluateFunctorDiagram r (stdSimplex.obj₀Equiv.symm 0)))
    (h1 : HasLimit (evaluateFunctorDiagram r (stdSimplex.obj₀Equiv.symm 1))) :
    ∃ c : JoinCone r, IsLimitCone c ∧ IsLimitCone (mapJoinCone (arrowEndpointPair C) c) := by
  have hp : HasPointwiseLimits r := by
    intro k
    obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective k
    fin_cases i
    · exact h0
    · exact h1
  obtain ⟨c, hc⟩ := exists_pointwiseLimitCone r hp
  exact ⟨c, isLimitCone_of_pointwise c hc, isLimitCone_arrowEndpointPair_of_pointwise c hc⟩

end SerrePositivity.InfinityCategories.F2
