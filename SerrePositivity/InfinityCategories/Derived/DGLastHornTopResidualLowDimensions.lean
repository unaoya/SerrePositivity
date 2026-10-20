module
public import SerrePositivity.InfinityCategories.Derived.DGLastHornExpandedSolution
public import SerrePositivity.InfinityCategories.Derived.DGLastHornCochains
public import SerrePositivity.InfinityCategories.Derived.DGFourLastHornRefinedResiduals

/-! # 一般最上位残差 K と後合成の既存三次・四次との照合

概要：一般の既知 K と最後辺による Q 項は、三次・四次の既存二未知微分式の同じ成分。
方針：三次では元の rhs 展開と未知欠面の零、四次では既存の最上位 rhs 公式を使う。
規約：符号と元の射を厳密に保持。使われ方：一般残差 cone の低次検証。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open DifferentialGraded DGNerve SSet
open scoped Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 三次の一般 K は、既存の実三次ホーンの同じ既知残差。 -/
lemma dgGeneralLastHornTopResidual_three
    (σ : (Λ[3, 3] : SSet.{max u v}) ⟶ dgNerve A D) :
    dgGeneralLastHornTopResidual σ = dgLastHornTopResidual σ := by
  have hQ := dgGeneralLastHornMissingHom_zero σ
  have hm : dgLastHornMissingIndex 1 = {0, 1, 2} := by decide
  simp only [hm] at hQ
  have ht : (HornData.knownData σ).tripleHom 0 1 2 (by decide) (by decide) = 0 := hQ
  have hr := dgTetrahedron_rhs_top (HornData.knownData σ)
  rw [ht, compose_zero, add_zero] at hr
  exact hr

/-- 四次の一般 K も、既存の実四次ホーンの同じ既知残差。 -/
lemma dgGeneralLastHornTopResidual_four
    (σ : (Λ[4, 4] : SSet.{max u v}) ⟶ dgNerve A D) :
    dgGeneralLastHornTopResidual σ = dgFourLastHornTopResidual σ :=
  dgFourLastHorn_rhs_top σ

/-- 三次の一般 Q 後合成は、既存二未知微分式の同じ最後辺との合成。 -/
lemma dgGeneralLastHornPostcomposeQ_three
    (σ : (Λ[3, 3] : SSet.{max u v}) ⟶ dgNerve A D)
    (Q : GradedHom A ((HornData.knownData σ).obj 0) ((HornData.knownData σ).obj 2) (-1)) :
    dgGeneralLastHornPostcomposeQ σ Q =
      compose A ((HornData.knownData σ).edgeHom 2 3 (by decide)) Q (by decide) := rfl

/-- 四次の一般 Q 後合成も、既存二未知微分式の同じ最後辺との合成。 -/
lemma dgGeneralLastHornPostcomposeQ_four
    (σ : (Λ[4, 4] : SSet.{max u v}) ⟶ dgNerve A D)
    (Q : GradedHom A ((HornData.knownData σ).obj 0) ((HornData.knownData σ).obj 3) (-2)) :
    dgGeneralLastHornPostcomposeQ σ Q =
      compose A ((HornData.knownData σ).edgeHom 3 4 (by decide)) Q (by decide) := rfl

end SerrePositivity.InfinityCategories
