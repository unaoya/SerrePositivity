module
public import SerrePositivity.InfinityCategories.Derived.DGLastHornGeneralComponents
public import SerrePositivity.InfinityCategories.Derived.DGLastHornCochains
public import SerrePositivity.InfinityCategories.Derived.DGFourLastHornCochains

/-! # 一般最後外ホーンの二未知データと既存三次・四次構成の一致

概要：一般残差 R と Q 挿入データは、三次・四次では検証済みの既存構成そのもの。
方針：欠面有限集合と次数を具体化し、三次では実 rhs の既存展開公式を使う。
規約：実データの厳密等式。使われ方：一般残差・符号計算と既存二未知方程式の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 次元三の一般欠面残差は、既存の同じ実三次ホーンの欠面残差。 -/
lemma dgGeneralLastHornMissingResidual_three
    (σ : (Λ[3, 3] : SSet.{max u v}) ⟶ dgNerve A D) :
    dgGeneralLastHornMissingResidual σ = dgLastHornMissingResidual σ := by
  unfold dgGeneralLastHornMissingResidual
  have hm : dgLastHornMissingIndex 1 = {0, 1, 2} := by decide
  simp only [hm]
  exact dgTetrahedron_rhs_missing (HornData.knownData σ)

/-- 次元四の一般欠面残差も、既存の同じ実四次ホーンの残差。 -/
lemma dgGeneralLastHornMissingResidual_four
    (σ : (Λ[4, 4] : SSet.{max u v}) ⟶ dgNerve A D) :
    dgGeneralLastHornMissingResidual σ = dgFourLastHornMissingResidual σ := by
  unfold dgGeneralLastHornMissingResidual dgFourLastHornMissingResidual
  have hm : dgLastHornMissingIndex 2 = {0, 1, 2, 3} := by decide
  simp only [hm]
  rfl

/-- 次元三の一般 Q 挿入は、既存の同じ実データの Q 挿入。 -/
lemma dgGeneralLastHornQData_three
    (σ : (Λ[3, 3] : SSet.{max u v}) ⟶ dgNerve A D)
    (Q : GradedHom A ((HornData.knownData σ).obj 0) ((HornData.knownData σ).obj 2) (-1)) :
    dgGeneralLastHornQData σ Q = dgLastHornQData σ Q := by
  unfold dgGeneralLastHornQData dgLastHornQData dgTetrahedronWithQ
  have hm : dgLastHornMissingIndex 1 = {0, 1, 2} := by decide
  simp only [hm]
  rfl

/-- 次元四の一般 Q 挿入も、既存の同じ実データの Q 挿入。 -/
lemma dgGeneralLastHornQData_four
    (σ : (Λ[4, 4] : SSet.{max u v}) ⟶ dgNerve A D)
    (Q : GradedHom A ((HornData.knownData σ).obj 0) ((HornData.knownData σ).obj 3) (-2)) :
    dgGeneralLastHornQData σ Q = dgFourLastHornQData σ Q := by
  unfold dgGeneralLastHornQData dgFourLastHornQData
  have hm : dgLastHornMissingIndex 2 = {0, 1, 2, 3} := by decide
  simp only [hm]
  rfl

end SerrePositivity.InfinityCategories
