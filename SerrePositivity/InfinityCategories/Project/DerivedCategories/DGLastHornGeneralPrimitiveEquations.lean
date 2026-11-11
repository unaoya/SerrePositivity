module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGLastHornGeneralRefinedCochains
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGGradedCompositionDegreeTransport

/-! # 追加分母後の一般 A 微分式を元の次数へ戻す

概要：原始元からの A 微分を、元の最上位方程式と同じ −n−1+1 の次数で読む。
方針：正規化の線形同型の単射性と、閉前合成・零次数後合成の輸送を使う。
規約：R・K と追加実閉射は同じもの。使われ方：細分ホーンの二未知解への接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D] {n : ℕ}
variable {P : Set D} {σ : (Λ[n + 2, Fin.last (n + 2)] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D}
variable (H : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGGeneralLastHornResidualRefinement P σ)

/-- 同じ実 A の微分式を、元の K と同じ未正規化次数で回収する。 -/
lemma DGGeneralLastHornResidualRefinement.a_differential_original :
    _root_.SerrePositivity.DifferentialGraded.differential A H.a =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose A D (-(n : ℤ) - 1 + 1) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornTopResidual σ) H.s +
        compose A ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).edgeHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate n) (Fin.last (n + 2))
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate_lt_last n)) H.Q (by omega) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport (A := A) (D := D) (rfl : H.q = H.q) rfl
    (by omega : -(n : ℤ) - 1 + 1 = -(n : ℤ))).injective
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedHomTransport_differential_to, map_add, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose_degreeTransport,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgZeroPostcompose_outputTransport]
  exact H.a_differential

end SerrePositivity.InfinityCategories.Project.DerivedCategories
