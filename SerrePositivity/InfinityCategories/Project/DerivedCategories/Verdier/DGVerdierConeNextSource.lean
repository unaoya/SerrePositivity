module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FiberCofiber.TruncatedConeNextBoundary
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGVerdierConeRefinementData
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGVerdierBoundaryLastDenominator
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.SliceComparisons.DGOverBoundaryRefinedFaces

/-! # 有限次数錐の次次数境界の共通始対象

概要：次次数の全実境界ホーンの始対象は、元の同じ共通 apex の始対象である。
方針：正番号一面の回収対象と、既存の錐単体の始頂点の等式を使う。
規約：全ての対象を元の dg 圏で厳密に揃える。使われ方：次次数の有限同時原始元。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]
variable (P : Set D) (x : D) {K : SSet.{max u v}}
variable {f : K ⟶ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet)} {N : ℕ}
variable (C : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.TruncatedJoinConeData f N)

/-- 次次数の全実境界ホーンの始対象は、元の同じ apex の始対象。 -/
lemma dgVerdierConeNextBoundary_source (σ : K _⦋N + 1⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierBoundaryHorn A D P x (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.truncatedConeNextBoundary C σ))).obj 0 =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierSimplexSource A D P x C.apex := by
  have he : SSet.yonedaEquiv
      (boundary.ι (0 : Fin (N + 2)).succ ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.truncatedConeNextBoundary C σ) =
        C.simplex N le_rfl (K.δ 0 σ) := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.truncatedConeNextBoundary_face_positive, Equiv.apply_symm_apply]
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverBoundaryFace_source _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.truncatedConeNextBoundary C σ ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x).ι)
    (0 : Fin (N + 2)).succ (Fin.succ_ne_zero _)).trans
      ((congrArg (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierSimplexSource A D P x) he).trans
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierConeSimplex_source A D P x C N le_rfl (K.δ 0 σ)))

end SerrePositivity.InfinityCategories.Project.DerivedCategories
