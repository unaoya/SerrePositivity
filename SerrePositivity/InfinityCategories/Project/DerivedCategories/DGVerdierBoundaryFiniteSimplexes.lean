module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierBoundaryRefinedSimplex
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierBoundaryOverFillers
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGLastHornGeneralComponents

/-! # 任意次元の実分母境界有限族の同じ部分圏内での同時充填

概要：新 apex の分母性から、全回収単体を元の実分母部分圏へ同時に戻す。
方針：共通追加分母と全充填を、任意次元の同じ実分母単体への持ち上げへ渡す。
規約：零面と全単体の台を保持する。使われ方：有限共通始錐の高次整合性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]
variable {P : Set D} {x source : D} {m : ℕ} {d : Fin m → ℕ}
variable (B : ∀ i, (∂Δ[d i + 1] : SSet.{max u v}) ⟶ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet))
variable (T : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGGeneralLastHornFiniteRefinement P source
  (fun i => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierBoundaryHorn A D P x (B i)))

/-- 同じ共通追加分母後に戻した、同じ実分母部分圏内の全次元の実単体。 -/
def dgVerdierBoundaryRefinementSimplex (i : Fin m) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet.{max u v}) _⦋d i + 1⦌ :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierBoundaryRefinedSimplex A D P x (B i) (T.residuals i).q (T.residuals i).s
    (T.filler i) (T.filler_fac i) (T.residuals i).denominator

/-- 全単体の台は、供給済みの同じ実 over 単体そのもの。 -/
lemma dgVerdierBoundaryRefinementSimplex_val (i : Fin m) :
    (dgVerdierBoundaryRefinementSimplex A D B T i).val =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierBoundaryRefinementOverSimplex A D B T i := rfl

/-- 同じ部分圏内の全零面は、元の同じ指定境界零面である。 -/
lemma dgVerdierBoundaryRefinementSimplex_face_zero (i : Fin m) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).δ (0 : Fin (d i + 2))
      (dgVerdierBoundaryRefinementSimplex A D B T i) =
        SSet.yonedaEquiv (boundary.ι (0 : Fin (d i + 2)) ≫ B i) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierBoundaryRefinedSimplex_face_zero A D P x (B i) _ _ _ _ _

/-- 全新単体の始対象は、同じ一つの共通追加閉分母の始対象である。 -/
lemma dgVerdierBoundaryRefinementSimplex_obj_zero (i : Fin m) :
    (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceSimplex _
      (dgVerdierBoundaryRefinementSimplex A D B T i).val)).obj 0 = T.q := by
  rw [dgVerdierBoundaryRefinementSimplex_val, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierBoundaryRefinementOverSimplex_simplex]
  change (T.residuals i).solution.simplex.obj 0 = T.q
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGGeneralLastHornSolution.simplex_obj, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornSourceRefinement_obj_zero,
    T.source_eq i]

/-- 共通始対象の実分母境界有限族に、同じ部分圏内の全次数の実単体を同時供給する。 -/
theorem dgVerdierBoundaryFinite_exists_refinedSimplexes
    (hsource : ∀ i, (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierBoundaryHorn A D P x (B i))).obj 0 = source) :
    ∃ T : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGGeneralLastHornFiniteRefinement P source
        (fun i => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierBoundaryHorn A D P x (B i)),
      ∀ i, ∃ U : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet.{max u v}) _⦋d i + 1⦌,
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceSimplex _ U.val = T.filler i ∧
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).δ (0 : Fin (d i + 2)) U =
          SSet.yonedaEquiv (boundary.ι (0 : Fin (d i + 2)) ≫ B i) := by
  obtain ⟨T⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierBoundaryFiniteRefinement_nonempty A D B hsource
  exact ⟨T, fun i => ⟨dgVerdierBoundaryRefinementSimplex A D B T i,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierBoundaryRefinementOverSimplex_simplex A D B T i,
    dgVerdierBoundaryRefinementSimplex_face_zero A D B T i⟩⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
