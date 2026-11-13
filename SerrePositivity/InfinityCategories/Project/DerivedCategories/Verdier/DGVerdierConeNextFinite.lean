module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGVerdierConeNextSource
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGVerdierConeRefinement
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGVerdierBoundaryFiniteSimplexes

/-! # 同じ有限次数錐の次次数の有限セル族の同時充填

概要：指定次次数単体の有限族に、一つの追加実分母と同じ部分圏内の実充填を供給する。
方針：全境界の共通始対象を元の apex に揃え、一般有限境界定理を使う。
規約：退化条件の次次数への延長は別工程。使われ方：非退化セル有限族の一段の処理。
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
variable (P : Set D) (x : D) {K : SSet.{max u v}}
variable {f : K ⟶ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet)} {N : ℕ}
variable (C : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.TruncatedJoinConeData f N) {m : ℕ} (τ : Fin m → K _⦋N + 1⦌)

/-- 次次数の指定有限族の実境界を消す、一つの追加実分母後の原始元は存在する。 -/
theorem dgVerdierConeNextFiniteRefinement_nonempty :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGGeneralLastHornFiniteRefinement P (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierSimplexSource A D P x C.apex)
      (fun i => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierBoundaryHorn A D P x (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.truncatedConeNextBoundary C (τ i)))) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierBoundaryFiniteRefinement_nonempty A D
    (fun i => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.truncatedConeNextBoundary C (τ i))
    (fun i => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierConeNextBoundary_source A D P x C (τ i))

variable (T : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGGeneralLastHornFiniteRefinement P (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierSimplexSource A D P x C.apex)
  (fun i => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierBoundaryHorn A D P x (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.truncatedConeNextBoundary C (τ i))))

/-- 同じ一つの追加実分母で更新した、既存下次数の錐全体。 -/
def dgVerdierConeNextLower : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.TruncatedJoinConeData f N :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierTruncatedConeRefinement A D P x C T.q T.s T.denominator

/-- 同じ一つの追加実分母後の各次次数セルの実錐単体。 -/
def dgVerdierConeNextSimplex (i : Fin m) : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet) _⦋N + 2⦌ :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierBoundaryRefinementSimplex A D (fun i => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.truncatedConeNextBoundary C (τ i)) T i

/-- 次次数の各実充填の零面は、同じ元の図式単体のまま。 -/
lemma dgVerdierConeNextSimplex_face_zero (i : Fin m) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).δ 0 (dgVerdierConeNextSimplex A D P x C τ T i) =
      f.app _ (τ i) := by
  unfold dgVerdierConeNextSimplex
  have hf := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierBoundaryRefinementSimplex_face_zero A D
    (fun i => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.truncatedConeNextBoundary C (τ i)) T i
  refine hf.trans ?_
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.truncatedConeNextBoundary_face_zero, Equiv.apply_symm_apply]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
