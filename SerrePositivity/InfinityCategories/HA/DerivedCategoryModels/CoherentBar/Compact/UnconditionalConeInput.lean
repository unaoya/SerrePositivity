module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.NativeEvaluationPreservation
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.EvaluationGeneratorClosure
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.UnconditionalCovers
/-!
概要：正則非可算 κ の実 cone 入力を、元の閉射影的代表系で供給する。
方針：全 native 評価保存を七入力の一般判定へ渡し、無条件 covers と組み立てる。
規約：κ-compact 性は F2 の native 定義であり、評価保存・比較・橋を追加仮定に残さない。
使われ方：D-8 の DGKappaConeInput の実例と K-B への引き渡し。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
open CategoryTheory DifferentialGraded SSet
open _root_.SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  (κ : Cardinal.{u}) [Fact κ.IsRegular] (hκ : Cardinal.aleph0 < κ)

lemma dgBarCompactRepresentableShift_isKappaCompact (x : D) (s : ℤ) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKappaCompact R D κ ((ForgetEnrichment.of (Complex R) (representable R x))⟦s⟧) :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactRepresentableShift_of_evaluation R D
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluation_preserves R D κ) x s

include hκ

lemma dgBarCompactSphereFree_isKappaCompact (i : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaSphereFreeIndex D κ) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKappaCompact R D κ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereFreeModule R D i) :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactSphereFree_of_evaluation R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluation_preserves R D κ) hκ i

lemma dgBarCompactClosedProjective_isKappaCompact (M : _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D)
    (hM : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveObjects R D κ M) : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKappaCompact R D κ M :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactClosedProjective_of_evaluation R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluation_preserves R D κ) hκ M hM

/-- D-8：元の実代表系による、追加の比較仮定を持たない K-7 cone 入力。 -/
def dgKappaConeInput_unconditional : DGKappaConeInput R D κ :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactConeInputOfEvaluationPreservation R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluation_preserves R D κ) hκ
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaCone_covers_unconditional R D κ hκ)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
