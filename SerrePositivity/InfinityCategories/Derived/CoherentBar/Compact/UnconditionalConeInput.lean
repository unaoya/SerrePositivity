module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.NativeEvaluationPreservation
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.EvaluationGeneratorClosure
public import SerrePositivity.InfinityCategories.Derived.KappaCovers.UnconditionalCovers
/-!
概要：正則非可算 κ の実 cone 入力を、元の閉射影的代表系で供給する。
方針：全 native 評価保存を七入力の一般判定へ渡し、無条件 covers と組み立てる。
規約：κ-compact 性は F2 の native 定義であり、評価保存・比較・橋を追加仮定に残さない。
使われ方：D-8 の DGKappaConeInput の実例と K-B への引き渡し。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (κ : Cardinal.{u}) [Fact κ.IsRegular] (hκ : Cardinal.aleph0 < κ)

lemma dgBarCompactRepresentableShift_isKappaCompact (x : D) (s : ℤ) :
    dgModuleKappaCompact R D κ ((ForgetEnrichment.of (Complex R) (representable R x))⟦s⟧) :=
  dgBarCompactRepresentableShift_of_evaluation R D
    (dgBarCompactEvaluation_preserves R D κ) x s

include hκ

lemma dgBarCompactSphereFree_isKappaCompact (i : DGKappaSphereFreeIndex D κ) :
    dgModuleKappaCompact R D κ (dgKappaSphereFreeModule R D i) :=
  dgBarCompactSphereFree_of_evaluation R D (dgBarCompactEvaluation_preserves R D κ) hκ i

lemma dgBarCompactClosedProjective_isKappaCompact (M : ModuleCategory R D)
    (hM : dgKappaClosedProjectiveObjects R D κ M) : dgModuleKappaCompact R D κ M :=
  dgBarCompactClosedProjective_of_evaluation R D (dgBarCompactEvaluation_preserves R D κ) hκ M hM

/-- D-8：元の実代表系による、追加の比較仮定を持たない K-7 cone 入力。 -/
def dgKappaConeInput_unconditional : DGKappaConeInput R D κ :=
  dgBarCompactConeInputOfEvaluationPreservation R D (dgBarCompactEvaluation_preserves R D κ) hκ
    (dgKappaCone_covers_unconditional R D κ hκ)

end SerrePositivity.InfinityCategories
