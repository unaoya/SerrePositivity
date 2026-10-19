module
public import SerrePositivity.InfinityCategories.Derived.DGClosedPrecompositionNaturality

/-! # 恒等閉射による Hom と実 pinched 前合成の恒等則

概要：恒等閉射による斉次前合成と Hom 鎖写像は、元の恒等そのもの。
方針：閉零射の単位評価と斉次合成の右単位則を使う。
規約：全整数次数で厳密に成立。使われ方：共通分母細分の恒等則。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.PinchedHom DGNerve.HomotopyComparison
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

omit [Small.{u} D] in
/-- 恒等閉射の斉次前合成は元の斉次元。 -/
lemma dgGradedPrecompose_id {x y : D} (k : ℤ) (a : GradedHom A x y k) :
    dgGradedPrecompose A D k a (𝟙 (ForgetEnrichment.of (Complex A) x)) = a := by
  rw [dgGradedPrecompose, closedHom_id]
  exact compose_unit A a

/-- 恒等閉射の前合成鎖写像は元の Hom 複体の恒等。 -/
lemma dgClosedPrecomposition_id {x y : D} :
    dgClosedPrecomposition A D (y := y) (𝟙 (ForgetEnrichment.of (Complex A) x)) =
      𝟙 (homObject A D x y) := by
  apply HomologicalComplex.Hom.ext
  funext k
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change (dgClosedPrecomposition A D (y := y) (𝟙 _)).f k a = a
  rw [dgClosedPrecomposition_f, dgGradedPrecompose_id]

end SerrePositivity.InfinityCategories
