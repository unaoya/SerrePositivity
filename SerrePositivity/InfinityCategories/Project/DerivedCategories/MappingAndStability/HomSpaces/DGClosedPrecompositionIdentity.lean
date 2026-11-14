module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.DGComposition.DGClosedPrecompositionNaturality

/-! # 恒等閉射による Hom と実 pinched 前合成の恒等則

概要：恒等閉射による斉次前合成と Hom 鎖写像は、元の恒等そのもの。
方針：閉零射の単位評価と斉次合成の右単位則を使う。
規約：全整数次数で厳密に成立。使われ方：共通分母細分の恒等則。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]

omit [Small.{u} D] in
/-- 恒等閉射の斉次前合成は元の斉次元。 -/
lemma dgGradedPrecompose_id {x y : D} (k : ℤ) (a : _root_.SerrePositivity.DifferentialGraded.GradedHom A x y k) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose A D k a (𝟙 (ForgetEnrichment.of (Complex A) x)) = a := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.closedHom_id]
  exact _root_.SerrePositivity.DifferentialGraded.compose_unit A a

/-- 恒等閉射の前合成鎖写像は元の Hom 複体の恒等。 -/
lemma dgClosedPrecomposition_id {x y : D} :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition A D (y := y) (𝟙 (ForgetEnrichment.of (Complex A) x)) =
      𝟙 (_root_.SerrePositivity.DifferentialGraded.homObject A D x y) := by
  apply HomologicalComplex.Hom.ext
  funext k
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition A D (y := y) (𝟙 _)).f k a = a
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition_f, dgGradedPrecompose_id]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
