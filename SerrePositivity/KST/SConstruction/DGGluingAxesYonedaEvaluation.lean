module
public import SerrePositivity.KST.SConstruction.DGGluingAxesHomShortExact
public import SerrePositivity.KST.SConstruction.DGGluingAxesYonedaCone
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ComparisonModels.RepresentableEvaluation

/-! # 元の二軸 Yoneda 像の評価短完全列
概要：同じ二射の Yoneda 像を評価した実短複体は、元の全 Hom 短複体と同型になる。
方針：同じ三対象の恒等同型と、元の二つの評価鎖写像の一致を使う。
規約：依存する円錐型の置換を避け、元の短複体を保持。使われ方：実円錐比較の準同型性。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (zc : C) (hc : IsZero (ForgetEnrichment.of (Complex R) zc))
  (zd : D) (hd : IsZero (ForgetEnrichment.of (Complex R) zd))
  (T X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)

/-- 元の二つの Yoneda 射を同じ対象で評価した実短複体。 -/
def dgGluingAxesYonedaEvaluationShortComplex : ShortComplex (Complex R) :=
  ShortComplex.mk
    ((moduleEvaluation R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) T).map
      (dgGluingAxesYonedaRightMap R C D M zc hc X))
    ((moduleEvaluation R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) T).map
      (dgGluingAxesYonedaLeftMap R C D M zd hd X))
    (moduleCompZero_eval R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) _ _
      (dgGluingAxesYoneda_comp_zero R C D M zc hc zd hd X) (Opposite.op T))

/-- 同じ三対象の恒等比較により、元の全 Hom 短複体を回収する。 -/
def dgGluingAxesYonedaEvaluationShortComplexIso :
    dgGluingAxesYonedaEvaluationShortComplex R C D M zc hc zd hd T X ≅
      dgGluingAxesHomShortComplex R C D M zc hc zd hd T X :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by
      have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingYoneda_evaluate R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) T
        (dgGluingRightAxisObject R C D M zc X.right) X
        (dgGluingAxisRightInclusion R C D M zc hc X)
      exact (Category.id_comp _).trans (h.symm.trans (Category.comp_id _).symm))
    (by
      have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingYoneda_evaluate R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) T X
        (dgGluingLeftAxisObject R C D M zd X.left)
        (dgGluingAxisLeftProjection R C D M zd hd X)
      exact (Category.id_comp _).trans (h.symm.trans (Category.comp_id _).symm))

/-- 同じ実 Yoneda 評価短複体は、元の二射を保った短完全列となる。 -/
lemma dgGluingAxesYonedaEvaluationShortComplex_shortExact :
    (dgGluingAxesYonedaEvaluationShortComplex R C D M zc hc zd hd T X).ShortExact :=
  ShortComplex.shortExact_of_iso
    (dgGluingAxesYonedaEvaluationShortComplexIso R C D M zc hc zd hd T X).symm
    (dgGluingAxesHomShortComplex_shortExact R C D M zc hc zd hd T X)

end SerrePositivity.KST.SConstruction
