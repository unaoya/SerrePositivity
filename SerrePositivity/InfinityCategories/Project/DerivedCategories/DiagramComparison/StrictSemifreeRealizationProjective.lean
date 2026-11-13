module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.ProjectiveComplexEvaluationComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictSemifreeRealizationFamily
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictSemifreeRealizationCocone
import all SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictSemifreeRealizationFamily

/-!
概要：元の全実現関手を射影的複体の部分圏へ持ち上げる。
方針：3b-1の定数一点加群の実現の射影性と、元の係数図式の等式を使う。
規約：対象だけでなく元の自然変換の直和全複体への像を保つ。
使われ方：3b-3 R6、実現の全族の評価比較と指定余錐の接続。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison

variable (A : Type u) [CommRing A]

local instance : (projectiveRingComplexInclusion A).onClosed.Full := by
  dsimp only [projectiveRingComplexInclusion]
  infer_instance

local instance : (projectiveRingComplexInclusion A).onClosed.Faithful := by
  dsimp only [projectiveRingComplexInclusion]
  infer_instance

/-- 元の半自由図式を、一点半自由加群の同じstrict図式として読む。 -/
def strictSemifreePointDiagram (F : StrictSemifreeDiagram A SimplexCategoryᵒᵖ) :=
  F ⋙ (semifreePointConstant A).onClosed

/-- 3b-1の係数図式は、元のstrict複体図式と同じ鎖写像を持つ。 -/
lemma strictSemifreePointDiagram_coefficients
    (F : StrictSemifreeDiagram A SimplexCategoryᵒᵖ) :
    smallStrictBarCoefficientDiagram A
        (pointSemifreeUnderlyingDiagram A (strictSemifreePointDiagram A F)) =
      (strictSemifreeUnderlyingComplex A .simplicial).obj F := by
  refine CategoryTheory.Functor.ext ?_ ?_
  · intro j
    rfl
  intro j k f
  change (complexClosedHomEquiv A _ _)
    (ForgetEnrichment.homOf (Complex A)
      ((ForgetEnrichment.homTo (Complex A)
        ((semifreeComplexInclusion A).onClosed.map (F.map f)) ≫
          (ringConstantHomIso A _ _).inv) ≫ (ringConstantHomIso A _ _).hom)) = _
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, ForgetEnrichment.homOf_homTo]
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

/-- 元の直和全複体の定数一点加群は、計算済みの射影性を持つ。 -/
lemma strictSemifreeRealizationComplex_projective
    (F : StrictSemifreeDiagram A SimplexCategoryᵒᵖ) :
    projectiveRingComplexProperty A ((strictSemifreeRealizationComplex A).obj F) := by
  have h := strictSimplicialRealization_projective A
    (pointSemifreeUnderlyingDiagram A (strictSemifreePointDiagram A F))
    (pointSemifreeUnderlyingDiagram_projective A (strictSemifreePointDiagram A F))
  change moduleHomotopicallyProjective A PUnit.{1}
    (ForgetEnrichment.of (Complex A)
      (ringModule A ((directSumTotalFunctor A).obj
        ((strictSemifreeUnderlyingComplex A .simplicial).obj F))))
  simpa only [strictSimplicialRealizationModule, strictSemifreePointDiagram_coefficients] using h

/-- 元の実現関手を、同じ射影的複体の閉零圏へ持ち上げた通常関手。 -/
def strictSemifreeRealizationProjective :
    StrictSemifreeDiagram A SimplexCategoryᵒᵖ ⥤ ClosedCategory A (ProjectiveRingComplex A) where
  obj F := ForgetEnrichment.of (Complex A)
    ⟨(strictSemifreeRealizationComplex A).obj F, strictSemifreeRealizationComplex_projective A F⟩
  map f := (projectiveRingComplexInclusion A).onClosed.preimage
    ((complexClosedPresentation A).map ((strictSemifreeRealizationComplex A).map f))
  map_id F := by
    apply (projectiveRingComplexInclusion A).onClosed.map_injective
    rw [Functor.map_preimage]
    rw [(strictSemifreeRealizationComplex A).map_id,
      (projectiveRingComplexInclusion A).onClosed.map_id]
    simpa only [projectiveRingComplexInclusion] using!
      (complexClosedPresentation A).map_id ((strictSemifreeRealizationComplex A).obj F)
  map_comp f g := by
    apply (projectiveRingComplexInclusion A).onClosed.map_injective
    simp only [Functor.map_comp, Functor.map_preimage]

/-- 射影的持ち上げを通常複体へ戻すと、元の実現関手の射を含めて一致する。 -/
lemma strictSemifreeRealizationProjective_underlying :
    strictSemifreeRealizationProjective A ⋙ projectiveRingUnderlyingComplex A =
      strictSemifreeRealizationComplex A := by
  refine CategoryTheory.Functor.ext ?_ ?_
  · intro F
    rfl
  intro F G f
  simp only [Functor.comp_map, projectiveRingUnderlyingComplex,
    strictSemifreeRealizationProjective, Functor.map_preimage,
    eqToHom_refl, Category.id_comp, Category.comp_id]
  change (complexClosedHomEquiv A _ _)
    ((complexClosedHomEquiv A _ _).symm ((strictSemifreeRealizationComplex A).map f)) = _
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using
    (Equiv.apply_symm_apply (complexClosedHomEquiv A _ _)
      ((strictSemifreeRealizationComplex A).map f))

/-- 3b-1の同じ射影的模型を経由する実現の、全パラメーター族。 -/
def strictSemifreeProjectiveRealizationFamily :
    nerve (StrictSemifreeDiagram A SimplexCategoryᵒᵖ) ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A :=
  nerveMap (strictSemifreeRealizationProjective A) ≫
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveInclusion A (ProjectiveRingComplex A) ≫
      SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
        (projectiveRingComplexConstant A) ≫ (projectivePointEquivalence A).hom

/-- 元の実現関手の全族と、同じ射影的模型への全族の比較。 -/
def strictSemifreeRealizationFamily_projectiveIso :
    SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (strictSemifreeRealizationFamily A) (strictSemifreeProjectiveRealizationFamily A) := by
  have e := (complexDerivedEvaluation_projectiveRingIso A).precomp
    (nerveMap (strictSemifreeRealizationProjective A))
  have hn : nerveMap (strictSemifreeRealizationProjective A) ≫
      nerveMap (projectiveRingUnderlyingComplex A) =
        nerveMap (strictSemifreeRealizationComplex A) := by
    change nerveMap (strictSemifreeRealizationProjective A ⋙ projectiveRingUnderlyingComplex A) = _
    rw [strictSemifreeRealizationProjective_underlying]
  simpa only [strictSemifreeRealizationFamily, strictSemifreeProjectiveRealizationFamily,
    ← Category.assoc, hn] using! e

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
