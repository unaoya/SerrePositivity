module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.ProjectiveComplexEvaluationComparison
public import Mathlib.CategoryTheory.Functor.FullyFaithful

/-!
概要：射影的一点加群の係数複体を、同じ射影的複体として表示する。
方針：一点加群の既存の復元等式で射影性を移し、充満包含で全射を持ち上げる。
規約：元の係数と鎖写像を保持する。
使われ方：3b-3 R6 U39の係数移送・照合C3。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.DerivedCategories
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison

variable (A : Type u) [CommRing A]

local instance : (projectiveRingComplexInclusion A).onClosed.Full := by
  dsimp only [projectiveRingComplexInclusion]
  infer_instance

local instance : (projectiveRingComplexInclusion A).onClosed.Faithful := by
  dsimp only [projectiveRingComplexInclusion]
  infer_instance

/-- 元の射影的一点加群の係数複体を読む通常関手。 -/
def projectivePointCoefficientComplex :
    ClosedCategory A (ProjectiveDGModules A PUnit.{1}) ⥤ Complex A :=
  (dgFullSubcategoryInclusion A (RightModule A PUnit.{1})
    (dgModuleProjectiveProperty A PUnit.{1})).onClosed ⋙
      moduleEvaluation A PUnit.{1} PUnit.unit

/-- 係数複体の定数加群は同じ元の加群なので射影的。 -/
lemma projectivePointCoefficient_projective
    (M : ClosedCategory A (ProjectiveDGModules A PUnit.{1})) :
    projectiveRingComplexProperty A ((projectivePointCoefficientComplex A).obj M) := by
  change moduleHomotopicallyProjective A PUnit.{1}
    (ForgetEnrichment.of (Complex A) (ringModule A
      ((ForgetEnrichment.to (Complex A) M).val.obj (Opposite.op PUnit.unit))))
  rw [ringModule_recover]
  exact (ForgetEnrichment.to (Complex A) M).property

/-- 同じ係数複体と鎖写像を射影的複体へ制限する。 -/
def projectivePointRingPresentation :
    ClosedCategory A (ProjectiveDGModules A PUnit.{1}) ⥤
      ClosedCategory A (ProjectiveRingComplex A) where
  obj M := ForgetEnrichment.of (Complex A)
    ⟨(projectivePointCoefficientComplex A).obj M, projectivePointCoefficient_projective A M⟩
  map f := (projectiveRingComplexInclusion A).onClosed.preimage
    ((complexClosedPresentation A).map ((projectivePointCoefficientComplex A).map f))
  map_id M := by
    apply (projectiveRingComplexInclusion A).onClosed.map_injective
    rw [CategoryTheory.Functor.map_preimage]
    rw [(projectivePointCoefficientComplex A).map_id,
      (projectiveRingComplexInclusion A).onClosed.map_id]
    simpa only [projectiveRingComplexInclusion] using!
      (complexClosedPresentation A).map_id ((projectivePointCoefficientComplex A).obj M)
  map_comp f g := by
    apply (projectiveRingComplexInclusion A).onClosed.map_injective
    simp only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_preimage]

/-- U39の係数移送：射影的表示を戻すと元の全係数関手。 -/
lemma projectivePointRingPresentation_underlying :
    projectivePointRingPresentation A ⋙ projectiveRingUnderlyingComplex A =
      projectivePointCoefficientComplex A := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro M N f
  simp only [CategoryTheory.Functor.comp_map, projectiveRingUnderlyingComplex,
    projectivePointRingPresentation, CategoryTheory.Functor.map_preimage,
    eqToHom_refl, Category.id_comp, Category.comp_id]
  change (complexClosedHomEquiv A _ _)
    ((complexClosedHomEquiv A _ _).symm ((projectivePointCoefficientComplex A).map f)) = _
  exact (complexClosedHomEquiv A _ _).apply_symm_apply _

/-- C3の分割：復元した定数一点加群の全係数関手は元と同じ。 -/
lemma projectivePointRingPresentation_constant_coefficients :
    projectivePointRingPresentation A ⋙ (projectiveRingComplexConstant A).onClosed ⋙
      projectivePointCoefficientComplex A = projectivePointCoefficientComplex A := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro M N f
  let g := (projectivePointCoefficientComplex A).map f
  have hm : (projectiveRingComplexInclusion A).onClosed.map
      ((projectivePointRingPresentation A).map f) =
        (complexClosedPresentation A).map g :=
    (projectiveRingComplexInclusion A).onClosed.map_preimage _
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  change (complexClosedHomEquiv A _ _)
    (ForgetEnrichment.homOf (Complex A)
      ((ForgetEnrichment.homTo (Complex A)
        ((projectiveRingComplexInclusion A).onClosed.map
          ((projectivePointRingPresentation A).map f)) ≫
          (ringConstantHomIso A _ _).inv) ≫ (ringConstantHomIso A _ _).hom)) = _
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, ForgetEnrichment.homOf_homTo]
  rw [hm]
  exact (complexClosedHomEquiv A _ _).apply_symm_apply g

local instance : (projectivePointCoefficientComplex A).Full := by
  dsimp only [projectivePointCoefficientComplex]
  infer_instance
local instance : (projectivePointCoefficientComplex A).Faithful := by
  dsimp only [projectivePointCoefficientComplex]
  infer_instance

private lemma functorMap_heq_of_eq {C D : Type (u + 1)}
    [Category.{u} C] [Category.{u} D] {F G : C ⥤ D} (e : F = G)
    {M N : C} (f : M ⟶ N) : HEq (F.map f) (G.map f) := by
  cases e
  rfl

private lemma projectivePointRingPresentation_constant_map
    {M N : ClosedCategory A (ProjectiveDGModules A PUnit.{1})} (f : M ⟶ N) :
    (projectivePointCoefficientComplex A).map
      ((projectivePointRingPresentation A ⋙ (projectiveRingComplexConstant A).onClosed).map f) =
        (projectivePointCoefficientComplex A).map f := by
  exact eq_of_heq (functorMap_heq_of_eq
    (projectivePointRingPresentation_constant_coefficients A) f)

/-- C3の同じ照合の厳密な形：復元等式は全通常関手で成り立つ。 -/
lemma projectivePointRingPresentation_constant :
    projectivePointRingPresentation A ⋙ (projectiveRingComplexConstant A).onClosed =
      𝟭 (ClosedCategory A (ProjectiveDGModules A PUnit.{1})) := by
  refine CategoryTheory.Functor.ext ?_ ?_
  · intro M
    apply congrArg (ForgetEnrichment.of (Complex A))
    apply Subtype.ext
    exact ringModule_recover A (ForgetEnrichment.to (Complex A) M).val
  · intro M N f
    apply (projectivePointCoefficientComplex A).map_injective
    simp only [CategoryTheory.Functor.map_comp, eqToHom_map]
    simpa only [eqToHom_refl, Category.id_comp, Category.comp_id, CategoryTheory.Functor.id_map] using
      projectivePointRingPresentation_constant_map A f

/-- C3：同じ係数複体から復元する一点加群と、元の全射影的加群の自然同型。 -/
def projectivePointRingPresentation_constantIso :
    projectivePointRingPresentation A ⋙ (projectiveRingComplexConstant A).onClosed ≅
      𝟭 (ClosedCategory A (ProjectiveDGModules A PUnit.{1})) :=
  CategoryTheory.Functor.fullyFaithfulCancelRight (projectivePointCoefficientComplex A)
    (eqToIso (projectivePointRingPresentation_constant_coefficients A))

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
