module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Actions.DGModuleSubcategoryYonedaShift
public import SerrePositivity.DifferentialGraded.Module.Hom.ConeComparison
public import SerrePositivity.DifferentialGraded.Module.ConeConstruction
public import SerrePositivity.DifferentialGraded.Functor.ModuleShift
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence
/-!
概要：選んだ実加群部分圏の Yoneda と cone 同型。
方針：元の包含と次数 −1 成分から比較を作り全評価で反映する。
規約：同じ代表集合と全 Hom を保持する。
使われ方：代表系の前三角性に必要な実 cone の表現。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
section
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
    (S : Set (ModuleCategory R D))

def dgModuleSubcategoryUnderlyingMap {M N : {M // S M}}
    (f : ForgetEnrichment.of (Complex R) M ⟶ ForgetEnrichment.of (Complex R) N) :
    M.val ⟶ N.val :=
  ForgetEnrichment.homOf (Complex R) (ForgetEnrichment.homTo (Complex R) f)

variable (hS : ∀ M N, S M → S N → ∀ f : M ⟶ N, S (moduleCone R D f))
    {M N : {M // S M}}
    (f : ForgetEnrichment.of (Complex R) M ⟶ ForgetEnrichment.of (Complex R) N)

def dgModuleSubcategoryConeObject : {M // S M} :=
  ⟨moduleCone R D (dgModuleSubcategoryUnderlyingMap R D S f),
    hS M.val N.val M.property N.property (dgModuleSubcategoryUnderlyingMap R D S f)⟩

def dgModuleSubcategoryConeInr :
    ForgetEnrichment.of (Complex R) N ⟶
      ForgetEnrichment.of (Complex R) (dgModuleSubcategoryConeObject R D S hS f) :=
  ForgetEnrichment.homOf (Complex R) (ForgetEnrichment.homTo (Complex R)
    (moduleConeInr R D (dgModuleSubcategoryUnderlyingMap R D S f)))

def dgModuleSubcategoryConeInl :
    GradedHom R M (dgModuleSubcategoryConeObject R D S hS f) (-1) :=
  moduleConeInlElement R D (dgModuleSubcategoryUnderlyingMap R D S f)

lemma dgModuleSubcategoryConeInl_d :
    (M ⟶[Complex R] dgModuleSubcategoryConeObject R D S hS f).d (-1) 0
        (dgModuleSubcategoryConeInl R D S hS f) =
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R)
        (f ≫ dgModuleSubcategoryConeInr R D S hS f))).val := by
  exact moduleConeInlElement_d R D (dgModuleSubcategoryUnderlyingMap R D S f)


variable [Small.{u} {M // S M}]

def dgModuleSubcategoryYonedaConeInl :
    (moduleHom R {M // S M} (representable R M)
      (representable R (dgModuleSubcategoryConeObject R D S hS f))).X (-1) :=
  (yonedaHom R {M // S M} M (dgModuleSubcategoryConeObject R D S hS f)).f (-1)
    (dgModuleSubcategoryConeInl R D S hS f)

lemma dgModuleSubcategoryYonedaConeInl_d :
    (moduleHom R {M // S M} (representable R M)
      (representable R (dgModuleSubcategoryConeObject R D S hS f))).d (-1) 0
        (dgModuleSubcategoryYonedaConeInl R D S hS f) =
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R)
        ((dgYoneda R {M // S M}).onClosed.map f ≫
          (dgYoneda R {M // S M}).onClosed.map
            (dgModuleSubcategoryConeInr R D S hS f)))).val := by
  let Y := dgYoneda R {M // S M}
  have hd := congrArg (fun k ↦ k (dgModuleSubcategoryConeInl R D S hS f))
    ((Y.map M (dgModuleSubcategoryConeObject R D S hS f)).comm (-1) 0)
  change (moduleHom R {M // S M} _ _).d (-1) 0
      (dgModuleSubcategoryYonedaConeInl R D S hS f) =
    (Y.map _ _).f 0 ((M ⟶[Complex R] dgModuleSubcategoryConeObject R D S hS f).d (-1) 0
      (dgModuleSubcategoryConeInl R D S hS f)) at hd
  rw [dgModuleSubcategoryConeInl_d] at hd
  rw [← Y.onClosed.map_comp]
  change _ = (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R)
    (f ≫ dgModuleSubcategoryConeInr R D S hS f) ≫ Y.map _ _)).val
  rw [cycleFromUnit_postcomp]
  exact hd

def dgModuleSubcategoryYonedaConeComparison :
    moduleCone R {M // S M} ((dgYoneda R {M // S M}).onClosed.map f) ⟶
      ForgetEnrichment.of (Complex R)
        (representable R (dgModuleSubcategoryConeObject R D S hS f)) :=
  moduleConeDescOfBoundary R {M // S M} ((dgYoneda R {M // S M}).onClosed.map f)
    (dgModuleSubcategoryYonedaConeInl R D S hS f)
    ((dgYoneda R {M // S M}).onClosed.map (dgModuleSubcategoryConeInr R D S hS f))
    (dgModuleSubcategoryYonedaConeInl_d R D S hS f)



lemma dgYonedaEvaluation_closed_map (A : Type u) [CommRing A] (C : Type w)
    [DGCategory A C] [Small.{u} C] (T : C) {X Y : ClosedCategory A C} (g : X ⟶ Y) :
    (moduleEvaluation A C T).map ((dgYoneda A C).onClosed.map g) =
      ((leftRepresentable A T).toComplexFunctor A).map g := by
  change (closedToComplex A).map (ForgetEnrichment.homOf (Complex A)
      ((ForgetEnrichment.homTo (Complex A) g ≫ yonedaHom A C X Y) ≫
        moduleHomπ A C (representable A X) (representable A Y) T)) =
    (closedToComplex A).map (ForgetEnrichment.homOf (Complex A)
      (ForgetEnrichment.homTo (Complex A) g ≫ (leftRepresentable A T).map X Y))
  rw [Category.assoc, yonedaHom_π, endomorphismYonedaApp]

lemma dgModuleSubcategoryYonedaConeInl_evaluation (T : {M // S M}) :
    (moduleHomπ R {M // S M} (representable R M)
      (representable R (dgModuleSubcategoryConeObject R D S hS f)) T).f (-1)
        (dgModuleSubcategoryYonedaConeInl R D S hS f) =
      DGFunctor.moduleConeImageInl R D
        (leftRepresentable R (ForgetEnrichment.to (Complex R) T.val))
        (dgModuleSubcategoryUnderlyingMap R D S f) := by
  change ((yonedaHom R {M // S M} M (dgModuleSubcategoryConeObject R D S hS f) ≫
      moduleHomπ R {M // S M} _ _ T).f (-1)
        (dgModuleSubcategoryConeInl R D S hS f)) = _
  rw [yonedaHom_π, endomorphismYonedaApp]
  rfl

lemma dgModuleSubcategoryYoneda_closed_evaluation {X Y : {M // S M}}
    (g : ForgetEnrichment.of (Complex R) X ⟶ ForgetEnrichment.of (Complex R) Y)
    (T : {M // S M}) :
    (moduleEvaluation R {M // S M} T).map ((dgYoneda R {M // S M}).onClosed.map g) =
      ((leftRepresentable R (ForgetEnrichment.to (Complex R) T.val)).toComplexFunctor R).map
        (dgModuleSubcategoryUnderlyingMap R D S g) := by
  calc
    _ = ((leftRepresentable R T).toComplexFunctor R).map g :=
      dgYonedaEvaluation_closed_map R {M // S M} T g
    _ = _ := rfl

lemma dgModuleSubcategoryYonedaConeInr_evaluation (T : {M // S M}) :
    (moduleEvaluation R {M // S M} T).map
      ((dgYoneda R {M // S M}).onClosed.map (dgModuleSubcategoryConeInr R D S hS f)) =
        ((leftRepresentable R (ForgetEnrichment.to (Complex R) T.val)).toComplexFunctor R).map
          (moduleConeInr R D (dgModuleSubcategoryUnderlyingMap R D S f)) :=
  dgModuleSubcategoryYoneda_closed_evaluation R D S (dgModuleSubcategoryConeInr R D S hS f) T

open CochainComplex HomComplex

lemma complexConeDesc_isIso_of_eq {X Y K : Complex R} {a b : X ⟶ Y}
    {α α' : Cochain X K (-1)} {β β' : Y ⟶ K}
    {hδ : δ (-1) 0 α = Cochain.ofHom (a ≫ β)}
    {hδ' : δ (-1) 0 α' = Cochain.ofHom (b ≫ β')}
    (ha : a = b) (hα : α = α') (hβ : β = β')
    (h : IsIso (mappingCone.desc b α' β' hδ')) :
    IsIso (mappingCone.desc a α β hδ) := by
  subst b
  subst α'
  subst β'
  exact h

lemma dgModuleSubcategoryYonedaConeComparison_isIso :
    IsIso (dgModuleSubcategoryYonedaConeComparison R D S hS f) := by
  apply moduleIsIso_of_evaluations R {M // S M}
  intro T
  change IsIso ((moduleEvaluation R {M // S M} T).map
    (moduleConeDescOfBoundary R {M // S M} _ _ _ _))
  rw [moduleConeDescOfBoundary_eval]
  change IsIso (CochainComplex.mappingCone.desc _
    ((moduleHomπ R {M // S M} (representable R M)
      (representable R (dgModuleSubcategoryConeObject R D S hS f)) T).f (-1)
        (dgModuleSubcategoryYonedaConeInl R D S hS f)) _ _)
  exact complexConeDesc_isIso_of_eq R
    (dgModuleSubcategoryYoneda_closed_evaluation R D S f T)
    (dgModuleSubcategoryYonedaConeInl_evaluation R D S hS f T)
    (dgModuleSubcategoryYonedaConeInr_evaluation R D S hS f T)
    (DGFunctor.moduleConeImageComparison_isIso R D
      (leftRepresentable R (ForgetEnrichment.to (Complex R) T.val))
      (dgModuleSubcategoryUnderlyingMap R D S f))

def dgModuleSubcategoryYonedaConeIso :
    moduleCone R {M // S M} ((dgYoneda R {M // S M}).onClosed.map f) ≅
      ForgetEnrichment.of (Complex R)
        (representable R (dgModuleSubcategoryConeObject R D S hS f)) := by
  let := dgModuleSubcategoryYonedaConeComparison_isIso R D S hS f
  exact asIso (dgModuleSubcategoryYonedaConeComparison R D S hS f)

end

end SerrePositivity.InfinityCategories.Project.DerivedCategories
