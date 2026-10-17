module

public import SerrePositivity.CLMST.IsogenyDescent
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletedBaseChangeTriangle

/-! # Prop 2.4.7：標準射の四角形から実錐全体の比較へ

始域と終域の実導来対象の同型と標準射の四角形を入力し、
完全三角形の第三対象として実錐を比較する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.CLMST
open CategoryTheory CategoryTheory.Pretriangulated DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
variable {R B : Type u} [CommRing R] [CommRing B] (φ : R →+* B) (a : R)
variable {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- 元の加群写像の標準三角形に対する実完備導来底変換。 -/
def prop247_completedModuleTriangle (f : M →ₗ[R] N) : Triangle (ConcreteDerivedCategory B) :=
  let X := boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R M)
  let Y := boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R N)
  let C := moduleMapConeBoundedAbove f
  let u : X ⟶ Y := boundedAboveDerivedSingleFunctor.map (ModuleCat.ofHom f)
  let v : Y ⟶ C := ObjectProperty.homMk (moduleMapConeTriangle R f).mor₂
  let δ : C ⟶ X⟦(1 : ℤ)⟧ := ObjectProperty.homMk
    ((moduleMapConeTriangle R f).mor₃ ≫
      (DerivedCategory.Minus.ι.commShiftIso (1 : ℤ)).inv.app X)
  completedBaseChangeTriangle φ a u v δ

/-- 元の実加群写像の錐は、完備導来底変換後も実完全三角形の第三対象となる。 -/
theorem prop247_completedModuleTriangle_distinguished (f : M →ₗ[R] N) :
    prop247_completedModuleTriangle φ a f ∈ distTriang (ConcreteDerivedCategory B) := by
  apply completedBaseChangeTriangle_distinguished
  simp only [ObjectProperty.homMk_hom, Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]
  change moduleMapConeTriangle R f ∈ distTriang _
  exact moduleMapConeTriangle_distinguished R f

/-- 標準射の始域・終域の比較を、実完備底変換錐と実加群写像錐の比較へ延長する。 -/
def prop247_completedModuleConeIso
    {L P : Type u} [AddCommGroup L] [Module B L] [AddCommGroup P] [Module B P]
    (f : M →ₗ[R] N) (α : L →ₗ[B] P)
    (eM : (derivedComplexCompletionFunctor B (φ a)).obj
      ((boundedAboveDerivedBaseChange φ).obj
        (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R M))).obj ≅
      (moduleObjectFunctor B).obj (ModuleCat.of B L))
    (eN : (derivedComplexCompletionFunctor B (φ a)).obj
      ((boundedAboveDerivedBaseChange φ).obj
        (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R N))).obj ≅
      (moduleObjectFunctor B).obj (ModuleCat.of B P))
    (hsq : (derivedComplexCompletionFunctor B (φ a)).map
        ((boundedAboveDerivedBaseChange φ).map
          (boundedAboveDerivedSingleFunctor.map (ModuleCat.ofHom f))).hom ≫ eN.hom =
      eM.hom ≫ (moduleObjectFunctor B).map (ModuleCat.ofHom α)) :
    (derivedComplexCompletionFunctor B (φ a)).obj
      ((boundedAboveDerivedBaseChange φ).obj (moduleMapConeBoundedAbove f)).obj ≅
        moduleMapCone B α :=
  Triangle.π₃.mapIso (isoTriangleOfIso₁₂ _ _
    (prop247_completedModuleTriangle_distinguished φ a f)
    (moduleMapConeTriangle_distinguished B α) eM eN hsq)

/-- 第三対象の比較は、元の実三角形の標準の右包含を保つ。 -/
theorem prop247_completedModuleConeIso_inclusion
    {L P : Type u} [AddCommGroup L] [Module B L] [AddCommGroup P] [Module B P]
    (f : M →ₗ[R] N) (α : L →ₗ[B] P)
    (eM : (derivedComplexCompletionFunctor B (φ a)).obj
      ((boundedAboveDerivedBaseChange φ).obj
        (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R M))).obj ≅
      (moduleObjectFunctor B).obj (ModuleCat.of B L))
    (eN : (derivedComplexCompletionFunctor B (φ a)).obj
      ((boundedAboveDerivedBaseChange φ).obj
        (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R N))).obj ≅
      (moduleObjectFunctor B).obj (ModuleCat.of B P))
    (hsq : (derivedComplexCompletionFunctor B (φ a)).map
        ((boundedAboveDerivedBaseChange φ).map
          (boundedAboveDerivedSingleFunctor.map (ModuleCat.ofHom f))).hom ≫ eN.hom =
      eM.hom ≫ (moduleObjectFunctor B).map (ModuleCat.ofHom α)) :
    (prop247_completedModuleTriangle φ a f).mor₂ ≫
        (prop247_completedModuleConeIso φ a f α eM eN hsq).hom =
      eN.hom ≫ (moduleMapConeTriangle B α).mor₂ := by
  exact (isoTriangleOfIso₁₂ _ _
    (prop247_completedModuleTriangle_distinguished φ a f)
    (moduleMapConeTriangle_distinguished B α) eM eN hsq).hom.comm₂

end SerrePositivity.CLMST
