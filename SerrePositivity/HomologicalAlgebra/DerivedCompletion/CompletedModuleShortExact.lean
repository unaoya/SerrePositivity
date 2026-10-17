module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletedBaseChangeTriangle
public import SerrePositivity.HomologicalAlgebra.BoundedAboveDerivedModule
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE

/-! # 加群の短完全列の実完備導来底変換

元の加群の全射・単射を完備化後にも仮定せず、実完全三角形を使う。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Pretriangulated
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R B : Type u} [CommRing R] [CommRing B] (φ : R →+* B) (a : R)

/-- 元の加群の短完全列から、実完備導来底変換の三角形を作る。 -/
def completedModuleShortExactTriangle (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact) :
    Triangle (ConcreteDerivedCategory B) :=
  let T := DerivedCategory.triangleOfSES
    (hS.map_of_exact (CochainComplex.singleFunctor (ModuleCat R) 0))
  let X := boundedAboveDerivedSingleFunctor.obj S.X₁
  let Y := boundedAboveDerivedSingleFunctor.obj S.X₂
  let Z := boundedAboveDerivedSingleFunctor.obj S.X₃
  let f : X ⟶ Y := ObjectProperty.homMk T.mor₁
  let g : Y ⟶ Z := ObjectProperty.homMk T.mor₂
  let δ : Z ⟶ X⟦(1 : ℤ)⟧ := ObjectProperty.homMk
    (T.mor₃ ≫ (DerivedCategory.Minus.ι.commShiftIso (1 : ℤ)).inv.app X)
  completedBaseChangeTriangle φ a f g δ

/-- 短完全列の三項の実完備底変換は完全三角形をなす。 -/
theorem completedModuleShortExactTriangle_distinguished
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact) :
    completedModuleShortExactTriangle φ a S hS ∈ distTriang (ConcreteDerivedCategory B) := by
  unfold completedModuleShortExactTriangle
  apply completedBaseChangeTriangle_distinguished
  simp only [ObjectProperty.homMk_hom, Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]
  exact DerivedCategory.triangleOfSES_distinguished
    (hS.map_of_exact (CochainComplex.singleFunctor (ModuleCat R) 0))

/-- 短完全列の両端の完備底変換が離散なら、中央も離散。 -/
theorem completedBaseChangeModule_shortExact_pure
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    (h₁ :
      let Y := (derivedComplexCompletionFunctor B (φ a)).obj
        ((boundedAboveDerivedBaseChange φ).obj (boundedAboveDerivedSingleFunctor.obj S.X₁)).obj
      Y.IsGE 0 ∧ Y.IsLE 0)
    (h₃ :
      let Y := (derivedComplexCompletionFunctor B (φ a)).obj
        ((boundedAboveDerivedBaseChange φ).obj (boundedAboveDerivedSingleFunctor.obj S.X₃)).obj
      Y.IsGE 0 ∧ Y.IsLE 0) :
    let Y := (derivedComplexCompletionFunctor B (φ a)).obj
      ((boundedAboveDerivedBaseChange φ).obj (boundedAboveDerivedSingleFunctor.obj S.X₂)).obj
    Y.IsGE 0 ∧ Y.IsLE 0 := by
  let T := completedModuleShortExactTriangle φ a S hS
  have hd := completedModuleShortExactTriangle_distinguished φ a S hS
  exact ⟨DerivedCategory.TStructure.t.isGE₂ T hd 0 h₁.1 h₃.1,
    DerivedCategory.TStructure.t.isLE₂ T hd 0 h₁.2 h₃.2⟩

end SerrePositivity.DerivedCompletion
