module
public import SerrePositivity.DifferentialGraded.Endomorphism.ScalarDerivedProjectiveComparison

/-! # 既存の導来係数拡大の主Perfへの制限 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D] [Small.{u} D]

lemma scalarDerivedExtension_obj_perfect (S : Set D) (X : PerfectModuleCategoryOver A D S) :
    modulePerfectOver A' (ScalarExtension.DGBaseChange φ D) (scalarPerfectGenerators φ D S)
      ((ScalarExtension.derivedExtension φ D).obj X.obj) := by
  let R := moduleCanonicalProjectiveResolution A D X.obj.as.obj
  let e : (moduleToDerived A D).obj R.obj ≅ X.obj := moduleDerivedIso A D R.π R.quasiIso
  have hR := (modulePerfectOver A D S).prop_of_iso e.symm X.property
  exact (modulePerfectOver A' (ScalarExtension.DGBaseChange φ D)
    (scalarPerfectGenerators φ D S)).prop_of_iso
      ((scalarDerivedProjectiveComputation φ D R.obj R.projective).symm ≪≫
        (ScalarExtension.derivedExtension φ D).mapIso e)
      (scalarModuleExtension_perfect_perfect φ D R.projective hR)

/-- 受入済みの主導来係数拡大を、指定集合から生成する主Perfへ制限する。 -/
def perfectScalarDerivedExtension (S : Set D) :
    PerfectModuleCategoryOver A D S ⥤
      PerfectModuleCategoryOver A' (ScalarExtension.DGBaseChange φ D)
        (scalarPerfectGenerators φ D S) :=
  (modulePerfectOver A' (ScalarExtension.DGBaseChange φ D) (scalarPerfectGenerators φ D S)).lift
    (perfectModuleInclusion A D S ⋙ ScalarExtension.derivedExtension φ D)
    (scalarDerivedExtension_obj_perfect φ D S)

def perfectScalarDerivedExtensionInclusionIso (S : Set D) :
    perfectScalarDerivedExtension φ D S ⋙
        perfectModuleInclusion A' (ScalarExtension.DGBaseChange φ D)
          (scalarPerfectGenerators φ D S) ≅
      perfectModuleInclusion A D S ⋙ ScalarExtension.derivedExtension φ D :=
  ObjectProperty.liftCompιIso _ _ _

end SerrePositivity.DifferentialGraded
