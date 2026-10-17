module
public import SerrePositivity.DifferentialGraded.Derived.ScalarExtension
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Category.ModuleCat.Descent

/-! # underived 係数変更による擬同型保存の条件

係数制限は無条件で exact。係数拡大はホモロジー保存を明示し、
環準同型の flatness をその十分条件として与える。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.ScalarExtension
open CategoryTheory HomologicalComplex
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D] [Small.{u} D]

lemma restriction_quasiIso {K L : Complex A'} (f : K ⟶ L) [QuasiIso f] :
    QuasiIso ((restriction φ).map f) := by
  change QuasiIso (((ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℤ)).map f)
  infer_instance

lemma moduleRestriction_quasiIso {M N : ModuleCategory A' (DGBaseChange φ D)}
    (f : M ⟶ N) (hf : moduleQuasiIso A' (DGBaseChange φ D) f) :
    moduleQuasiIso A D ((moduleRestriction φ D).map f) := by
  intro x
  rw [moduleRestriction_eval]
  have := hf x
  exact restriction_quasiIso φ _

/-- 係数制限は非 flat な環準同型でも主導来加群圏へ降りる。 -/
def derivedRestriction : DerivedModuleCategory A' (DGBaseChange φ D) ⥤
    DerivedModuleCategory A D :=
  moduleDerivedLift A' (DGBaseChange φ D)
    (moduleRestriction φ D ⋙ moduleToDerived A D) (by
      intro M N f hf
      exact moduleToDerived_inverts A D _ (moduleRestriction_quasiIso φ D f hf))

lemma derivedRestriction_fac :
    moduleToDerived A' (DGBaseChange φ D) ⋙ derivedRestriction φ D =
      moduleRestriction φ D ⋙ moduleToDerived A D := moduleDerivedLift_fac _ _ _ _

/-- 一般の擬同型を underived に送る十分条件は exactness。 -/
lemma extension_quasiIso_of_preservesHomology
    [(ModuleCat.extendScalars φ).PreservesHomology]
    {K L : Complex A} (f : K ⟶ L) [QuasiIso f] :
    QuasiIso ((extension φ).map f) := by
  change QuasiIso (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).map f)
  infer_instance

lemma extension_quasiIso_of_flat (hφ : φ.Flat) {K L : Complex A} (f : K ⟶ L)
    [QuasiIso f] : QuasiIso ((extension φ).map f) := by
  have := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hφ
  exact extension_quasiIso_of_preservesHomology φ f

lemma moduleExtension_quasiIso_of_flat (hφ : φ.Flat) {M N : ModuleCategory A D}
    (f : M ⟶ N) (hf : moduleQuasiIso A D f) :
    moduleQuasiIso A' (DGBaseChange φ D) ((moduleExtension φ D).map f) := by
  intro x
  rw [moduleExtension_eval]
  have := hf x
  exact extension_quasiIso_of_flat φ hφ _

/-- flat な場合は解像度の増大射の係数変更も擬同型となる。 -/
lemma derivedExtensionComparison_isIso_of_flat (hφ : φ.Flat)
    {M : ModuleCategory A D} (P : ModuleProjectiveResolution A D M) :
    IsIso (derivedExtensionComparison φ D P) :=
  derivedExtensionComparison_isIso φ D P
    (moduleExtension_quasiIso_of_flat φ D hφ P.π P.quasiIso)

end SerrePositivity.DifferentialGraded.ScalarExtension
