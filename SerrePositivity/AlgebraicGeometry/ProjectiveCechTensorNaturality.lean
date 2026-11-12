module

public import SerrePositivity.AlgebraicGeometry.ProjectiveCechTensorBaseChange
public import Mathlib.CategoryTheory.Whiskering

/-!
概要：実際の Čech テンソル底変換の比較を、係数図式の射に自然にする。
方針：純テンソルの各成分を比較し、複体と関手の同型にまとめる。
規約：この複体の比較には平坦性を仮定しない。
使われ方：flat な Čech コホモロジーの底変換と、射の可換性の照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
open scoped TensorProduct ChangeOfRings
universe u
variable {R B : Type u} [CommRing R] [CommRing B] (φ : R →+* B)
variable {ι : Type} [DecidableEq ι] [Fintype ι]
local instance projectiveCechTensorNatExtendAdditive : (ModuleCat.extendScalars φ).Additive :=
  projectiveCechTensorExtendAdditive φ
variable (D E : Finset ι ⥤ ModuleCat.{u} R) (η : D ⟶ E)

/-- Čech 各項のテンソル比較は、任意の係数図式の射に自然。 -/
theorem projectiveCechTensorCochainsIso_naturality (k : ℕ) :
    (ModuleCat.extendScalars φ).map (ModuleCat.ofHom (fullCechCochainsMap η k)) ≫
        (projectiveCechTensorCochainsIso φ E k).hom =
      (projectiveCechTensorCochainsIso φ D k).hom ≫
        ModuleCat.ofHom (fullCechCochainsMap
          (Functor.whiskerRight η (ModuleCat.extendScalars φ)) k) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul b a =>
    change (projectiveCechTensorCochainsIso φ E k).hom
        (b ⊗ₜ[R,φ] (fullCechCochainsMap η k a)) =
      fullCechCochainsMap (Functor.whiskerRight η (ModuleCat.extendScalars φ)) k
        ((projectiveCechTensorCochainsIso φ D k).hom (b ⊗ₜ[R,φ] a))
    rw [projectiveCechTensorCochainsIso_tmul, projectiveCechTensorCochainsIso_tmul]
    funext t
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Čech 複体のテンソル比較は、係数図式の自然変換と可換。 -/
theorem projectiveCechTensorComplexIso_naturality :
    ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℕ)).map
        (fullCechComplexMap η) ≫ (projectiveCechTensorComplexIso φ E).hom =
      (projectiveCechTensorComplexIso φ D).hom ≫
        fullCechComplexMap (Functor.whiskerRight η (ModuleCat.extendScalars φ)) := by
  apply HomologicalComplex.hom_ext
  intro q
  change (ModuleCat.extendScalars φ).map
      (ModuleCat.ofHom (fullCechCochainsMap η (q + 1))) ≫
      (projectiveCechTensorCochainsIso φ E (q + 1)).hom =
    (projectiveCechTensorCochainsIso φ D (q + 1)).hom ≫
      ModuleCat.ofHom (fullCechCochainsMap
        (Functor.whiskerRight η (ModuleCat.extendScalars φ)) (q + 1))
  exact projectiveCechTensorCochainsIso_naturality φ D E η (q + 1)

/-- Čech 複体とテンソル底変換の比較を、係数図式の圏上の自然同型にする。 -/
def projectiveCechTensorComplexNatIso :
    fullCechComplexFunctor (R := R) (ι := ι) ⋙
        (ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℕ) ≅
      (Functor.whiskeringRight (Finset ι) (ModuleCat.{u} R) (ModuleCat.{u} B)).obj
          (ModuleCat.extendScalars φ) ⋙ fullCechComplexFunctor (R := B) (ι := ι) :=
  NatIso.ofComponents (projectiveCechTensorComplexIso φ)
    (fun η ↦ projectiveCechTensorComplexIso_naturality φ _ _ η)

end SerrePositivity.AlgebraicGeometry
