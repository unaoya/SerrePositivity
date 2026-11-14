module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.DiagramHomFamilyEquiv
public import SerrePositivity.DifferentialGraded.Complexes.HomLimits
/-!
概要：図式テンソル–Hom同値の単位における評価。
方針：閉構造の既存成分公式と右単位子の値を各点で使う。
規約：A06の前提計算2/3。既存構成の単位則のみ。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable {A : Type (max u v)} [CommRing A] {J : Type v} [SmallCategory J]
local notation "E" => functorToComplexOfFunctors J (ModuleCat A) (ComplexShape.up ℤ)
/-- 右単位子で戻した図式射の転置は、同じ零次閉コチェインからの単位射。 -/
theorem diagramTensorLinearHomEquiv_unit {R S : J ⥤ Complex A} (f : R ⟶ S) :
    diagramTensorLinearHomEquiv R S (𝟙_ (Complex A)) ((ρ_ R).hom ≫ f) =
      unitFromCycle (linearHomComplex A ((E).obj R) ((E).obj S))
        ⟨Cochain.ofHom ((E).map f), δ_ofHom ((E).map f)⟩ := by
  apply (unitCycleEquiv _).injective
  apply Subtype.ext
  change (cycleFromUnit _ _).val = (cycleFromUnit _ (unitFromCycle _ _)).val
  rw [cycleFromUnit_unitFromCycle]
  apply diagramCochain_ext R S
  intro j
  apply Cochain.ext₀
  intro i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change ((tensorHomEquiv (R.obj j) (𝟙_ (Complex A)) (S.obj j)
    ((ρ_ (R.obj j)).hom ≫ f.app j)).f 0 (1 : A)).v i i (add_zero i) x =
      (f.app j).f i x
  rw [tensorHomEquiv_component]
  simp only [zero_mul, Int.negOnePow_zero, one_smul]
  change (f.app j).f i ((ρ_ (R.obj j)).hom.f i
    (ιTensorObj (R.obj j) (𝟙_ (Complex A)) i 0 i (add_zero i) (x ⊗ₜ[A] (1 : A)))) = _
  rw [rightUnitor_apply]
end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
