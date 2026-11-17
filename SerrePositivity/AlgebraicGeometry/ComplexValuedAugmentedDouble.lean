module

public import SerrePositivity.AlgebraicGeometry.CechIntegerTotalToColumnZeroQuasiIso
public import SerrePositivity.AlgebraicGeometry.CechIntegerLiftTotalFunctor
public import SerrePositivity.HomologicalAlgebra.Cech.Double

/-!
概要：増大単体圏二つの積から複体への図式を、複体値の二重複体にする。
方針：既存の増大余鎖関手を二回使い、零次列の射影へつなぐ。
規約：増大項は次数0に置き、元の全ての係数と微分を保持する。
使われ方：複体値の二重Čechの軸比較（計画C06・C08〜C10）。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits AlgebraicTopology
universe u
local notation "up" => ComplexShape.up ℕ
set_option backward.isDefEq.respectTransparency false

/-- 同じ複体値の二変数図式へ既存の増大余鎖関手を二回適用する。 -/
def complexValuedAugmentedDouble
    (F : AugmentedSimplexCategory × AugmentedSimplexCategory ⥤
      CochainComplex (ModuleCat.{u} ℤ) ℕ) :
    HomologicalComplex₂ (CochainComplex (ModuleCat.{u} ℤ) ℕ) up up :=
  SerrePositivity.Cech.augmentedCochain.obj
    (AugmentedSimplexCategory.equivAugmentedCosimplicialObject.functor.obj
      (Functor.curryObj F ⋙
        AugmentedSimplexCategory.equivAugmentedCosimplicialObject.functor ⋙
          SerrePositivity.Cech.augmentedCochain))

/-- 同じ三重図式の固定した列のtotalは、元の列の増大totalと一致する。 -/
def complexValuedAugmentedDouble_columnIso
    (F : AugmentedSimplexCategory × AugmentedSimplexCategory ⥤
      CochainComplex (ModuleCat.{u} ℤ) ℕ) (i : ℕ) :
    (((cechIntegerLiftTotalFunctor.mapHomologicalComplex up).obj
      (complexValuedAugmentedDouble F)).X i) ≅
    HomologicalComplex₂.total (C := ModuleCat.{u} ℤ)
      (SerrePositivity.Cech.augmentedCochain.obj (SerrePositivity.Cech.col F i)) up := by
  cases i <;> exact Iso.refl _

/-- 同じ三重totalから、元の零次列の増大totalへの射影。 -/
def complexValuedAugmentedDouble_columnZeroProjection
    (F : AugmentedSimplexCategory × AugmentedSimplexCategory ⥤
      CochainComplex (ModuleCat.{u} ℤ) ℕ) :
    HomologicalComplex₂.total (C := ModuleCat.{u} ℤ)
      ((cechIntegerLiftTotalFunctor.mapHomologicalComplex up).obj
        (complexValuedAugmentedDouble F)) up ⟶
    HomologicalComplex₂.total (C := ModuleCat.{u} ℤ)
      (SerrePositivity.Cech.augmentedCochain.obj (SerrePositivity.Cech.col F 0)) up :=
  SerrePositivity.HomologicalAlgebra.totalToColumnZero _ ≫
    (complexValuedAugmentedDouble_columnIso F 0).hom

/-- 正の列の増大totalが完全なら、同じ零次列射影は擬同型である。 -/
theorem complexValuedAugmentedDouble_columnZeroProjection_quasiIso
    (F : AugmentedSimplexCategory × AugmentedSimplexCategory ⥤
      CochainComplex (ModuleCat.{u} ℤ) ℕ)
    (hF : ∀ i, 0 < i → (HomologicalComplex₂.total (C := ModuleCat.{u} ℤ)
      (SerrePositivity.Cech.augmentedCochain.obj (SerrePositivity.Cech.col F i)) up).Acyclic) :
    QuasiIso (complexValuedAugmentedDouble_columnZeroProjection F) := by
  haveI hq := cechIntegerTotalToColumnZero_quasiIso
    ((cechIntegerLiftTotalFunctor.mapHomologicalComplex up).obj
      (complexValuedAugmentedDouble F)) (fun i hi n ↦
        (hF i hi n).of_iso (complexValuedAugmentedDouble_columnIso F i).symm)
  dsimp only [complexValuedAugmentedDouble_columnZeroProjection]
  exact quasiIso_comp _ _

end SerrePositivity.AlgebraicGeometry
