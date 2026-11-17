module

public import SerrePositivity.AlgebraicGeometry.CechConstantPositiveDoubleMap

/-!
概要：同じ正次数の商の射の単位・合成・零を保つ。
方針：外零次では同じ零複体、正次数では元の射を照合する。
規約：元の正次数の商の構成を変えない。
使われ方：同じ基底列の短複体への係数移送。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
universe u v
variable {R : Type v} [CommRing R]
variable {A B C : CochainComplex (ModuleCat.{u} R) ℕ}

/-- 同じ正次数の商の射は単位を保つ。 -/
theorem cechConstantPositiveDoubleMap_id (A : CochainComplex (ModuleCat.{u} R) ℕ) :
    cechConstantPositiveDoubleMap (𝟙 A) = 𝟙 (cechConstantPositiveDouble A) := by
  ext n b x
  cases n <;> rfl

/-- 同じ正次数の商の射は合成を保つ。 -/
theorem cechConstantPositiveDoubleMap_comp (f : A ⟶ B) (g : B ⟶ C) :
    cechConstantPositiveDoubleMap (f ≫ g) =
      cechConstantPositiveDoubleMap f ≫ cechConstantPositiveDoubleMap g := by
  ext n b x
  cases n <;> rfl

/-- 同じ正次数の商の射は零を保つ。 -/
theorem cechConstantPositiveDoubleMap_zero (A B : CochainComplex (ModuleCat.{u} R) ℕ) :
    cechConstantPositiveDoubleMap (0 : A ⟶ B) = 0 := by
  apply HomologicalComplex.Hom.ext
  funext n
  cases n with
  | zero =>
    have h : IsZero (HomologicalComplex.zero : CochainComplex (ModuleCat.{u} R) ℕ) :=
      HomologicalComplex.isZero_zero
    exact h.eq_of_src _ _
  | succ n => rfl

/-- 元の複体を同じ定数列の正次数の商へ送る関手。 -/
def cechConstantPositiveDoubleFunctor : CochainComplex (ModuleCat.{u} R) ℕ ⥤
    CochainComplex (CochainComplex (ModuleCat.{u} R) ℕ) ℕ where
  obj := cechConstantPositiveDouble
  map := cechConstantPositiveDoubleMap
  map_id := cechConstantPositiveDoubleMap_id
  map_comp := cechConstantPositiveDoubleMap_comp

instance cechConstantPositiveDoubleFunctor_preservesZeroMorphisms :
    (cechConstantPositiveDoubleFunctor : CochainComplex (ModuleCat.{u} R) ℕ ⥤
      CochainComplex (CochainComplex (ModuleCat.{u} R) ℕ) ℕ).PreservesZeroMorphisms where
  map_zero A B := cechConstantPositiveDoubleMap_zero A B

end SerrePositivity.AlgebraicGeometry
