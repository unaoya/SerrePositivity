module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone

/-! # 複体の可算逆系のホモトピー逆極限の具体的モデル

複体の直積上の恒等写像−遷移写像のmapping coneを一段シフトする。
これは実際の加群複体とその導来像であり、完備性を仮定して作る対象ではない。
導来完備化への適用とH⁰の環構造は別工程である。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits CategoryTheory.Category CategoryTheory.Preadditive
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R]
    (K : ℕ → CochainComplex (ModuleCat.{u} R) ℤ) (t : ∀ n, K (n + 1) ⟶ K n)

/-- 逆系の直積上の一段の遷移写像。 -/
def complexTowerShift : piObj K ⟶ piObj K :=
  Pi.lift (fun n ↦ Pi.π K (n + 1) ≫ t n)

/-- 複体の直積上の差分写像。 -/
def complexTowerDifference : piObj K ⟶ piObj K := 𝟙 _ - complexTowerShift R K t

/-- 差分写像の各射影を具体的に計算する。 -/
theorem complexTowerDifference_projection (n : ℕ) :
    complexTowerDifference R K t ≫ Pi.π K n = Pi.π K n - Pi.π K (n + 1) ≫ t n := by
  simp only [complexTowerDifference, complexTowerShift, sub_comp, id_comp, Pi.lift_comp_π]

/-- 可算逆系のホモトピー逆極限の、実際のmapping coneによるモデル。 -/
def complexTowerHomotopyLimit : CochainComplex (ModuleCat.{u} R) ℤ :=
  (CochainComplex.mappingCone (complexTowerDifference R K t))⟦(-1 : ℤ)⟧

/-- 上の複体を標準的な実導来圏へ移した対象。 -/
def complexTowerHomotopyLimitObject : ConcreteDerivedCategory R :=
  DerivedCategory.Q.obj (complexTowerHomotopyLimit R K t)

variable {K} {L : ℕ → CochainComplex (ModuleCat.{u} R) ℤ}

/-- 各段の写像から直積の写像を構成する。 -/
def complexTowerProductMap (g : ∀ n, K n ⟶ L n) : piObj K ⟶ piObj L :=
  Pi.lift (fun n ↦ Pi.π K n ≫ g n)

/-- 直積の写像を射影で計算する。 -/
theorem complexTowerProductMap_projection (g : ∀ n, K n ⟶ L n) (n : ℕ) :
    complexTowerProductMap R g ≫ Pi.π L n = Pi.π K n ≫ g n := by
  simp only [complexTowerProductMap, Pi.lift_comp_π]

/-- 逆系の写像と差分写像は可換する。 -/
theorem complexTowerDifference_naturality (s : ∀ n, L (n + 1) ⟶ L n)
    (g : ∀ n, K n ⟶ L n) (hg : ∀ n, t n ≫ g n = g (n + 1) ≫ s n) :
    complexTowerProductMap R g ≫ complexTowerDifference R L s =
      complexTowerDifference R K t ≫ complexTowerProductMap R g := by
  apply Pi.hom_ext
  intro n
  simp only [assoc, complexTowerDifference_projection, comp_sub,
    complexTowerProductMap_projection]
  rw [← assoc, complexTowerProductMap_projection, assoc, ← hg]
  conv_rhs => rw [← assoc, complexTowerDifference_projection, sub_comp]
  rw [assoc]

end SerrePositivity.DerivedCompletion
