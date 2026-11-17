module

public import SerrePositivity.AlgebraicGeometry.CechIntegerTotalToRowZeroQuasiIso
public import Mathlib.Algebra.Homology.TotalComplexSymmetry
import all SerrePositivity.HomologicalAlgebra.BicomplexColumnQuasiIso
import all SerrePositivity.HomologicalAlgebra.BicomplexProjection

/-!
概要：元の零次列射影の自然性と全射性、正の列の完全性による擬同型性。
方針：既存のtotalFlipIsoと同じ零次行射影の判定を使う。
規約：新しい全複体や対角線消去の証明を作らない。
使われ方：相対の二重Čech比較のもう一方の軸への射影。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
universe u
local notation "up" => ComplexShape.up ℕ
/-- 既存HAと同じ横次数・縦次数の積の符号。使用箇所に限ってインスタンスとする。 -/
def cechIntegerTotalShapeSymmetry : TotalComplexShapeSymmetry up up up where
  symm a b := Nat.add_comm b a
  σ a b := (-1 : ℤˣ) ^ (a * b)
  σ_ε₁ := by
    rintro a _ rfl b
    change (-1 : ℤˣ) ^ (a * b) * 1 = (-1 : ℤˣ)^b * (-1 : ℤˣ)^((a + 1) * b)
    rw [Nat.add_mul, Nat.one_mul, pow_add, mul_one]
    rw [← mul_assoc, mul_comm ((-1 : ℤˣ)^b) ((-1 : ℤˣ)^(a * b)), mul_assoc,
      Int.units_mul_self, mul_one]
  σ_ε₂ := by
    rintro a b _ rfl
    change (-1 : ℤˣ) ^ (a * b) * (-1 : ℤˣ)^a = 1 * (-1 : ℤˣ)^(a * (b + 1))
    rw [Nat.mul_add, Nat.mul_one, pow_add, one_mul]


attribute [local instance] cechIntegerTotalShapeSymmetry

variable {K L : HomologicalComplex₂ (ModuleCat.{u} ℤ) up up}

set_option backward.isDefEq.respectTransparency false in
/-- 元の零次列射影は二重複体の射に自然。 -/
theorem cechIntegerTotalToColumnZero_naturality (f : K ⟶ L) :
    HomologicalComplex₂.total.map f up ≫ SerrePositivity.HomologicalAlgebra.totalToColumnZero L =
      SerrePositivity.HomologicalAlgebra.totalToColumnZero K ≫ f.f 0 := by
  apply HomologicalComplex.Hom.ext
  funext n
  simp only [HomologicalComplex.comp_f]
  apply HomologicalComplex₂.total.hom_ext
  intro a b h
  rw [← Category.assoc, HomologicalComplex₂.ιTotal_map, Category.assoc]
  by_cases ha : a = 0
  · subst a
    have hb : b = n := by simpa using h
    subst b
    simp [SerrePositivity.HomologicalAlgebra.totalToColumnZero,
      SerrePositivity.HomologicalAlgebra.columnZeroApp]
  · simp [SerrePositivity.HomologicalAlgebra.totalToColumnZero,
      SerrePositivity.HomologicalAlgebra.columnZeroApp, ha]

set_option backward.isDefEq.respectTransparency false in
/-- 元の零次列射影の各全次数の成分は全射。 -/
theorem cechIntegerTotalToColumnZero_component_surjective
    (K : HomologicalComplex₂ (ModuleCat.{u} ℤ) up up) (n : ℕ) : Function.Surjective
      ((SerrePositivity.HomologicalAlgebra.totalToColumnZero K).f n).hom := by
  intro x
  refine ⟨(K.ιTotal up 0 n n (by change 0 + n = n; omega)).hom x, ?_⟩
  have hi : K.ιTotal up 0 n n (by change 0 + n = n; omega) ≫
      (SerrePositivity.HomologicalAlgebra.totalToColumnZero K).f n = 𝟙 _ := by
    simp [SerrePositivity.HomologicalAlgebra.totalToColumnZero,
      SerrePositivity.HomologicalAlgebra.columnZeroApp]
  exact congrArg (fun v ↦ v.hom x) hi

set_option backward.isDefEq.respectTransparency false in
/-- 同じtotalFlipIsoの軸上の符号は一で、元の列射影を元の行射影へ送る。 -/
theorem cechIntegerTotalFlip_rowZero (K : HomologicalComplex₂ (ModuleCat.{u} ℤ) up up) :
    (HomologicalComplex₂.totalFlipIso K up).hom ≫ SerrePositivity.HomologicalAlgebra.totalToColumnZero K =
      SerrePositivity.HomologicalAlgebra.totalToRowZero K.flip := by
  apply HomologicalComplex.Hom.ext
  funext n
  simp only [HomologicalComplex.comp_f]
  apply HomologicalComplex₂.total.hom_ext
  intro a b h
  rw [← Category.assoc, HomologicalComplex₂.ιTotal_totalFlipIso_f_hom]
  by_cases hb : b = 0
  · subst b
    have ha : a = n := by simpa using h
    subst a
    simp [SerrePositivity.HomologicalAlgebra.totalToColumnZero,
      SerrePositivity.HomologicalAlgebra.totalToRowZero,
      SerrePositivity.HomologicalAlgebra.columnZeroApp,
      SerrePositivity.HomologicalAlgebra.rowZeroApp, ComplexShape.σ]
    change ((-1 : ℤˣ) ^ (0 * n)) • (𝟙 ((K.X 0).X n)) = 𝟙 _
    simp
  · simp [SerrePositivity.HomologicalAlgebra.totalToColumnZero,
      SerrePositivity.HomologicalAlgebra.totalToRowZero,
      SerrePositivity.HomologicalAlgebra.columnZeroApp,
      SerrePositivity.HomologicalAlgebra.rowZeroApp, hb]

set_option backward.isDefEq.respectTransparency false in
/-- 正の列が完全なら元の同じ零次列射影は擬同型。既存の零次行の判定を使う。 -/
theorem cechIntegerTotalToColumnZero_quasiIso
    (K : HomologicalComplex₂ (ModuleCat.{u} ℤ) up up)
    (hK : ∀ a, 0 < a → (K.X a).Acyclic) :
    QuasiIso (SerrePositivity.HomologicalAlgebra.totalToColumnZero K) := by
  have hq : QuasiIso (SerrePositivity.HomologicalAlgebra.totalToRowZero K.flip) :=
    cechIntegerTotalToRowZero_quasiIso K.flip (fun a b hb ↦ hK b hb a)
  apply (_root_.quasiIso_iff_comp_left (HomologicalComplex₂.totalFlipIso K up).hom _).mp
  rw [cechIntegerTotalFlip_rowZero]
  exact hq

end SerrePositivity.AlgebraicGeometry
