module

public import SerrePositivity.AlgebraicGeometry.CechConstantPositiveDoubleFunctor
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
概要：同じ正次数の商への射影の自然性と短完全性。
方針：外零次の零複体と、正次数の元の射・短完全性を使う。
規約：係数環と加群の宇宙を分け、元の複体の仮定を保つ。
使われ方：F8の基底列の短完全列と核の比較。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
universe u v
variable {R : Type v} [CommRing R]
variable {A B : CochainComplex (ModuleCat.{u} R) ℕ}

set_option backward.isDefEq.respectTransparency false in
/-- 元の定数列から同じ正次数の商への射影は、元の射に自然。 -/
theorem cechConstantPositiveDoubleProjection_naturality (f : A ⟶ B) :
    (AlgebraicTopology.alternatingCofaceMapComplex (CochainComplex (ModuleCat.{u} R) ℕ)).map
        ((Functor.const SimplexCategory).map f) ≫ cechConstantPositiveDoubleProjection B =
      cechConstantPositiveDoubleProjection A ≫ cechConstantPositiveDoubleMap f := by
  apply HomologicalComplex.Hom.ext
  funext n
  cases n with
  | zero =>
    change f ≫ 0 = 0 ≫ 𝟙 (HomologicalComplex.zero : CochainComplex (ModuleCat.{u} R) ℕ)
    rw [comp_zero, zero_comp]
  | succ n =>
    change f ≫ 𝟙 B = 𝟙 A ≫ f
    rw [Category.comp_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/-- 同じ正次数の商の関手は、元の複体の短完全性を保つ。 -/
theorem cechConstantPositiveDouble_shortExact
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℕ)) (hS : S.ShortExact) :
    (S.map cechConstantPositiveDoubleFunctor).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  cases n with
  | zero =>
    let T := (S.map cechConstantPositiveDoubleFunctor).map
      (HomologicalComplex.eval (CochainComplex (ModuleCat.{u} R) ℕ) (.up ℕ) 0)
    have hz : IsZero T.X₂ := HomologicalComplex.isZero_zero
    refine { exact := ShortComplex.exact_of_isZero_X₂ T hz, mono_f := ?_, epi_g := ?_ }
    · change Mono (𝟙 (HomologicalComplex.zero : CochainComplex (ModuleCat.{u} R) ℕ))
      infer_instance
    · change Epi (𝟙 (HomologicalComplex.zero : CochainComplex (ModuleCat.{u} R) ℕ))
      infer_instance
  | succ n => exact hS

end SerrePositivity.AlgebraicGeometry
