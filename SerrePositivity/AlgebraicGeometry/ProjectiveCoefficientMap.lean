module

public import SerrePositivity.AlgebraicGeometry.HomogeneousDegreeOneBaseChange
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

/-!
概要：任意の係数移送が定める Proj の実際の射。
方針：各次数の baseChange の span と irrelevant ideal の像を照合する。
規約：flat 性・Noether 性・次数一生成を仮定しない。
使われ方：任意のアフィン底変換の Proj の表示と標準開の pullback 比較。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
open scoped TensorProduct
universe u
variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B]
variable (G : ℕ → Submodule R A) [GradedRing G]

/-- 係数環 B の次数成分を使う、同じ includeRight の graded な環写像。 -/
def projectiveCoefficientGradedMap : G →+*ᵍ (fun n ↦ (G n).baseChange B) where
  toRingHom := (Algebra.TensorProduct.includeRight : A →ₐ[R] B ⊗[R] A).toRingHom
  map_mem hx := Submodule.tmul_mem_baseChange_of_mem (1 : B) hx

/-- 移送後の irrelevant ideal は、元の irrelevant ideal の像に入る。 -/
theorem projectiveCoefficient_irrelevant_le_map :
    HomogeneousIdeal.irrelevant (fun n ↦ (G n).baseChange B) ≤
      (HomogeneousIdeal.irrelevant G).map (projectiveCoefficientGradedMap (B := B) G) := by
  apply (HomogeneousIdeal.irrelevant_le (fun n ↦ (G n).baseChange B)).mpr
  intro d hd x hx
  let J : Ideal (B ⊗[R] A) := (HomogeneousIdeal.irrelevant G).toIdeal.map
    (projectiveCoefficientGradedMap (B := B) G).toRingHom
  have hspan : (G d).baseChange B ≤ J.restrictScalars B := by
    rw [Submodule.baseChange_eq_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨a, ha, rfl⟩
    change projectiveCoefficientGradedMap (B := B) G a ∈ J
    exact Ideal.mem_map_of_mem _ (HomogeneousIdeal.mem_irrelevant_of_mem G hd ha)
  exact hspan hx

/-- 任意の係数移送が定める、移送後の Proj から元の Proj への実際の射。 -/
def projectiveCoefficientMap : Proj (fun n ↦ (G n).baseChange B) ⟶ Proj G :=
  Proj.map (projectiveCoefficientGradedMap (B := B) G) (projectiveCoefficient_irrelevant_le_map G)

/-- 係数移送の射の標準開の逆像は、同じ元を移送した標準開。 -/
theorem projectiveCoefficientMap_preimage_basicOpen (s : A) :
    projectiveCoefficientMap (B := B) G ⁻¹ᵁ Proj.basicOpen G s =
      Proj.basicOpen (fun n ↦ (G n).baseChange B) ((1 : B) ⊗ₜ[R] s) :=
  Proj.map_preimage_basicOpen _ _ s

end SerrePositivity.AlgebraicGeometry
