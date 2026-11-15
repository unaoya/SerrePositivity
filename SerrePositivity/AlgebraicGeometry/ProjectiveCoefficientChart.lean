module

public import SerrePositivity.AlgebraicGeometry.ProjectiveCoefficientMap
public import SerrePositivity.AlgebraicGeometry.HomogeneousDegreeOneBaseChangeFormula
public import SerrePositivity.AlgebraicGeometry.HomogeneousDegreeOneNormalizationNaturality
public import SerrePositivity.AlgebraicGeometry.DegreeOneChartExt

/-!
概要：任意の係数移送の Proj の射と、標準開の代数同型との一致。
方針：正規化の全射性・自然性と、純テンソルの像の式で照合する。
規約：flat 性・Noether 性を仮定しない。
使われ方：Proj のアフィン底変換の局所的な pullback 比較。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
open scoped TensorProduct
universe u
variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B]
variable (G : ℕ → Submodule R A) [GradedRing G] {f : A} (hf : f ∈ G 1)
local instance projectiveCoefficientChartSourceAlgebra :
    Algebra R (HomogeneousLocalization.Away G f) := projectiveHomogeneousAwayAlgebra G f

/-- 係数移送の標準開の写像は、テンソル積への包含と構成した同型の合成。 -/
theorem projectiveCoefficientAwayMap_eq :
    HomogeneousLocalization.Away.map (projectiveCoefficientGradedMap (B := B) G) f =
      (homogeneousDegreeOneBaseChangeEquiv (B := B) G hf).toRingHom.comp
        (Algebra.TensorProduct.includeRight : HomogeneousLocalization.Away G f →ₐ[R]
          B ⊗[R] HomogeneousLocalization.Away G f).toRingHom := by
  apply RingHom.ext
  intro z
  obtain ⟨x, rfl⟩ := homogeneousDegreeOneNormalize_surjective G hf z
  change HomogeneousLocalization.Away.map (projectiveCoefficientGradedMap (B := B) G) f
    (homogeneousDegreeOneNormalize G hf x) =
      homogeneousDegreeOneBaseChangeEquiv (B := B) G hf
        ((1 : B) ⊗ₜ[R] homogeneousDegreeOneNormalize G hf x)
  rw [homogeneousDegreeOneNormalize_naturality]
  exact (homogeneousDegreeOneBaseChangeEquiv_tmul_normalize G hf (1 : B) x).symm

/-- 係数移送の Proj の射は、標準開の同型からの実際の Spec の写像と整合する。 -/
theorem projectiveCoefficientMap_awayι :
    Proj.awayι (fun n ↦ (G n).baseChange B) ((1 : B) ⊗ₜ[R] f)
        (Submodule.tmul_mem_baseChange_of_mem (1 : B) hf) (by decide) ≫
      projectiveCoefficientMap (B := B) G =
      Spec.map (CommRingCat.ofHom
        ((homogeneousDegreeOneBaseChangeEquiv (B := B) G hf).toRingHom.comp
        (Algebra.TensorProduct.includeRight : HomogeneousLocalization.Away G f →ₐ[R]
          B ⊗[R] HomogeneousLocalization.Away G f).toRingHom)) ≫ Proj.awayι G f hf (by decide) := by
  change Proj.awayι _ (projectiveCoefficientGradedMap (B := B) G f) _ _ ≫
    Proj.map (projectiveCoefficientGradedMap (B := B) G) _ = _
  rw [Proj.awayι_comp_map (projectiveCoefficientGradedMap (B := B) G)
    (projectiveCoefficient_irrelevant_le_map G) (by decide : 0 < 1) f hf,
    projectiveCoefficientAwayMap_eq G hf]
  rfl

end SerrePositivity.AlgebraicGeometry
