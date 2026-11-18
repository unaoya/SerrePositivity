module

public import SerrePositivity.AlgebraicGeometry.ProjectiveCoefficientChart
public import SerrePositivity.AlgebraicGeometry.AffineTensorModelPullback

/-!
概要：係数移送の標準開を、実際の Cartesian な四角形で記述する。
方針：構成済みの標準開の代数同型と、Spec のテンソル積の pullback を使う。
規約：係数移送は任意。flat 性・Noether 性を仮定しない。
使われ方：Proj の係数移送を標準開上で判定する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct
universe u
variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B]
variable (G : ℕ → Submodule R A) [GradedRing G]
local instance projectiveCoefficientPullbackSourceAlgebra (f : A) :
    Algebra R (HomogeneousLocalization.Away G f) := projectiveHomogeneousAwayAlgebra G f
local instance projectiveCoefficientPullbackTargetAlgebra (f : A) :
    Algebra B (HomogeneousLocalization.Away (fun n ↦ (G n).baseChange B) ((1 : B) ⊗ₜ[R] f)) :=
  projectiveHomogeneousAwayAlgebra (fun n ↦ (G n).baseChange B) ((1 : B) ⊗ₜ[R] f)

set_option backward.isDefEq.respectTransparency false in
/-- 次数一の標準開の係数移送は、同じ Spec R 上の実際の pullback。 -/
theorem isPullback_projectiveCoefficientChart {f : A} (hf : f ∈ G 1) :
    IsPullback
      (Spec.map (CommRingCat.ofHom
        (HomogeneousLocalization.Away.map (projectiveCoefficientGradedMap (B := B) G) f)))
      (Spec.map (CommRingCat.ofHom
        (algebraMap B (HomogeneousLocalization.Away (fun n ↦ (G n).baseChange B)
          ((1 : B) ⊗ₜ[R] f)))))
      (Spec.map (CommRingCat.ofHom (algebraMap R (HomogeneousLocalization.Away G f))))
      (Spec.map (CommRingCat.ofHom (algebraMap R B))) := by
  refine (IsPullback.of_hasPullback _ _).of_iso'
    (affineTensorModelIso (homogeneousDegreeOneBaseChangeEquiv (B := B) G hf))
    (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
  · simpa only [Iso.refl_hom, Category.comp_id, projectiveCoefficientAwayMap_eq G hf]
      using affineTensorModelIso_hom_fst (homogeneousDegreeOneBaseChangeEquiv (B := B) G hf)
  · simpa only [Iso.refl_hom, Category.comp_id]
      using affineTensorModelIso_hom_snd (homogeneousDegreeOneBaseChangeEquiv (B := B) G hf)

set_option backward.isDefEq.respectTransparency false in
/-- 任意の正次数の標準開の四角形は、Proj の係数移送の射の pullback。 -/
theorem isPullback_projectiveCoefficientAwayι {f : A} {d : ℕ} (hf : f ∈ G d) (hd : 0 < d) :
    IsPullback
      (Spec.map (CommRingCat.ofHom
        (HomogeneousLocalization.Away.map (projectiveCoefficientGradedMap (B := B) G) f)))
      (Proj.awayι (fun n ↦ (G n).baseChange B) ((1 : B) ⊗ₜ[R] f)
        (Submodule.tmul_mem_baseChange_of_mem (1 : B) hf) hd)
      (Proj.awayι G f hf hd) (projectiveCoefficientMap (B := B) G) := by
  apply IsOpenImmersion.isPullback
  · exact Proj.awayι_comp_map (projectiveCoefficientGradedMap (B := B) G)
      (projectiveCoefficient_irrelevant_le_map G) hd f hf
  · rw [Proj.opensRange_awayι, Proj.opensRange_awayι,
      projectiveCoefficientMap_preimage_basicOpen]

end SerrePositivity.AlgebraicGeometry
