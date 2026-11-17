module

public import SerrePositivity.AlgebraicGeometry.SegreChartEquiv
public import SerrePositivity.AlgebraicGeometry.AffineSectionComponentLocus

/-!
概要：Segre 標準開の二つの因子への射は、Spec R 上の Cartesian 四角形を与える。
方針：実際のテンソル積との代数同型で Spec の既存の pullback を移送する。
規約：元の R 上の代数構造を保ち、平坦性・Noether 性を仮定しない。
使われ方：Segre の大域のファイバー積を標準開上で判定する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct
universe u
variable {R A B : Type u} {ι κ : Type} [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B] (a : ι → A) (b : κ → B)
variable (G : ℕ → Submodule R A) [GradedRing G]
variable (H : ℕ → Submodule R B) [GradedRing H]
variable (ha : ∀ k, a k ∈ G 1) (hb : ∀ l, b l ∈ H 1)
local instance segrePullbackColumnAlgebra (x : A) :
    Algebra R (HomogeneousLocalization.Away G x) := projectiveHomogeneousAwayAlgebra G x
local instance segrePullbackRowAlgebra (x : B) :
    Algebra R (HomogeneousLocalization.Away H x) := projectiveHomogeneousAwayAlgebra H x
local instance segrePullbackStandardAlgebra
    [GradedRing (segreCoordinateGrade (R := R) a b)] (x : SegreCoordinateRing (R := R) a b) :
    Algebra R (HomogeneousLocalization.Away (segreCoordinateGrade (R := R) a b) x) :=
  projectiveHomogeneousAwayAlgebra (segreCoordinateGrade (R := R) a b) x

set_option backward.isDefEq.respectTransparency false in
/-- 列・行の標準開写像の Spec は、同じ Spec R 上の実際の pullback。 -/
theorem isPullback_segreStandardOpen
    (hsA : Function.Surjective (MvPolynomial.aeval (R := R) a))
    (hsB : Function.Surjective (MvPolynomial.aeval (R := R) b)) (i : ι) (j : κ) :
    letI := segreCoordinateGradedRing a b G ha
    IsPullback
      (Spec.map (CommRingCat.ofHom (segreColumnChartMap a b G i j ha hsA).toRingHom))
      (Spec.map (CommRingCat.ofHom (segreRowChartMap a b G H i j ha hb hsB).toRingHom))
      (Spec.map (CommRingCat.ofHom (algebraMap R (HomogeneousLocalization.Away G (a i)))))
      (Spec.map (CommRingCat.ofHom (algebraMap R (HomogeneousLocalization.Away H (b j))))) := by
  let := segreCoordinateGradedRing a b G ha
  let e := segreStandardOpenTensorEquiv a b G H i j ha hb hsA hsB
  refine (isPullback_specTensor R
    (HomogeneousLocalization.Away G (a i)) (HomogeneousLocalization.Away H (b j))).of_iso'
    (Scheme.Spec.mapIso e.symm.toRingEquiv.toCommRingCatIso.op)
    (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
  · change Spec.map (CommRingCat.ofHom
        (segreTensorToStandardOpen a b G H i j ha hb hsA hsB).toRingHom) ≫
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : HomogeneousLocalization.Away G (a i) →ₐ[R]
          (HomogeneousLocalization.Away H (b j)) ⊗[R]
            (HomogeneousLocalization.Away G (a i))).toRingHom) = _
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    change segreTensorToStandardOpen a b G H i j ha hb hsA hsB (1 ⊗ₜ[R] x) = _
    simp [segreTensorToStandardOpen]
  · change Spec.map (CommRingCat.ofHom
        (segreTensorToStandardOpen a b G H i j ha hb hsA hsB).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (HomogeneousLocalization.Away H (b j))
        ((HomogeneousLocalization.Away H (b j)) ⊗[R]
          (HomogeneousLocalization.Away G (a i))))) = _
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    change segreTensorToStandardOpen a b G H i j ha hb hsA hsB (x ⊗ₜ[R] 1) = _
    simp [segreTensorToStandardOpen]

end SerrePositivity.AlgebraicGeometry
