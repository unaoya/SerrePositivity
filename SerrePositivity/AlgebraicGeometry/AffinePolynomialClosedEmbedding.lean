module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
概要：有限型 affine を、実際の有限変数の多項式空間へ閉埋め込みする。
方針：有限型代数の多項式環からの全射を Spec に移し、係数射の可換式を追う。
規約：Stacks 01VS の affine の場合の、標準開への immersion の前半。
使われ方：C05 の固有な Proj の周辺への immersion の構成。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u

/-- 有限型 R-代数の Spec は有限変数の多項式空間へ Spec R 上で閉埋め込みする。 -/
theorem exists_affine_polynomial_closed_embedding
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] [Algebra.FiniteType R A] :
    ∃ (s : Finset A) (j : Spec (CommRingCat.of A) ⟶
        Spec (CommRingCat.of (MvPolynomial s R))),
      IsClosedImmersion j ∧
        j ≫ Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial s R))) =
          Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
  obtain ⟨s, q, hq⟩ := (Algebra.FiniteType.iff_quotient_mvPolynomial (R := R) (S := A)).mp
    (inferInstance : Algebra.FiniteType R A)
  refine ⟨s, Spec.map (CommRingCat.ofHom q.toRingHom),
    IsClosedImmersion.spec_of_surjective _ hq, ?_⟩
  rw [← Spec.map_comp]
  congr 1
  ext r
  exact q.commutes r

end SerrePositivity.AlgebraicGeometry
