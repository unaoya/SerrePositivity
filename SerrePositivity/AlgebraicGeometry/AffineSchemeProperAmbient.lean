module

public import SerrePositivity.AlgebraicGeometry.AffineProperAmbient
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
概要：任意の affine スキーム間の局所有限型の射に、実際の固有な周辺への immersion を供給する。
方針：全切断の実際の環写像に C05 を適用し、canonical な Spec の同型で戻す。
規約：係数の環の同型の自然性で元の構造射を保ち、Noether 性を要求しない。
使われ方：C06 の有限 affine 被覆の各チャートの固有な周辺。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u

/-- affine な局所有限型の射は、同じ実際の基底上の固有な周辺へ immersion する。 -/
theorem exists_affine_scheme_immersion_proper_ambient
    {X S : Scheme.{u}} [IsAffine X] [IsAffine S] (f : X ⟶ S) [LocallyOfFiniteType f] :
    ∃ (P : Scheme.{u}) (q : P ⟶ S) (j : X ⟶ P),
      IsProper q ∧ IsImmersion j ∧ j ≫ q = f := by
  let R := Γ(S, ⊤)
  let A := Γ(X, ⊤)
  letI : Algebra R A := f.appTop.hom.toAlgebra
  letI : Algebra.FiniteType R A :=
    HasRingHomProperty.appTop (P := @LocallyOfFiniteType) f inferInstance
  obtain ⟨P, q, j, hq, hj, hcomm⟩ := exists_affine_immersion_proper_ambient R A
  letI : IsProper q := hq
  letI : IsImmersion j := hj
  have hc : j ≫ q = Spec.map f.appTop := by
    simpa only [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom] using hcomm
  refine ⟨P, q ≫ S.isoSpec.inv, X.isoSpec.hom ≫ j, inferInstance, inferInstance, ?_⟩
  calc
    _ = X.isoSpec.hom ≫ (j ≫ q) ≫ S.isoSpec.inv := by simp only [Category.assoc]
    _ = X.isoSpec.hom ≫ Spec.map f.appTop ≫ S.isoSpec.inv := by rw [hc]
    _ = f := by rw [Scheme.isoSpec_hom_naturality_assoc, Iso.hom_inv_id, Category.comp_id]

end SerrePositivity.AlgebraicGeometry
