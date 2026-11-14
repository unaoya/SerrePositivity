module

public import SerrePositivity.AlgebraicGeometry.AffineOpenVCoverRefinement
public import SerrePositivity.AlgebraicGeometry.AffineRingVCoverRefinement

/-!
概要：任意の affine 基底上の有限表示 v 被覆を、固有全射と fppf 射で細分する。
方針：有限アフィン開被覆による始域の細分に、一般の環上の affine 始域の出口を適用する。
規約：元の射に平坦性・固有性・Noether 性を要求しない。Rydh 3.10 の affine 基底の場合。
使われ方：G1 の非 Noether affine 基底の細分 A07。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u

/-- 任意の affine 基底の局所有限表示・準コンパクトな v 被覆は、有限表示の固有全射と fppf 射で細分できる。 -/
theorem exists_fppf_proper_refinement_vCover_affineBase
    {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R)
    [LocallyOfFinitePresentation f] [QuasiCompact f] (hf : IsSchemeVCover f) :
    ∃ (T W : Scheme.{u}) (r : T ⟶ Spec R) (q : W ⟶ T) (k : W ⟶ X),
      IsProper r ∧ Surjective r ∧ LocallyOfFinitePresentation r ∧ QuasiCompact r ∧
      Flat q ∧ Surjective q ∧ LocallyOfFinitePresentation q ∧ QuasiCompact q ∧ k ≫ f = q ≫ r := by
  obtain ⟨B, _, _, hB, a, hb, ha⟩ :=
    exists_affine_finitePresentation_vCover_refinement R f hf
  letI : Algebra.FinitePresentation R B := hB
  obtain ⟨T, W, q, r, l, hr, hrfp, hrsurj, hq, hqfp, hqqc, hqsurj, hl⟩ :=
    exists_fppf_proper_refinement_vCover_affineRing R B hb
  letI : IsProper r := hr
  refine ⟨T, W, r, q, l ≫ a, hr, hrsurj, hrfp, inferInstance,
    hq, hqsurj, hqfp, hqqc, ?_⟩
  rw [Category.assoc, ha, hl]

end SerrePositivity.AlgebraicGeometry
