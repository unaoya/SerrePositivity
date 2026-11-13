module

public import SerrePositivity.AlgebraicGeometry.AffineVCover
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
概要：nil な核を持つ全射は affine v 被覆である。
方針：付値整域への射が nil な核を消すことを使い、同じ試験付値環へ射を降ろす。
規約：冪零指数の一様性や Noether 性を要求しない。
使われ方：2g の被約化・nilimmersion の付値判定。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
universe u
variable {A B : Type u} [CommRing A] [CommRing B]

/-- nil な核を持つ環の全射は、同じ付値試験環への持ち上げを持つ。 -/
theorem isAffineVCover_of_surjective_of_nil_kernel (f : A →+* B)
    (hf : Function.Surjective f) (hn : RingHom.ker f ≤ nilradical A) : IsAffineVCover f := by
  intro V _ _ k
  have hk : RingHom.ker f ≤ RingHom.ker k := by
    intro a ha
    exact RingHom.mem_ker.mpr (isNilpotent_iff_eq_zero.mp ((mem_nilradical.mp (hn ha)).map k))
  refine ⟨V, inferInstance, inferInstance, RingHom.id V,
    f.liftOfSurjective hf ⟨k, hk⟩,
    RingHom.FaithfullyFlat.of_bijective Function.bijective_id, ?_⟩
  simpa only [RingHom.id_comp] using RingHom.liftOfSurjective_comp f hf ⟨k, hk⟩

/-- nil イデアルによる商射は affine v 被覆。 -/
theorem isAffineVCover_quotient_of_le_nilradical (J : Ideal A) (hJ : J ≤ nilradical A) :
    IsAffineVCover (Ideal.Quotient.mk J) :=
  isAffineVCover_of_surjective_of_nil_kernel _ Ideal.Quotient.mk_surjective
    (by simpa only [Ideal.mk_ker] using hJ)

end SerrePositivity.AlgebraicGeometry
