module

public import SerrePositivity.AlgebraicGeometry.ArcRouteB.Definitions
public import SerrePositivity.CommutativeAlgebra.PerfectRing

/-!
概要：有限族と積への一射のarc判定、底変換と細分の互換性。
方針：付値拡大の証人を保ち、整域への有限積の射の因子化とtensorの普遍性を使う。
規約：元の付値環と拡大の階数をともに保つ。
使われ方：2iのU04〜U06、BM18 Definition 1.2の有限族と一射の照合。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory
open SerrePositivity
open scoped TensorProduct
namespace SerrePositivity.AlgebraicGeometry.ArcRouteB

/-- 計画U04：元の付値拡大と階数を保つ被覆の法則。 -/
theorem isArcHom_pi_iff {A : Type u} [CommRing A]
    {ι : Type u} [Finite ι] (B : ι → Type u) [∀ i, CommRing (B i)]
    (f : ∀ i, A →+* B i) :
    IsArcHom (RingHom.pi f) ↔ IsArcCoverFamilyCharP B f := by
  constructor
  · intro h V _ _ hdim k
    obtain ⟨W, hW, hval, hdimW, e, l, he, hl⟩ := h V hdim k
    letI : IsDomain W := hW
    obtain ⟨i, m, hm⟩ := exists_factor_evalRingHom_of_isDomain B l
    refine ⟨i, W, hW, hval, hdimW, e, m, he, ?_⟩
    apply RingHom.ext
    intro a
    exact (RingHom.congr_fun hm (RingHom.pi f a)).trans (RingHom.congr_fun hl a)
  · intro h V _ _ hdim k
    obtain ⟨i, W, hW, hval, hdimW, e, l, he, hl⟩ := h V hdim k
    refine ⟨W, hW, hval, hdimW, e, l.comp (Pi.evalRingHom B i), he, ?_⟩
    exact RingHom.ext fun a ↦ RingHom.congr_fun hl a

/-- 計画U05：元の付値拡大と階数を保つ被覆の法則。 -/
theorem isArcHom_baseChange {A B T : Type u} [CommRing A]
    [CommRing B] [CommRing T] (f : A →+* B) (g : A →+* T)
    (hf : IsArcHom f) : IsArcHom (arcBaseChangeHom f g) := by
  letI := f.toAlgebra
  letI := g.toAlgebra
  intro V _ _ hdim k
  obtain ⟨W, hW, hval, hdimW, e, l, he, hl⟩ := hf V hdim (k.comp g)
  letI : IsDomain W := hW
  have hc (a : A) : (e.comp k) (algebraMap A T a) = l (algebraMap A B a) :=
    (RingHom.congr_fun hl a).symm
  let r := coefficientTensorLift (e.comp k) l hc
  refine ⟨W, hW, hval, hdimW, e, r, he, ?_⟩
  apply RingHom.ext
  intro t
  change r (t ⊗ₜ[A] (1 : B)) = (e.comp k) t
  rw [coefficientTensorLift_tmul, map_one, mul_one]

/-- 計画U06：元の付値拡大と階数を保つ被覆の法則。 -/
theorem isArcHom_of_refinement {A B C : Type u} [CommRing A]
    [CommRing B] [CommRing C] (f : A →+* B) (g : A →+* C)
    (r : B →+* C) (hr : r.comp f = g) (hg : IsArcHom g) : IsArcHom f := by
  intro V _ _ hdim k
  obtain ⟨W, hW, hval, hdimW, e, l, he, hl⟩ := hg V hdim k
  refine ⟨W, hW, hval, hdimW, e, l.comp r, he, ?_⟩
  rw [RingHom.comp_assoc, hr, hl]

end SerrePositivity.AlgebraicGeometry.ArcRouteB
