module

public import SerrePositivity.AlgebraicGeometry.AffineVCover
public import SerrePositivity.AlgebraicGeometry.FiniteProductDomainFactor

/-!
概要：付値判定における有限族と積への一射を同定する。
方針：整域への有限積の射の因子化を使い、同じ付値環拡大を保持する。
規約：族の添字と環の宇宙は drafts の入口と同じ。
使われ方：BS17 Thm 4.1(i) の有限族を affine な一射へまとめる G0 の橋。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
universe u
variable {A : Type u} [CommRing A] {ι : Type u} [Finite ι]
variable (B : ι → Type u) [∀ i, CommRing (B i)] (f : ∀ i, A →+* B i)

/-- 有限族の v 判定は、積への環準同型の v 判定と同値。 -/
theorem isAffineVCoverFamily_iff_pi :
    IsAffineVCoverFamily B f ↔ IsAffineVCover (RingHom.pi f) := by
  constructor
  · intro h V _ _ k
    obtain ⟨i, W, hW, hval, _, e, l, he, hl⟩ := h V trivial k
    refine ⟨W, hW, hval, e, l.comp (Pi.evalRingHom B i), he, ?_⟩
    exact RingHom.ext fun a ↦ RingHom.congr_fun hl a
  · intro h V _ _ _ k
    obtain ⟨W, hW, hval, e, l, he, hl⟩ := h V k
    letI : IsDomain W := hW
    obtain ⟨i, m, hm⟩ := exists_factor_evalRingHom_of_isDomain B l
    refine ⟨i, W, hW, hval, trivial, e, m, he, ?_⟩
    apply RingHom.ext
    intro a
    exact (RingHom.congr_fun hm (RingHom.pi f a)).trans (RingHom.congr_fun hl a)

/-- 有限族の一つの射が v 被覆なら、族全体も v 被覆。 -/
theorem isAffineVCoverFamily_of_member (i : ι) (h : IsAffineVCover (f i)) :
    IsAffineVCoverFamily B f := by
  intro V _ _ _ k
  obtain ⟨W, hW, hval, e, l, he, hl⟩ := h V k
  exact ⟨i, W, hW, hval, trivial, e, l, he, hl⟩

/-- 細分された有限族の付値判定から元の有限族の判定を得る。 -/
theorem IsAffineVCoverFamily.of_refinement
    {κ : Type u} [Finite κ] (C : κ → Type u) [∀ j, CommRing (C j)]
    (g : ∀ j, A →+* C j) (ρ : κ → ι) (l : ∀ j, B (ρ j) →+* C j)
    (hl : ∀ j, (l j).comp (f (ρ j)) = g j) (h : IsAffineVCoverFamily C g) :
    IsAffineVCoverFamily B f := by
  intro V _ _ _ k
  obtain ⟨j, W, hW, hval, _, e, m, he, hm⟩ := h V trivial k
  refine ⟨ρ j, W, hW, hval, trivial, e, m.comp (l j), he, ?_⟩
  rw [RingHom.comp_assoc, hl, hm]

/-- 各成分をさらに有限な v 被覆族で覆うと、その合成族も v 被覆。 -/
theorem IsAffineVCoverFamily.comp (hf : IsAffineVCoverFamily B f)
    {κ : ι → Type u} [∀ i, Finite (κ i)]
    (C : ∀ i, κ i → Type u) [∀ i j, CommRing (C i j)]
    (g : ∀ i j, B i →+* C i j) (hg : ∀ i, IsAffineVCoverFamily (C i) (g i)) :
    IsAffineVCoverFamily (fun ij : Sigma κ ↦ C ij.1 ij.2)
      (fun ij ↦ (g ij.1 ij.2).comp (f ij.1)) := by
  intro V _ _ _ k
  obtain ⟨i, W, hW, hvalW, _, e, l, he, hl⟩ := hf V trivial k
  letI : IsDomain W := hW
  letI : ValuationRing W := hvalW
  obtain ⟨j, Z, hZ, hvalZ, _, d, m, hd, hm⟩ := hg i W trivial l
  refine ⟨⟨i, j⟩, Z, hZ, hvalZ, trivial, d.comp e, m,
    RingHom.FaithfullyFlat.stableUnderComposition e d he hd, ?_⟩
  rw [← RingHom.comp_assoc, hm, RingHom.comp_assoc, hl, RingHom.comp_assoc]

end SerrePositivity.AlgebraicGeometry
