module

public import SerrePositivity.HomologicalAlgebra.TwoTermConeAnnihilator

/-! # 実可換図式から元の加群写像の錐への零化の移送

始域比較と比較先の写像の核・余核、終域比較の核の零化を使う。
終域比較の余核、有限性、平坦性は要求しない。
-/

@[expose] public noncomputable section
universe u v w
namespace SerrePositivity
variable {R M N : Type u} {L : Type v} {P : Type w} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup L] [Module R L]
    [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]

/-- 三辺の実比較から元の写像の核・余核の具体的な零化因子を得る。 -/
theorem ker_coker_annihilated_of_comparison_square
    (f : M →ₗ[R] N) (s : M →ₗ[R] L) (h : L →ₗ[R] P) (t : N →ₗ[R] P)
    (hsq : t.comp f = h.comp s) (a b c d e : R)
    (hsk : ∀ x : s.ker, a • x = 0) (hsc : ∀ y : L ⧸ s.range, b • y = 0)
    (hhk : ∀ x : h.ker, c • x = 0) (hhc : ∀ y : P ⧸ h.range, d • y = 0)
    (htk : ∀ x : t.ker, e • x = 0) :
    (∀ x : f.ker, (a * c) • x = 0) ∧
      (∀ y : N ⧸ f.range, (e * b * d) • y = 0) := by
  have hs (x : M) : t (f x) = h (s x) := LinearMap.congr_fun hsq x
  constructor
  · intro x
    apply Subtype.ext
    change (a * c) • (x : M) = 0
    have hh : h (s (x : M)) = 0 := by rw [← hs, x.property, map_zero]
    have hcs : c • s (x : M) = 0 := congrArg Subtype.val (hhk ⟨s x, hh⟩)
    have hscx : s (c • (x : M)) = 0 := (s.map_smul c x).trans hcs
    have hac : a • (c • (x : M)) = 0 := congrArg Subtype.val (hsk ⟨c • x, hscx⟩)
    simpa only [mul_smul] using hac
  · intro y
    obtain ⟨y, rfl⟩ := f.range.mkQ_surjective y
    have hdy : d • t y ∈ h.range := by
      apply (Submodule.Quotient.mk_eq_zero h.range).mp
      exact (h.range.mkQ.map_smul d (t y)).trans (hhc _)
    obtain ⟨z, hz⟩ := hdy
    have hbz : b • z ∈ s.range := by
      apply (Submodule.Quotient.mk_eq_zero s.range).mp
      exact (s.range.mkQ.map_smul b z).trans (hsc _)
    obtain ⟨x, hx⟩ := hbz
    have hcomp : h (s x) = (b * d) • t y := by
      rw [hx, map_smul, hz, smul_smul]
    have hzero : t ((b * d) • y - f x) = 0 := by
      rw [map_sub, map_smul, hs, hcomp, sub_self]
    have he : e • ((b * d) • y - f x) = 0 :=
      congrArg Subtype.val (htk ⟨(b * d) • y - f x, hzero⟩)
    have he' : (e * b * d) • y = f (e • x) := by
      rw [smul_sub, smul_smul, ← f.map_smul, sub_eq_zero] at he
      simpa only [mul_assoc] using he
    rw [← map_smul]
    apply (Submodule.Quotient.mk_eq_zero f.range).mpr
    exact ⟨e • x, he'.symm⟩

/-- 同じ元の可換図式から、元の実錐のスカラー射を零にする。 -/
theorem moduleMapConeScalar_of_comparison_square
    (f : M →ₗ[R] N) (s : M →ₗ[R] L) (h : L →ₗ[R] P) (t : N →ₗ[R] P)
    (hsq : t.comp f = h.comp s) (a b c d e : R)
    (hsk : ∀ x : s.ker, a • x = 0) (hsc : ∀ y : L ⧸ s.range, b • y = 0)
    (hhk : ∀ x : h.ker, c • x = 0) (hhc : ∀ y : P ⧸ h.range, d • y = 0)
    (htk : ∀ x : t.ker, e • x = 0) :
    moduleMapConeScalar R f ((a * c) * (e * b * d)) = 0 := by
  obtain ⟨hk, hc⟩ := ker_coker_annihilated_of_comparison_square f s h t hsq
    a b c d e hsk hsc hhk hhc htk
  apply moduleMapConeScalar_eq_zero_of_ker_coker_annihilated R f
  · intro x hx
    exact congrArg Subtype.val (hk ⟨x, hx⟩)
  · exact hc

end SerrePositivity
