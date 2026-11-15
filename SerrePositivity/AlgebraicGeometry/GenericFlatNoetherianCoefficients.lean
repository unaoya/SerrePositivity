module

public import SerrePositivity.AlgebraicGeometry.MinimalPrimeQuotientFactor
public import Mathlib.RingTheory.Adjoin.FG

/-!
概要：極小素点での有限関係の消去を、有限生成の係数部分代数に保存する。
方針：共通消去元を一つ adjoin し、その局所化で商を経由させる。
規約：係数環の Noether 性の代わりに縮約イデアルの有限生成性を入力する。
使われ方：選んだ一般自由開を Noether 模型上にも供給する係数移送。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
universe u v

/-- 共通消去元を反転すると、係数射は指定イデアルの商を経由する。 -/
private def quotientToAwayOfAnnihilator
    {S : Type v} [CommRing S] {R : Type u} [CommRing R]
    (f : S →+* R) (J : Ideal S) (s : R) (hann : ∀ a ∈ J, s * f a = 0) :
    S ⧸ J →+* Localization.Away s :=
  Ideal.Quotient.lift J ((algebraMap R (Localization.Away s)).comp f) (by
    intro a ha
    apply (IsLocalization.map_eq_zero_iff (Submonoid.powers s) (Localization.Away s) (f a)).mpr
    exact ⟨⟨s, ⟨1, pow_one s⟩⟩, hann a ha⟩)

/-- 極小素点での商への因子化は、消去元を含む有限生成部分代数で実現できる。 -/
theorem exists_fg_subalgebra_quotient_localization_factor
    {S : Type v} [CommRing S] {R : Type u} [CommRing R] [IsReduced R] [Algebra S R]
    {p : Ideal R} (hp : p ∈ minimalPrimes R)
    (hfg : (p.comap (algebraMap S R)).FG) :
    ∃ T : Subalgebra S R, T.FG ∧ ∃ s : T, (s : R) ∉ p ∧
      ∃ l : S ⧸ p.comap (algebraMap S R) →+* Localization.Away s,
        l.comp (Ideal.Quotient.mk (p.comap (algebraMap S R))) =
          (algebraMap T (Localization.Away s)).comp (algebraMap S T) := by
  classical
  let f := algebraMap S R
  obtain ⟨r, hr, hkill⟩ := exists_common_annihilator_fg_minimalPrime hp (hfg.map f)
    (Ideal.map_le_iff_le_comap.mpr le_rfl)
  let T := Algebra.adjoin S (↑({r} : Finset R) : Set R)
  let s : T := ⟨r, Algebra.subset_adjoin (by simp)⟩
  have hann (a : S) (ha : a ∈ p.comap f) : s * algebraMap S T a = 0 := by
    apply Subtype.ext
    change r * f a = 0
    exact hkill (f a) (Ideal.mem_map_of_mem f ha)
  refine ⟨T, Subalgebra.fg_adjoin_finset {r}, s, hr,
    quotientToAwayOfAnnihilator (algebraMap S T) (p.comap f) s hann, ?_⟩
  ext a
  rfl

end SerrePositivity.AlgebraicGeometry
