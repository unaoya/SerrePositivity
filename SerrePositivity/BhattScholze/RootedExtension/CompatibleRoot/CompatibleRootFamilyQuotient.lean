module

public import SerrePositivity.BhattScholze.RootedExtension.CompatibleRoot.CompatibleRootFamilyIdeal
public import SerrePositivity.BhattScholze.RootedExtension.CompatibleRoot.CompatibleRootCompletionSurjective

/-! # B4-4：任意根族の商とp完備化の普遍性・標準射

被約なp進完備試験環への普遍性を先に示し、perfectoid試験環への入口を特殊化する。
候補自身のperfectoid性は別の仮定とする。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R] {σ : Type u}

/-- 最初の元の全体の商から、全根族の商への標準射。 -/
def compatibleRootFamilyQuotientMap (ρ : σ → ℕ → R) :
    R ⧸ compatibleRootFamilyZeroIdeal ρ →+* R ⧸ compatibleRootFamilyIdeal ρ :=
  Ideal.quotientMap _ (RingHom.id R) (compatibleRootFamilyZeroIdeal_le ρ)

/-- 根族商のp完備化の具体的な環。 -/
abbrev CompatibleRootFamilyCompletion (p : ℕ) (ρ : σ → ℕ → R) :=
  AdicCompletion (Ideal.span {(p : R ⧸ compatibleRootFamilyIdeal ρ)})
    (R ⧸ compatibleRootFamilyIdeal ρ)

/-- 最初の元の商から、全根族の商のp完備化への標準射。 -/
def compatibleRootFamilyCompletionMap (p : ℕ) (ρ : σ → ℕ → R) :
    R ⧸ compatibleRootFamilyZeroIdeal ρ →+* CompatibleRootFamilyCompletion p ρ :=
  (algebraMap (R ⧸ compatibleRootFamilyIdeal ρ) _).comp (compatibleRootFamilyQuotientMap ρ)

omit [Fact p.Prime] in
/-- 被約なp進完備試験環への射は、全根族商のp完備化を一意に経由する。
pの素数性、源の完備性、生成族の有限性や非空性は要求しない。 -/
theorem existsUnique_compatibleRootFamilyCompletionLift
    (ρ : σ → ℕ → R) (hρ : ∀ s n, ρ s (n + 1) ^ p = ρ s n)
    {T : Type u} [CommRing T] [IsReduced T]
    [IsAdicComplete (Ideal.span {(p : T)}) T]
    (g : R ⧸ compatibleRootFamilyZeroIdeal ρ →+* T) :
    ∃! l : CompatibleRootFamilyCompletion p ρ →+* T,
      l.comp (compatibleRootFamilyCompletionMap p ρ) = g := by
  let f := g.comp (Ideal.Quotient.mk (compatibleRootFamilyZeroIdeal ρ))
  have hf : ∀ s, f (ρ s 0) = 0 := by
    intro s
    change g (Ideal.Quotient.mk (compatibleRootFamilyZeroIdeal ρ) (ρ s 0)) = 0
    have hz : Ideal.Quotient.mk (compatibleRootFamilyZeroIdeal ρ) (ρ s 0) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr Ideal.mem_span_range_self
    rw [hz, map_zero]
  have hK := compatibleRootFamilyIdeal_le_ker ρ hρ f hf
  let q := Ideal.Quotient.lift (compatibleRootFamilyIdeal ρ) f hK
  have hq : q.comp (compatibleRootFamilyQuotientMap ρ) = g := by
    apply Ideal.Quotient.ringHom_ext
    rfl
  let l := completionLift (R ⧸ compatibleRootFamilyIdeal ρ) T p q
  have hl : l.comp (compatibleRootFamilyCompletionMap p ρ) = g := by
    change l.comp ((algebraMap _ _).comp (compatibleRootFamilyQuotientMap ρ)) = g
    rw [← RingHom.comp_assoc, completionLift_comp, hq]
  refine ⟨l, hl, ?_⟩
  intro k hk
  apply completionLift_unique _ _ _ q k
  apply RingHom.ext
  intro x
  have hsurj : Function.Surjective (compatibleRootFamilyQuotientMap ρ) :=
    Ideal.quotientMap_surjective Function.surjective_id
  obtain ⟨s, rfl⟩ := hsurj x
  exact (RingHom.congr_fun hk s).trans (RingHom.congr_fun hq s).symm

/-- 任意perfectoid試験環への射は、全根族の商のp完備化を一意に経由する。 -/
theorem existsUnique_compatibleRootFamilyCompletionLift_to_perfectoid
    (ρ : σ → ℕ → R) (hρ : ∀ s n, ρ s (n + 1) ^ p = ρ s n)
    {T : Type u} [CommRing T] (hT : IsIntegralPerfectoid T p)
    (g : R ⧸ compatibleRootFamilyZeroIdeal ρ →+* T) :
    ∃! l : CompatibleRootFamilyCompletion p ρ →+* T,
      l.comp (compatibleRootFamilyCompletionMap p ρ) = g := by
  let := hT.isReduced T p
  let := hT.isAdicComplete T p
  exact existsUnique_compatibleRootFamilyCompletionLift ρ hρ g

omit [Fact p.Prime] in
/-- 任意根族商は、p前完備な基底からの全射によりp前完備。 -/
theorem compatibleRootFamilyQuotient_isPrecomplete (ρ : σ → ℕ → R)
    [IsPrecomplete (Ideal.span {(p : R)}) R] :
    IsPrecomplete (Ideal.span {(p : R ⧸ compatibleRootFamilyIdeal ρ)})
      (R ⧸ compatibleRootFamilyIdeal ρ) := by
  let J := compatibleRootFamilyIdeal ρ
  let Q := R ⧸ J
  have h : IsPrecomplete (Ideal.span {(p : R)}) Q :=
    isPrecomplete_of_surjective (Ideal.span {(p : R)}) J.mkQ (Submodule.mkQ_surjective J)
  have hh := (IsPrecomplete.map_algebraMap_iff
    (I := Ideal.span {(p : R)}) (S := Q) (M := Q)).mpr h
  simpa only [Ideal.map_span, Set.image_singleton, map_natCast] using hh

omit [Fact p.Prime] in
/-- 任意根族商のp完備化への具体的標準射は全射。 -/
theorem compatibleRootFamilyCompletionMap_surjective (ρ : σ → ℕ → R)
    [IsPrecomplete (Ideal.span {(p : R)}) R] :
    Function.Surjective (compatibleRootFamilyCompletionMap p ρ) := by
  let := compatibleRootFamilyQuotient_isPrecomplete (p := p) ρ
  have hc : Function.Surjective
      (algebraMap (R ⧸ compatibleRootFamilyIdeal ρ) (CompatibleRootFamilyCompletion p ρ)) :=
    AdicCompletion.of_surjective _ _
  have hq : Function.Surjective (compatibleRootFamilyQuotientMap ρ) :=
    Ideal.quotientMap_surjective Function.surjective_id
  exact hc.comp hq

/-- 候補のperfectoid性が得られれば、任意根族の具体的標準射はperfectoid化。 -/
theorem compatibleRootFamilyCompletionMap_isPerfectoidization_of_isIntegralPerfectoid
    (ρ : σ → ℕ → R) (hρ : ∀ s n, ρ s (n + 1) ^ p = ρ s n)
    (hC : IsIntegralPerfectoid (CompatibleRootFamilyCompletion p ρ) p) :
    IsPerfectoidization p (compatibleRootFamilyCompletionMap p ρ) := by
  refine ⟨hC, ?_⟩
  intro T _ hT g
  exact existsUnique_compatibleRootFamilyCompletionLift_to_perfectoid ρ hρ hT g

end SerrePositivity.BhattScholze
