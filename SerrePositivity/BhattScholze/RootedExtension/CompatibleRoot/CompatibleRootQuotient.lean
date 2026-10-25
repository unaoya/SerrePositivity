module

public import SerrePositivity.BhattScholze.RootedExtension.CompatibleRoot.CompatibleRootIdeal
public import SerrePositivity.CommutativeAlgebra.PerfectoidizationCompletion

/-! # 根イデアル商と完備化の制限付き普遍性

著者公開版Theorem 7.4の単項・根を持つ場合に向けた部分定理。
試験環の被約性を明示し、候補のperfectoid性と完備化射の全射性は結論しない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze
variable {p : ℕ} {R : Type u} [CommRing R]

/-- 最初の元の商から、すべての根の商への標準射。 -/
def compatibleRootQuotientMap (ρ : ℕ → R) :
    R ⧸ Ideal.span {ρ 0} →+* R ⧸ compatibleRootIdeal ρ :=
  Ideal.quotientMap _ (RingHom.id R) (span_root_zero_le_compatibleRootIdeal ρ)

/-- 標準商射の代表元公式。 -/
@[simp] theorem compatibleRootQuotientMap_mk (ρ : ℕ → R) (r : R) :
    compatibleRootQuotientMap ρ (Ideal.Quotient.mk _ r) =
      Ideal.Quotient.mk (compatibleRootIdeal ρ) r := rfl

/-- 完備化前の標準商射は全射。 -/
theorem compatibleRootQuotientMap_surjective (ρ : ℕ → R) :
    Function.Surjective (compatibleRootQuotientMap ρ) :=
  Ideal.quotientMap_surjective Function.surjective_id

/-- 被約環への射は根イデアル商を一意に経由する。 -/
theorem existsUnique_compatibleRootQuotientLift
    (ρ : ℕ → R) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n)
    {T : Type u} [CommRing T] [IsReduced T] (g : R ⧸ Ideal.span {ρ 0} →+* T) :
    ∃! l : R ⧸ compatibleRootIdeal ρ →+* T, l.comp (compatibleRootQuotientMap ρ) = g := by
  let f := g.comp (Ideal.Quotient.mk (Ideal.span {ρ 0}))
  have hK : compatibleRootIdeal ρ ≤ RingHom.ker f :=
    compatibleRootIdeal_le_ker_of_root_zero ρ hρ f (by
      change g (Ideal.Quotient.mk _ (ρ 0)) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _), map_zero])
  let l := Ideal.Quotient.lift (compatibleRootIdeal ρ) f hK
  have hl : l.comp (compatibleRootQuotientMap ρ) = g := by
    apply Ideal.Quotient.ringHom_ext
    rfl
  refine ⟨l, hl, ?_⟩
  intro k hk
  apply RingHom.ext
  intro x
  obtain ⟨s, rfl⟩ := compatibleRootQuotientMap_surjective ρ x
  exact (RingHom.congr_fun hk s).trans (RingHom.congr_fun hl s).symm

/-- 根イデアル商をp進完備化した具体的候補。 -/
abbrev CompatibleRootCompletion (p : ℕ) (ρ : ℕ → R) :=
  AdicCompletion (Ideal.span {(p : R ⧸ compatibleRootIdeal ρ)})
    (R ⧸ compatibleRootIdeal ρ)

/-- 最初の元の商から、根イデアル商のp進完備化への具体的な射。 -/
def compatibleRootCompletionMap (p : ℕ) (ρ : ℕ → R) :
    R ⧸ Ideal.span {ρ 0} →+* CompatibleRootCompletion p ρ :=
  (algebraMap (R ⧸ compatibleRootIdeal ρ) (CompatibleRootCompletion p ρ)).comp
    (compatibleRootQuotientMap ρ)

/-- 被約なp進完備環への射は、具体的な完備化候補を一意に経由する。
試験環は一般perfectoid環とは同定せず、被約性と完備性を明示する。 -/
theorem existsUnique_compatibleRootCompletionLift
    (ρ : ℕ → R) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n)
    {T : Type u} [CommRing T] [IsReduced T]
    [IsAdicComplete (Ideal.span {(p : T)}) T] (g : R ⧸ Ideal.span {ρ 0} →+* T) :
    ∃! l : CompatibleRootCompletion p ρ →+* T,
      l.comp (compatibleRootCompletionMap p ρ) = g := by
  obtain ⟨f, hf, hfu⟩ := existsUnique_compatibleRootQuotientLift ρ hρ g
  let l := completionLift (R ⧸ compatibleRootIdeal ρ) T p f
  have hl : l.comp (algebraMap (R ⧸ compatibleRootIdeal ρ) (CompatibleRootCompletion p ρ)) = f :=
    completionLift_comp _ _ _ f
  refine ⟨l, ?_, ?_⟩
  · change l.comp ((algebraMap _ _).comp (compatibleRootQuotientMap ρ)) = g
    rw [← RingHom.comp_assoc, hl, hf]
  · intro k hk
    apply completionLift_unique _ _ _ f k
    apply hfu
    change (k.comp (algebraMap _ _)).comp (compatibleRootQuotientMap ρ) = g
    rw [RingHom.comp_assoc]
    exact hk

end SerrePositivity.BhattScholze
