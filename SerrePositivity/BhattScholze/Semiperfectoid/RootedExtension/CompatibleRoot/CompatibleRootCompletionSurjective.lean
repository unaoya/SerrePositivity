module

public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.CompatibleRoot.CompatibleRootPerfectoidUniversal
public import SerrePositivity.CommutativeAlgebra.AdicCompleteness

/-! # B4-2：根イデアル商のp完備化への標準射の全射性

商の前完備性を既存の全射移送から供給する。
根イデアルの閉性・商の分離性・有限生成性を仮定しない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze
variable {p : ℕ} {R : Type u} [CommRing R]

/-- p前完備な環の根イデアル商は、自身のp作用について前完備。 -/
theorem compatibleRootQuotient_isPrecomplete (ρ : ℕ → R)
    [IsPrecomplete (Ideal.span {(p : R)}) R] :
    IsPrecomplete (Ideal.span {(p : R ⧸ compatibleRootIdeal ρ)})
      (R ⧸ compatibleRootIdeal ρ) := by
  let J := compatibleRootIdeal ρ
  let Q := R ⧸ J
  have h : IsPrecomplete (Ideal.span {(p : R)}) Q :=
    isPrecomplete_of_surjective (Ideal.span {(p : R)}) J.mkQ (Submodule.mkQ_surjective J)
  have hh := (IsPrecomplete.map_algebraMap_iff (I := Ideal.span {(p : R)}) (S := Q) (M := Q)).mpr h
  simpa only [Ideal.map_span, Set.image_singleton, map_natCast] using hh

/-- 根イデアル商からそのp完備化への標準射は全射。 -/
theorem compatibleRootCompletion_algebraMap_surjective (ρ : ℕ → R)
    [IsPrecomplete (Ideal.span {(p : R)}) R] :
    Function.Surjective
      (algebraMap (R ⧸ compatibleRootIdeal ρ) (CompatibleRootCompletion p ρ)) := by
  let := compatibleRootQuotient_isPrecomplete (p := p) ρ
  exact AdicCompletion.of_surjective _ _

/-- 最初の元の商から根イデアル商の完備化への具体的な射は全射。 -/
theorem compatibleRootCompletionMap_surjective (ρ : ℕ → R)
    [IsPrecomplete (Ideal.span {(p : R)}) R] :
    Function.Surjective (compatibleRootCompletionMap p ρ) :=
  (compatibleRootCompletion_algebraMap_surjective (p := p) ρ).comp
    (compatibleRootQuotientMap_surjective ρ)

/-- perfectoid基底の根付き商では、候補のperfectoid性があれば任意のperfectoid化は全射。 -/
theorem surjective_of_isPerfectoidization_of_compatibleRoots
    [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (ρ : ℕ → R) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n)
    (hC : IsIntegralPerfectoid (CompatibleRootCompletion p ρ) p)
    {C : Type u} [CommRing C] (f : R ⧸ Ideal.span {ρ 0} →+* C)
    (hf : IsPerfectoidization p f) : Function.Surjective f := by
  let := hR.isAdicComplete R p
  have h := compatibleRootCompletionMap_isPerfectoidization_of_isIntegralPerfectoid ρ hρ hC
  exact (h.surjective_iff p hf).mp (compatibleRootCompletionMap_surjective ρ)

end SerrePositivity.BhattScholze
