module

public import SerrePositivity.BhattScholze.Semiperfectoid.AndreSurjectivity
public import SerrePositivity.BhattScholze.Semiperfectoid.SemiperfectoidPerfectoidization
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.AdicComparison

/-! # B4：導来p完備なperfectoid環の全射商の普遍perfectoid化は全射

## 概要
BS 著者版 Thm 7.4。perfectoid 環 R の導来 p 完備な全射商 S の任意の perfectoid 化は全射。

## 方針
原典どおり、André の補題（Thm 7.14、証明済み）で絶対整閉な perfectoid 環 T へ
p 完全忠実平坦に拡大する。T では核の全元が両立する p 冪根を持つので全射性が出て、
それを R へ降下する（`Semiperfectoid/AndreSurjectivity`）。

## 規約
p ねじれなし・有限性・古典的完備性は仮定しない。André を使わない別証明は
`Semiperfectoid/RootEnvelope/RootEnvelopeSurjectivity`。

## 使われ方
CLMST、`Almost/PerfectoidIdealLemma103`、`Perfectoidization/Prop813PerfectoidBaseChange`、
`Semiperfectoid/PerfectoidizationSurjectiveMap`、`Inputs/SemiperfectoidSurjectivity` で使う。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {R S C : Type u}
variable [CommRing R] [CommRing S] [CommRing C]

/-- 任意perfectoid環の導来p完備な全射商の、任意の普遍perfectoid化は全射。
pねじれのない商・有限性・古典的完備性は仮定しない。証明は André の補題経由。 -/
theorem surjective_of_isPerfectoidization_of_semiperfectoid_quotient
    (hR : IsIntegralPerfectoid R p) (q : R →+* S) (hq : Function.Surjective q)
    (hS : DerivedCompletion.IsModuleComplete S (p : S) (ModuleCat.of S S))
    (f : S →+* C) (hf : IsPerfectoidization p f) : Function.Surjective f :=
  surjective_of_isPerfectoidization_of_andre R S C p hR q hq hS f hf

/-- B3の一般存在・普遍性とB4により、一般の導来p完備商は全射perfectoid化を持つ。 -/
theorem exists_surjective_perfectoidization_of_semiperfectoid_quotient
    (hR : IsIntegralPerfectoid R p) (q : R →+* S) (hq : Function.Surjective q)
    (hS : DerivedCompletion.IsModuleComplete S (p : S) (ModuleCat.of S S)) :
    ∃ (C : Type u) (_ : CommRing C) (f : S →+* C),
      IsPerfectoidization p f ∧ Function.Surjective f := by
  obtain ⟨C, hC, f, hf⟩ := exists_perfectoidization_of_semiperfectoid_quotient hR q hq hS
  let := hC
  exact ⟨C, hC, f, hf,
    surjective_of_isPerfectoidization_of_semiperfectoid_quotient hR q hq hS f hf⟩

/-- 古典的p進完備な商への互換入口。共通の比較により商のp正則性は不要。 -/
theorem surjective_of_isPerfectoidization_of_adic_complete_quotient
    (hR : IsIntegralPerfectoid R p) (q : R →+* S) (hq : Function.Surjective q)
    [IsAdicComplete (Ideal.span {(p : S)}) S]
    (f : S →+* C) (hf : IsPerfectoidization p f) : Function.Surjective f :=
  surjective_of_isPerfectoidization_of_semiperfectoid_quotient hR q hq
    (DerivedCompletion.isModuleComplete_of_isAdicComplete S (p : S) (ModuleCat.of S S)) f hf

end SerrePositivity.BhattScholze
