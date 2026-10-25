module

public import SerrePositivity.BhattScholze.Results.SemiperfectoidSurjectivity

/-! # semiperfectoid全射性の証明済み互換入口

Bhatt–Scholze著者公開版Corollary 7.3 / Theorem 7.4の、pねじれのない古典的p進完備商への旧適用形。
任意perfectoid源の導来p完備全射商に対する一般全射性とB3の存在・普遍性から証明する。
古典的/導来完備性の比較は既存共通APIを使用する。公開署名を維持し、文献入力のsorryは解消済み。

出典：https://people.mpim-bonn.mpg.de/scholze/prisms.pdf （§7.1、印刷pp.55–56）。
-/

public section
universe u
namespace SerrePositivity.BhattScholze.Inputs

/-- BS Cor 7.3 / Thm 7.4のpねじれのない完備商への適用形。 -/
theorem exists_surjective_perfectoidization_of_complete_torsionFree_quotient
    (R S : Type u) [CommRing R] [CommRing S] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) (q : R →+* S) (hq : Function.Surjective q)
    [IsAdicComplete (Ideal.span {(p : S)}) S]
    (hp : Function.Injective (fun x : S ↦ (p : S) * x)) :
    ∃ (C : Type u) (_ : CommRing C) (f : S →+* C),
      IsPerfectoidization p f ∧ Function.Surjective f := by
  exact BhattScholze.exists_surjective_perfectoidization_of_semiperfectoid_quotient hR q hq
    ((DerivedCompletion.isModuleComplete_iff_isAdicComplete_of_regular S (p : S)
      (ModuleCat.of S S) hp).mpr inferInstance)

end SerrePositivity.BhattScholze.Inputs
