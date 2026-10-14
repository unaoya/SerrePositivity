module

public import SerrePositivity.CommutativeAlgebra.IntegralPerfectoid

/-! # semiperfectoid環のperfectoid化の全射性（文献入力）

Bhatt–Scholze, Prisms and prismatic cohomology, Corollary 7.3 / Theorem 7.4。
ここではpねじれのない、古典的にp進完備な商への適用形を引用する。
この場合、古典的p進完備性と導来p進完備性が一致し、Notation 7.1の条件を満たす。
この完備性の同値も引用境界に含め、導来prismatic構成を形式化したとは扱わない。
原典の選択による全射対象を引用し、任意の普遍対象への移送は別に証明する。

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
  sorry

end SerrePositivity.BhattScholze.Inputs
