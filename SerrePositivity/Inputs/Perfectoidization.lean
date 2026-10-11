module

public import SerrePositivity.CommutativeAlgebra.IntegralPerfectoid
public import Mathlib.RingTheory.Finiteness.Basic

/-! # 有限代数の perfectoid 化の存在（文献からの引用）

Bhatt–Scholze, *Prisms and prismatic cohomology*, Ann. of Math. 196 (2022),
1135–1275, Theorem 10.11 と Proposition 8.5 による存在と普遍性。
CLMST §2.4 (3)(4) と Notation 4.0.1 に記載された有限・有限表示の場合を使う。
出典：https://arxiv.org/html/2209.04046v4
引用の形はこれらを合わせた系である。有限代数の `p` 進完備化に存在定理を適用し、
完備な perfectoid 環への写像が完備化を一意に経由することにより、
完備化前の有限代数からの普遍写像として記す。
長さの性質はこの引用には含めない。
-/

public section

universe u

namespace SerrePositivity.Inputs

/-- Perfectoid 環上の有限かつ有限表示な代数は、環としての perfectoid 化を持つ。
引用：Bhatt–Scholze Theorem 10.11、Proposition 8.5、CLMST Notation 4.0.1。 -/
theorem exists_perfectoidization_of_finite
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] [Algebra.FinitePresentation R S]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p) :
    ∃ (C : Type u) (_ : CommRing C) (f : S →+* C), IsPerfectoidization p f := by
  sorry

end SerrePositivity.Inputs
