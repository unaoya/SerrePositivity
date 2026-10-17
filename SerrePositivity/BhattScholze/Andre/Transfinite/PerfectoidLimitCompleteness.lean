module

public import SerrePositivity.BhattScholze.Andre.Transfinite.CountableCompletion
public import SerrePositivity.CommutativeAlgebra.IntegralPerfectoid
public import SerrePositivity.CommutativeAlgebra.CompletelyFaithfullyFlatInjective
/-! # 完全忠実平坦な perfectoid 塔の非可算極限の完備性

BS Thm 7.14（著者版 p.61）。p ねじれを許す既存の単射性定理と
可算データの降下を結び、極限環が自動的に p 進完備であることを示す。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Andre.Transfinite
/-- ## 概要
perfectoid 環からの p 完全忠実平坦な環準同型は単射である。
BS Thm 7.14（著者版 p.61）の塔を単射な系として扱うための入口。

## 方針
非零の場合は p 進分離性と各冪剰余の忠実平坦性による既存の単射性定理を適用する。
零環の場合は元の一意性を使う。

## 規約
S の完備性、perfectoid 性、p 正則性は不要。作用は φ.toAlgebra そのもの。

## 使われ方
非可算共終性の極限での自動的な完備性を perfectoid 塔へ適用する。
-/
theorem injective_of_perfectoid_completelyFaithfullyFlat {R S : Type u} [CommRing R] [CommRing S]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (φ : R →+* S)
    (hφ : let := φ.toAlgebra; IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) S) :
    Function.Injective φ := by
  rcases hR with hsub | ⟨_, hc, _⟩
  · exact fun _ _ _ ↦ hsub.elim _ _
  · let := hc
    let := φ.toAlgebra
    exact algebraMap_injective_of_completelyFaithfullyFlat_of_isHausdorff R S (p : R) hφ

/-- ## 概要
perfectoid 環の p 完全忠実平坦な有向系で、可算添字集合がすべて上界を持つなら、
余極限は p 進完備である。BS Thm 7.14（著者版 p.61）の非可算共終性の極限段。

## 方針
各段の完備性を定義から取り出し、完全忠実平坦性から遷移射の単射性を導いて、
可算データの降下による完備性定理を適用する。

## 規約
p ねじれと零環を許す。環と添字は Type u。Fontaine 核の単項性と極限写像の
完全忠実平坦性は、この定理の結論には含めない。

## 使われ方
ω₁ の終段や非可算共終性の極限段で、完備化を挟まず完備な環を得る。
-/
theorem isAdicComplete_directLimit_of_perfectoid_completelyFaithfullyFlat
    {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    (R : ι → Type u) [∀ i, CommRing (R i)]
    (f : ∀ i j, i ≤ j → R i →+* R j)
    [DirectedSystem R (fun i j h ↦ f i j h)]
    (p : ℕ) [Fact p.Prime]
    (hR : ∀ i, IsIntegralPerfectoid (R i) p)
    (hflat : ∀ i j h, let := (f i j h).toAlgebra;
      IsCompletelyFaithfullyFlat (Ideal.span {(p : R i)}) (R j))
    (hbound : ∀ s : Set ι, s.Countable → ∃ j, ∀ i ∈ s, i ≤ j) :
    IsAdicComplete (Ideal.span {(p : Ring.DirectLimit R (fun i j h ↦ f i j h))})
      (Ring.DirectLimit R (fun i j h ↦ f i j h)) := by
  have hc (i : ι) : IsAdicComplete (Ideal.span {(p : R i)}) (R i) := by
    rcases hR i with hsub | ⟨_, hc, _⟩
    · let := hsub
      infer_instance
    · exact hc
  let (i : ι) : IsAdicComplete (Ideal.span {(p : R i)}) (R i) := hc i
  apply isAdicComplete_directLimit_of_countable_upperBound R f p hbound
  intro i j h
  exact injective_of_perfectoid_completelyFaithfullyFlat p (hR i) (f i j h) (hflat i j h)
end SerrePositivity.BhattScholze.Andre.Transfinite
