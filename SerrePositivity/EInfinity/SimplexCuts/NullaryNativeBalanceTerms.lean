module

public import SerrePositivity.EInfinity.SimplexCuts.NullaryNativeInputData
public import SerrePositivity.EInfinity.SimplexCuts.NullaryCanonicalBalanceTerms
public import SerrePositivity.EInfinity.Surjection.CompositionBoundaryCases

/-!
# 元の全分割の空語合成項と全二段項

Berger–Fresse §1.2.4・§2.2.6、M14 L12a、報告 §373。
元の係数の合成符号とraw語の正規化を保持し、実際の空語代入と合わせる。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory
open SerrePositivity.TensorPowers
open scoped Simplicial

/-- 元の全分割の合成符号とraw合成語の同じ正規化Cut項（BF §1.2.4・§2.2.6）。 -/
def nullaryNativeCompositeTerm (A : Type u) [CommRing A] (S : SSet.{0}) {m d : ℕ}
    (u : Surjection.BasisWord (m + 2) d) (ν : Surjection.BasisWord 0 0) (k : Fin (m + 2))
    (q : ℕ)
    (c : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) 0 × Cut (m + d) q)
    (x : S _⦋q⦌) : (power (chains A S) (m + 1)).X (-((d + q : ℕ) : ℤ)) :=
  if h : Surjection.Nondegenerate (IntervalCuts.nullaryRawWord u ν k c.1) then
    let w : Surjection.BasisWord (m + 1) d :=
      ⟨IntervalCuts.nullaryRawWord u ν k c.1, IntervalCuts.nullaryRawWord_surjective u ν k c.1, h⟩
    Surjection.compositionSign u ν k c.1 •
      nullarySmallCutTerm A S (positiveWord w) x (-((d + q : ℕ) : ℤ)) (by omega) c.2
  else 0

/-- 元の全大Cutの実際の二段項を同じ語長で読む（BF §2.2.6）。 -/
def nullaryNativeOuterTerm (A : Type u) [CommRing A] (S : SSet.{0}) {m d : ℕ}
    (u : Surjection.BasisWord (m + 2) d) (ν : Surjection.BasisWord 0 0) (k : Fin (m + 2))
    (q : ℕ) (s : Cut ((m + d) + 1) q) (x : S _⦋q⦌) :
    (power (chains A S) (m + 1)).X (-((d + q : ℕ) : ℤ)) :=
  nullaryOuterCutTerm A S (nullaryNativeOuterWord u) ν k x (-((d + q : ℕ) : ℤ)) (by omega) s

/-- 元の合成側の項と、負号付きの元の二段側の項（BF §2.2.6）。 -/
def nullaryNativeBalanceTerm (A : Type u) [CommRing A] (S : SSet.{0}) {m d : ℕ}
    (u : Surjection.BasisWord (m + 2) d) (ν : Surjection.BasisWord 0 0) (k : Fin (m + 2))
    (q : ℕ) (i : NullaryNativeBalanceIndex u k q) (x : S _⦋q⦌) :
    (power (chains A S) (m + 1)).X (-((d + q : ℕ) : ℤ)) :=
  matchedSubsetBalanceTerm (fun c => nullaryNativeCompositeTerm A S u ν k q c x)
    (fun s => nullaryNativeOuterTerm A S u ν k q s x) i

end SerrePositivity.EInfinity.SimplexCuts
