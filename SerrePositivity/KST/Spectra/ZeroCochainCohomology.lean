module

public import SerrePositivity.KST.Spectra.RepresentationCochainComparison
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

/-!
概要：線形な非斉次余単体 cochain の零次数コホモロジーと不変部分の比較。
方針：複体の同型による群コホモロジーの比較に標準の H⁰ の不変部分表示を合成する。
規約：有限性や標数零を要求しない。
使われ方：Goerss–Jardine VIII §2。有理自明作用で残る零次数の代数的な係数の計算。
-/

@[expose] public section

universe u

open CategoryTheory

namespace SerrePositivity.KST.Spectra.LinearGroupCochains

noncomputable section

variable {k G : Type u} [CommRing k] [Group G]

/-- 概要：余単体 cochain の零次数コホモロジーは表現の不変部分と同型。
方針：群コホモロジーの比較と H⁰ の不変部分の同型を合成する。
規約：任意の群と係数環について成立する。
使われ方：Goerss–Jardine VIII §2。零次数に残る係数の表示。 -/
def zeroCohomologyIso (A : Rep.{u} k G) :
    (complex A).homology 0 ≅ ModuleCat.of k A.ρ.invariants :=
  cohomologyIso A 0 ≪≫ groupCohomology.H0Iso A

/-- 概要：自明な作用では余単体 cochain の零次数コホモロジーは元の係数と同型。
方針：複体の比較と自明作用の H⁰ の同型を合成する。
規約：有限性や有理性を必要としない零次数の代数的な主張。
使われ方：Goerss–Jardine VIII §2。有理 Shapiro の Tot の計算への零次数の入力。 -/
def zeroCohomologyIsoOfTrivial (A : Rep.{u} k G) [A.IsTrivial] :
    (complex A).homology 0 ≅ ModuleCat.of k A :=
  cohomologyIso A 0 ≪≫ groupCohomology.H0IsoOfIsTrivial A

end

end SerrePositivity.KST.Spectra.LinearGroupCochains
