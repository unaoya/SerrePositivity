module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.CAlgHoLocalization
public import SerrePositivity.EInfinity.BarrattEccles.Theory.HomologyAlgebraFunctor

/-!
# Barratt–Eccles CAlg の π₀

## 概要
Berger–Fresse §1 の厳密代数の H⁰ を、CAlg のホモトピー圏の通常関手にする。

## 方針
全厳密代数の弱同値が H⁰ の同型になることから、通常の局所化の普遍性を使う。

## 規約
値は基礎環の下の可換環とし、厳密な H⁰ との比較を与える。

## 使われ方
BS 著者版 Theorem 6.2 の `pi0` 欄。
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory SSet
open SerrePositivity.InfinityCategories

variable (A : Type u) [CommRing A]

/-- 厳密代数の H⁰ を基礎環の下の可換環として取る関手。 -/
abbrev strictPiZero : (operad A).Algebra ⥤ RingAlgebra A :=
  homologyAlgebraFunctor A ⋙ (commAlgCatEquivUnder (CommRingCat.of A)).functor

/-- 厳密代数の H⁰ は全ての擬同型を反転する。 -/
lemma strictPiZero_inverts :
    (ordinaryAlgebraWeak A).IsInvertedBy (strictPiZero A) := by
  intro X Y g hg
  have : QuasiIso g.hom := hg
  have := homologyAlgebraFunctor_map_isIso g
  exact Functor.map_isIso (commAlgCatEquivUnder (CommRingCat.of A)).functor
    ((homologyAlgebraFunctor A).map g)

/-- CAlg のホモトピー圏上の、基礎環の下の可換環に値を取る π₀。 -/
def barrattEcclesPi0 : (CAlg_R A).HomotopyCategory ⥤ RingAlgebra A :=
  letI := ordinaryAlgebraHoSource_isLocalization A
  Localization.lift (strictPiZero A) (strictPiZero_inverts A) (ordinaryAlgebraHoSource A)

/-- π₀ を全厳密代数の源に引き戻すと、通常の H⁰ の代数になる。 -/
def barrattEcclesPi0_sourceIso :
    ordinaryAlgebraHoSource A ⋙ barrattEcclesPi0 A ≅ strictPiZero A :=
  letI := ordinaryAlgebraHoSource_isLocalization A
  Localization.fac (strictPiZero A) (strictPiZero_inverts A) (ordinaryAlgebraHoSource A)

end SerrePositivity.EInfinity.BarrattEccles
