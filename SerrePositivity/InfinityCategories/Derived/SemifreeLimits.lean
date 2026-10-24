module
public import SerrePositivity.InfinityCategories.DGNerve.FullFiberSquare
public import SerrePositivity.InfinityCategories.DGNerve.FullZeroObject
public import SerrePositivity.InfinityCategories.Derived.SemifreeClosure
public import SerrePositivity.InfinityCategories.Derived.SemifreeSubcategory

/-! # Semifree 複体の dg nerve の零対象と標準引き戻し

概要：Semifree 複体の dg nerve は零対象と標準 fiber による引き戻しを持つ。
方針：記録済みの D2h・D2h′ の零・有限直和・fiber の閉性を充満部分圏への制限に適用する。
規約：HTT §1.2.13、HA §1.3.1。使われ方：D(S) の D4 の標準引き戻しと零対象。
-/

@[expose] public section
noncomputable section

universe u

namespace SerrePositivity.InfinityCategories.DGNerve

open CategoryTheory MonoidalCategory DifferentialGraded
open scoped Simplicial ZeroObject

variable (A : Type u) [CommRing A]

/-- 概要：Semifree の零複体の頂点は終対象。
方針：D2h の零複体の閉性と充満部分圏での零終対象の定理を使う。
規約：HTT §1.2.12。使われ方：導来 ∞ 圏の空図式の極限。 -/
lemma isTerminalVertex_semifree_zero :
    IsTerminalVertex (X := dgNerve A (Semifree A))
      (Simplex.vertex (⟨0, complexSemifree_zero A⟩ : Semifree A)) :=
  isTerminalVertex_full_zero A (complexSemifree A) (complexSemifree_zero A)

/-- 概要：Semifree の零複体の頂点は始対象。
方針：D2h の零複体の閉性と充満部分圏での零始対象の定理を使う。
規約：HTT §1.2.12 の双対。使われ方：導来 ∞ 圏の零対象。 -/
lemma isInitialVertex_semifree_zero :
    IsInitialVertex (X := dgNerve A (Semifree A))
      (Simplex.vertex (⟨0, complexSemifree_zero A⟩ : Semifree A)) :=
  isInitialVertex_full_zero A (complexSemifree A) (complexSemifree_zero A)

variable {A} {B C D : Complex A}

/-- 概要：Semifree 複体 B,C,D の cospan に対する標準 fiber 四角形を Semifree の内部に構成する。
方針：D2h′ の有限直和と fiber の閉性で標準 fiber の所属を得て、充満部分圏の四角形を作る。
規約：標準 fiber は mapping cone の −1 シフト。使われ方：導来 ∞ 圏の明示的な引き戻し。 -/
def semifreeFiberSquare (g : B ⟶ D) (h : C ⟶ D)
    (hB : complexSemifree A B) (hC : complexSemifree A C) (hD : complexSemifree A D) :
    (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ dgNerve A (Semifree A) :=
  fullFiberSquare (complexSemifree A) g h hB hC hD
    (complexSemifree_biprodFiber A (fiberDifference g h) hB hC hD)

/-- 概要：Semifree の標準 fiber 四角形は dg nerve の ∞ 引き戻し四角形。
方針：D2h′ の閉性で充満部分圏への制限の前提を満たし、周囲での引き戻し性を反映する。
規約：任意の可換環と非有界 Semifree 複体。使われ方：D4 と有限極限の標準モデル。 -/
lemma semifreeFiberSquare_isPullback (g : B ⟶ D) (h : C ⟶ D)
    (hB : complexSemifree A B) (hC : complexSemifree A C) (hD : complexSemifree A D) :
    IsPullbackSquare (semifreeFiberSquare g h hB hC hD) :=
  fullFiberSquare_isPullback (complexSemifree A) g h hB hC hD
    (complexSemifree_biprodFiber A (fiberDifference g h) hB hC hD)

/-- 概要：Semifree 内の標準 fiber 四角形の包含像は全複体の標準四角形。
方針：一般の充満部分圏の包含像の式を適用する。
規約：HTT §1.2.13。使われ方：D4 の周囲の複体との比較。 -/
lemma semifreeFiberSquare_inclusion (g : B ⟶ D) (h : C ⟶ D)
    (hB : complexSemifree A B) (hC : complexSemifree A C) (hD : complexSemifree A D) :
    semifreeFiberSquare g h hB hC hD ≫
        dgNerve.map (dgFullSubcategoryInclusion A (Complex A) (complexSemifree A)) =
      standardFiberSquare g h :=
  fullFiberSquare_inclusion (complexSemifree A) g h hB hC hD
    (complexSemifree_biprodFiber A (fiberDifference g h) hB hC hD)

end SerrePositivity.InfinityCategories.DGNerve
