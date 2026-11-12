module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import Mathlib.Data.Finset.Sort
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex

/-! # 元の有限部分集合の昇順単体
概要：元の有限部分集合を全ての頂点を保つ昇順列挙として、元の単体圏の射にする。
方針：元の orderEmbOfFin を同じ濃度の標準単体の頂点に使う。
規約：濃度二以上の HA 添字集合。使われ方：元の部分集合 bead と HA 成分。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
open _root_.SerrePositivity.KST.SConstruction
open CategoryTheory _root_.Simplicial

/-- 元の有限部分集合の全頂点を、同じ昇順の標準単体から列挙する単調写像。 -/
def simplexSubsetOrder {n : ℕ} (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card) :
    Fin (I.card - 1 + 1) →o Fin (n + 1) :=
  (I.orderEmbOfFin (show I.card = I.card - 1 + 1 by omega)).toOrderHom

/-- 元の昇順単体の全頂点は、元の同じ部分集合に属する。 -/
lemma simplexSubsetOrder_mem {n : ℕ} (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card)
    (v : Fin (I.card - 1 + 1)) : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder I hI v ∈ I :=
  I.orderEmbOfFin_mem (show I.card = I.card - 1 + 1 by omega) v

/-- 元の昇順単体は全頂点で単射。 -/
lemma simplexSubsetOrder_injective {n : ℕ} (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card) :
    Function.Injective (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder I hI) :=
  (I.orderEmbOfFin (show I.card = I.card - 1 + 1 by omega)).injective

/-- 元の昇順単体の始頂点は、元の部分集合の最小元。 -/
lemma simplexSubsetOrder_first {n : ℕ} (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder I hI 0 = I.min' (Finset.card_pos.mp (by omega)) :=
  Finset.orderEmbOfFin_zero (show I.card = I.card - 1 + 1 by omega) (by omega)

/-- 元の昇順単体の終頂点は、元の部分集合の最大元。 -/
lemma simplexSubsetOrder_last {n : ℕ} (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder I hI (Fin.last (I.card - 1)) = I.max' (Finset.card_pos.mp (by omega)) :=
  Finset.orderEmbOfFin_last (show I.card = I.card - 1 + 1 by omega) (by omega)

/-- 元の昇順単体の頂点の像は、元の部分集合全体そのもの。 -/
lemma simplexSubsetOrder_range {n : ℕ} (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card) :
    Set.range (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder I hI) = I :=
  I.range_orderEmbOfFin (show I.card = I.card - 1 + 1 by omega)

/-- 元の有限部分集合の昇順列挙を、元の標準単体圏の射として読む。 -/
def simplexSubsetHom {n : ℕ} (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card) :
    ⦋I.card - 1⦌ ⟶ ⦋n⦌ := SimplexCategory.Hom.mk (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder I hI)

end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetHom (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.simplexSubsetHom := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetHom

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.simplexSubsetOrder := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.simplexSubsetOrder_first := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder_first

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.simplexSubsetOrder_injective := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder_injective

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.simplexSubsetOrder_last := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder_last

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.simplexSubsetOrder_mem := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder_mem

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.simplexSubsetOrder_range := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder_range

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.simplexSubsetOrder._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.simplexSubsetOrder_first._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder_first._proof_2
