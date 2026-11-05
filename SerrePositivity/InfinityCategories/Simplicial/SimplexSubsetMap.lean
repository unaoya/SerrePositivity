module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Simplicial.SimplexSubsetOrder
public import SerrePositivity.InfinityCategories.Simplicial.SimplexIntervalMap

/-! # 元の有限部分集合の単体的包含
概要：元の昇順部分集合を標準単体に含め、全高次単体と元の両端を回収する。
方針：元の昇順列挙の単体圏の射に、元の標準単体関手を適用する。
規約：元の有限部分集合そのものを使う。使われ方：元の部分集合 bead の augmentation。
-/
@[expose] public section
universe u
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Simplicial
open SerrePositivity.KST.SConstruction
open CategoryTheory _root_.Simplicial SSet

/-- 元の有限部分集合の標準単体から、同じ頂点の像を持つ標準単体への包含。 -/
def simplexSubsetMap {n : ℕ} (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card) :
    (Δ[I.card - 1] : SSet.{u}) ⟶ Δ[n] := stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Simplicial.simplexSubsetHom I hI)

/-- 元の部分集合の単体的包含は、全ての高次単体で元の昇順頂点作用を回収する。 -/
lemma simplexSubsetMap_apply {n m : ℕ} (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card)
    (s : (Δ[I.card - 1] : SSet.{u}) _⦋m⦌) (i : Fin (m + 1)) :
    (_root_.SerrePositivity.InfinityCategories.Simplicial.simplexSubsetMap I hI).app _ s i = _root_.SerrePositivity.InfinityCategories.Simplicial.simplexSubsetOrder I hI (s i) := rfl

/-- 元の部分集合の全高次単体を保つ包含は単射。 -/
instance simplexSubsetMap_mono {n : ℕ} (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card) :
    Mono (_root_.SerrePositivity.InfinityCategories.Simplicial.simplexSubsetMap.{u} I hI) := by
  let : Mono (_root_.SerrePositivity.InfinityCategories.Simplicial.simplexSubsetHom I hI) :=
    (SimplexCategory.mono_iff_injective (f := _root_.SerrePositivity.InfinityCategories.Simplicial.simplexSubsetHom I hI)).mpr
      (_root_.SerrePositivity.InfinityCategories.Simplicial.simplexSubsetOrder_injective I hI)
  exact inferInstanceAs (Mono (uliftYoneda.{u}.map (_root_.SerrePositivity.InfinityCategories.Simplicial.simplexSubsetHom I hI)))

/-- 元の部分集合の包含の始頂点は、元の最小元の同じ零単体。 -/
lemma simplexSubsetMap_first {n : ℕ} (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card) :
    (_root_.SerrePositivity.InfinityCategories.Simplicial.simplexSubsetMap.{u} I hI).app _ (_root_.SerrePositivity.InfinityCategories.Simplicial.standardSimplexVertex 0) =
      _root_.SerrePositivity.InfinityCategories.Simplicial.standardSimplexVertex (I.min' (Finset.card_pos.mp (by omega))) :=
  _root_.SerrePositivity.InfinityCategories.Simplicial.standardSimplexVertex_ext (_root_.SerrePositivity.InfinityCategories.Simplicial.simplexSubsetOrder_first I hI)

/-- 元の部分集合の包含の終頂点は、元の最大元の同じ零単体。 -/
lemma simplexSubsetMap_last {n : ℕ} (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card) :
    (_root_.SerrePositivity.InfinityCategories.Simplicial.simplexSubsetMap.{u} I hI).app _ (_root_.SerrePositivity.InfinityCategories.Simplicial.standardSimplexVertex (Fin.last (I.card - 1))) =
      _root_.SerrePositivity.InfinityCategories.Simplicial.standardSimplexVertex (I.max' (Finset.card_pos.mp (by omega))) :=
  _root_.SerrePositivity.InfinityCategories.Simplicial.standardSimplexVertex_ext (_root_.SerrePositivity.InfinityCategories.Simplicial.simplexSubsetOrder_last I hI)

end SerrePositivity.InfinityCategories.Simplicial

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Simplicial.simplexSubsetMap (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.simplexSubsetMap := _root_.SerrePositivity.InfinityCategories.Simplicial.simplexSubsetMap

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.simplexSubsetMap_apply := _root_.SerrePositivity.InfinityCategories.Simplicial.simplexSubsetMap_apply

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.simplexSubsetMap_first := _root_.SerrePositivity.InfinityCategories.Simplicial.simplexSubsetMap_first

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.simplexSubsetMap_last := _root_.SerrePositivity.InfinityCategories.Simplicial.simplexSubsetMap_last

@[deprecated _root_.SerrePositivity.InfinityCategories.Simplicial.simplexSubsetMap_mono (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.simplexSubsetMap_mono := _root_.SerrePositivity.InfinityCategories.Simplicial.simplexSubsetMap_mono

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.simplexSubsetMap_first._proof_2 := _root_.SerrePositivity.InfinityCategories.Simplicial.simplexSubsetMap_first._proof_2
