module
public import SerrePositivity.KST.SConstruction.SimplexSubsetOrder
public import SerrePositivity.KST.SConstruction.SimplexIntervalMap

/-! # 元の有限部分集合の単体的包含
概要：元の昇順部分集合を標準単体に含め、全高次単体と元の両端を回収する。
方針：元の昇順列挙の単体圏の射に、元の標準単体関手を適用する。
規約：元の有限部分集合そのものを使う。使われ方：元の部分集合 bead の augmentation。
-/
@[expose] public section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Simplicial SSet

/-- 元の有限部分集合の標準単体から、同じ頂点の像を持つ標準単体への包含。 -/
def simplexSubsetMap {n : ℕ} (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card) :
    (Δ[I.card - 1] : SSet.{u}) ⟶ Δ[n] := stdSimplex.map (simplexSubsetHom I hI)

/-- 元の部分集合の単体的包含は、全ての高次単体で元の昇順頂点作用を回収する。 -/
lemma simplexSubsetMap_apply {n m : ℕ} (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card)
    (s : (Δ[I.card - 1] : SSet.{u}) _⦋m⦌) (i : Fin (m + 1)) :
    (simplexSubsetMap I hI).app _ s i = simplexSubsetOrder I hI (s i) := rfl

/-- 元の部分集合の全高次単体を保つ包含は単射。 -/
instance simplexSubsetMap_mono {n : ℕ} (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card) :
    Mono (simplexSubsetMap.{u} I hI) := by
  let : Mono (simplexSubsetHom I hI) :=
    (SimplexCategory.mono_iff_injective (f := simplexSubsetHom I hI)).mpr
      (simplexSubsetOrder_injective I hI)
  exact inferInstanceAs (Mono (uliftYoneda.{u}.map (simplexSubsetHom I hI)))

/-- 元の部分集合の包含の始頂点は、元の最小元の同じ零単体。 -/
lemma simplexSubsetMap_first {n : ℕ} (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card) :
    (simplexSubsetMap.{u} I hI).app _ (standardSimplexVertex 0) =
      standardSimplexVertex (I.min' (Finset.card_pos.mp (by omega))) :=
  standardSimplexVertex_ext (simplexSubsetOrder_first I hI)

/-- 元の部分集合の包含の終頂点は、元の最大元の同じ零単体。 -/
lemma simplexSubsetMap_last {n : ℕ} (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card) :
    (simplexSubsetMap.{u} I hI).app _ (standardSimplexVertex (Fin.last (I.card - 1))) =
      standardSimplexVertex (I.max' (Finset.card_pos.mp (by omega))) :=
  standardSimplexVertex_ext (simplexSubsetOrder_last I hI)

end SerrePositivity.KST.SConstruction
