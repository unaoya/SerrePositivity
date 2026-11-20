module

public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Chains.SimplexSubsetOrder
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.FaceDegeneracy.SimplexIntervalMap

/-! # 元の有限部分集合の単体的包含
概要：元の昇順部分集合を標準単体に含め、全高次単体と元の両端を回収する。
方針：元の昇順列挙の単体圏の射に、元の標準単体関手を適用する。
規約：元の有限部分集合そのものを使う。使われ方：元の部分集合 bead の augmentation。
-/
@[expose] public section
universe u
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
open _root_.SerrePositivity.KST.SConstruction
open CategoryTheory _root_.Simplicial SSet

/-- 元の有限部分集合の標準単体から、同じ頂点の像を持つ標準単体への包含。 -/
def simplexSubsetMap {n : ℕ} (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card) :
    (Δ[I.card - 1] : SSet.{u}) ⟶ Δ[n] := stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetHom I hI)

/-- 元の部分集合の単体的包含は、全ての高次単体で元の昇順頂点作用を回収する。 -/
lemma simplexSubsetMap_apply {n m : ℕ} (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card)
    (s : (Δ[I.card - 1] : SSet.{u}) _⦋m⦌) (i : Fin (m + 1)) :
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetMap I hI).app _ s i = _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder I hI (s i) := rfl

/-- 元の部分集合の全高次単体を保つ包含は単射。 -/
instance simplexSubsetMap_mono {n : ℕ} (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card) :
    Mono (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetMap.{u} I hI) := by
  let : Mono (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetHom I hI) :=
    (SimplexCategory.mono_iff_injective (f := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetHom I hI)).mpr
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder_injective I hI)
  exact inferInstanceAs (Mono (uliftYoneda.{u}.map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetHom I hI)))

/-- 元の部分集合の包含の始頂点は、元の最小元の同じ零単体。 -/
lemma simplexSubsetMap_first {n : ℕ} (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card) :
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetMap.{u} I hI).app _ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex 0) =
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (I.min' (Finset.card_pos.mp (by omega))) :=
  _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex_ext (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder_first I hI)

/-- 元の部分集合の包含の終頂点は、元の最大元の同じ零単体。 -/
lemma simplexSubsetMap_last {n : ℕ} (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card) :
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetMap.{u} I hI).app _ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (Fin.last (I.card - 1))) =
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (I.max' (Finset.card_pos.mp (by omega))) :=
  _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex_ext (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder_last I hI)

end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
