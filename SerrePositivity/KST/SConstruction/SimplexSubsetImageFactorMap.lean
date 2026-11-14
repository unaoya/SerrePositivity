module
public import SerrePositivity.KST.SConstruction.SimplexSubsetImageFactorOrder
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.FaceDegeneracy.SimplexSubsetMap

/-! # 元の部分集合写像の像への実単体的因子
概要：元の部分集合の単体的写像を、同じ元の像部分集合の単体を通して分解する。
方針：元の局所番号因子を標準単体関手へ送り、全高次単体と両端を照合する。
規約：単射性を仮定しない。使われ方：像 necklace の実可換三角形。
-/
@[expose] public section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Simplicial SSet

/-- 元の像部分集合への番号因子を、元の単体圏の射にする。 -/
def simplexSubsetImageFactorHom {M N : ℕ} (α : Fin (M + 1) →o Fin (N + 1))
    (I : Finset (Fin (M + 1))) (hI : 2 ≤ I.card) (hJ : 2 ≤ (I.image α).card) :
    ⦋I.card - 1⦌ ⟶ ⦋(I.image α).card - 1⦌ :=
  SimplexCategory.Hom.mk (simplexSubsetImageFactorOrder α I hI hJ)

/-- 元の像部分集合への、元の全単体を保つ実写像。 -/
def simplexSubsetImageFactorMap {M N : ℕ} (α : Fin (M + 1) →o Fin (N + 1))
    (I : Finset (Fin (M + 1))) (hI : 2 ≤ I.card) (hJ : 2 ≤ (I.image α).card) :
    (Δ[I.card - 1] : SSet.{u}) ⟶ Δ[(I.image α).card - 1] :=
  SSet.stdSimplex.map (simplexSubsetImageFactorHom α I hI hJ)

/-- 元の像部分集合への因子と元の像包含の合成は、元の入力写像の後合成。 -/
lemma simplexSubsetImageFactorMap_triangle {M N : ℕ} (α : Fin (M + 1) →o Fin (N + 1))
    (I : Finset (Fin (M + 1))) (hI : 2 ≤ I.card) (hJ : 2 ≤ (I.image α).card) :
    simplexSubsetImageFactorMap.{u} α I hI hJ ≫ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetMap (I.image α) hJ =
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetMap I hI ≫ SSet.stdSimplex.map (SimplexCategory.Hom.mk α) := by
  have h : simplexSubsetImageFactorHom α I hI hJ ≫ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetHom (I.image α) hJ =
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetHom I hI ≫ SimplexCategory.Hom.mk α := by
    ext v
    exact congrArg Fin.val (simplexSubsetImageFactorOrder_recovery α I hI hJ v)
  exact ((SSet.stdSimplex.{u}).map_comp _ _).symm.trans
    ((congrArg (SSet.stdSimplex.{u}).map h).trans ((SSet.stdSimplex.{u}).map_comp _ _))

/-- 元の像部分集合への実因子は、元の始零単体を保つ。 -/
lemma simplexSubsetImageFactorMap_first {M N : ℕ} (α : Fin (M + 1) →o Fin (N + 1))
    (I : Finset (Fin (M + 1))) (hI : 2 ≤ I.card) (hJ : 2 ≤ (I.image α).card) :
    (simplexSubsetImageFactorMap.{u} α I hI hJ).app _ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex 0) =
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex 0 :=
  _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex_ext (simplexSubsetImageFactorOrder_first α I hI hJ)

/-- 元の像部分集合への実因子は、元の終零単体を保つ。 -/
lemma simplexSubsetImageFactorMap_last {M N : ℕ} (α : Fin (M + 1) →o Fin (N + 1))
    (I : Finset (Fin (M + 1))) (hI : 2 ≤ I.card) (hJ : 2 ≤ (I.image α).card) :
    (simplexSubsetImageFactorMap.{u} α I hI hJ).app _
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (Fin.last (I.card - 1))) =
        _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (Fin.last ((I.image α).card - 1)) :=
  _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex_ext (simplexSubsetImageFactorOrder_last α I hI hJ)

end SerrePositivity.KST.SConstruction
