module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Simplicial.SimplexSubsetInclusionOrder
public import SerrePositivity.InfinityCategories.Simplicial.SimplexSubsetMap

/-! # 元の部分集合包含の単体的可換三角形
概要：元の部分集合包含を全単体的な射にし、元の包含への合成と両端を回収する。
方針：元の局所番号の単調写像を標準単体関手へ送る。
規約：元の最小・最大元の一致を明示。使われ方：端点を保つ実 necklace 包含。
-/
@[expose] public section
universe u
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Simplicial
open SerrePositivity.KST.SConstruction
open CategoryTheory _root_.Simplicial SSet

/-- 元の始端が一致する部分集合包含は、元の局所始頂点を保つ。 -/
lemma simplexSubsetInclusionOrder_first {n : ℕ} (I J : Finset (Fin (n + 1)))
    (hI : 2 ≤ I.card) (hJ : 2 ≤ J.card) (hIJ : I ⊆ J)
    (hmin : I.min' (Finset.card_pos.mp (by omega)) =
      J.min' (Finset.card_pos.mp (by omega))) :
    simplexSubsetInclusionOrder I J hI hJ hIJ 0 = 0 :=
  simplexSubsetOrder_injective J hJ
    ((simplexSubsetInclusionOrder_recovery I J hI hJ hIJ 0).trans
      ((simplexSubsetOrder_first I hI).trans (hmin.trans (simplexSubsetOrder_first J hJ).symm)))

/-- 元の終端が一致する部分集合包含は、元の局所終頂点を保つ。 -/
lemma simplexSubsetInclusionOrder_last {n : ℕ} (I J : Finset (Fin (n + 1)))
    (hI : 2 ≤ I.card) (hJ : 2 ≤ J.card) (hIJ : I ⊆ J)
    (hmax : I.max' (Finset.card_pos.mp (by omega)) =
      J.max' (Finset.card_pos.mp (by omega))) :
    simplexSubsetInclusionOrder I J hI hJ hIJ (Fin.last (I.card - 1)) =
      Fin.last (J.card - 1) :=
  simplexSubsetOrder_injective J hJ
    ((simplexSubsetInclusionOrder_recovery I J hI hJ hIJ _).trans
      ((simplexSubsetOrder_last I hI).trans (hmax.trans (simplexSubsetOrder_last J hJ).symm)))

/-- 元の部分集合包含の、元の単体圏の射。 -/
def simplexSubsetInclusionHom {n : ℕ} (I J : Finset (Fin (n + 1)))
    (hI : 2 ≤ I.card) (hJ : 2 ≤ J.card) (hIJ : I ⊆ J) :
    ⦋I.card - 1⦌ ⟶ ⦋J.card - 1⦌ :=
  SimplexCategory.Hom.mk (simplexSubsetInclusionOrder I J hI hJ hIJ)

/-- 元の部分集合包含の、元の全高次単体を保つ単体的射。 -/
def simplexSubsetInclusionMap {n : ℕ} (I J : Finset (Fin (n + 1)))
    (hI : 2 ≤ I.card) (hJ : 2 ≤ J.card) (hIJ : I ⊆ J) :
    (Δ[I.card - 1] : SSet.{u}) ⟶ Δ[J.card - 1] :=
  stdSimplex.map (simplexSubsetInclusionHom I J hI hJ hIJ)

/-- 元の単体圏の包含の射は、元の標準単体への包含と可換。 -/
lemma simplexSubsetInclusionHom_triangle {n : ℕ} (I J : Finset (Fin (n + 1)))
    (hI : 2 ≤ I.card) (hJ : 2 ≤ J.card) (hIJ : I ⊆ J) :
    simplexSubsetInclusionHom I J hI hJ hIJ ≫ simplexSubsetHom J hJ = simplexSubsetHom I hI :=
  congrArg (fun f : Fin (I.card - 1 + 1) →o Fin (n + 1) =>
    (SimplexCategory.Hom.mk f : ⦋I.card - 1⦌ ⟶ ⦋n⦌))
    (simplexSubsetInclusionOrder_triangle I J hI hJ hIJ)

/-- 元の全単体的な包含の合成は、同じ元の部分集合の包含を厳密に回収する。 -/
lemma simplexSubsetInclusionMap_triangle {n : ℕ} (I J : Finset (Fin (n + 1)))
    (hI : 2 ≤ I.card) (hJ : 2 ≤ J.card) (hIJ : I ⊆ J) :
    simplexSubsetInclusionMap.{u} I J hI hJ hIJ ≫ simplexSubsetMap J hJ = simplexSubsetMap I hI :=
  ((stdSimplex.{u}).map_comp _ _).symm.trans
    (congrArg (fun f => stdSimplex.map f) (simplexSubsetInclusionHom_triangle I J hI hJ hIJ))

/-- 元の最小元が一致すると、元の単体的包含は同じ始零単体を保つ。 -/
lemma simplexSubsetInclusionMap_first {n : ℕ} (I J : Finset (Fin (n + 1)))
    (hI : 2 ≤ I.card) (hJ : 2 ≤ J.card) (hIJ : I ⊆ J)
    (hmin : I.min' (Finset.card_pos.mp (by omega)) =
      J.min' (Finset.card_pos.mp (by omega))) :
    (simplexSubsetInclusionMap.{u} I J hI hJ hIJ).app _ (standardSimplexVertex 0) =
      standardSimplexVertex 0 :=
  standardSimplexVertex_ext (simplexSubsetInclusionOrder_first I J hI hJ hIJ hmin)

/-- 元の最大元が一致すると、元の単体的包含は同じ終零単体を保つ。 -/
lemma simplexSubsetInclusionMap_last {n : ℕ} (I J : Finset (Fin (n + 1)))
    (hI : 2 ≤ I.card) (hJ : 2 ≤ J.card) (hIJ : I ⊆ J)
    (hmax : I.max' (Finset.card_pos.mp (by omega)) =
      J.max' (Finset.card_pos.mp (by omega))) :
    (simplexSubsetInclusionMap.{u} I J hI hJ hIJ).app _
        (standardSimplexVertex (Fin.last (I.card - 1))) =
      standardSimplexVertex (Fin.last (J.card - 1)) :=
  standardSimplexVertex_ext (simplexSubsetInclusionOrder_last I J hI hJ hIJ hmax)

end SerrePositivity.InfinityCategories.Simplicial

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Simplicial.simplexSubsetInclusionHom (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.simplexSubsetInclusionHom := _root_.SerrePositivity.InfinityCategories.Simplicial.simplexSubsetInclusionHom

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.simplexSubsetInclusionHom_triangle := _root_.SerrePositivity.InfinityCategories.Simplicial.simplexSubsetInclusionHom_triangle

@[deprecated _root_.SerrePositivity.InfinityCategories.Simplicial.simplexSubsetInclusionMap (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.simplexSubsetInclusionMap := _root_.SerrePositivity.InfinityCategories.Simplicial.simplexSubsetInclusionMap

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.simplexSubsetInclusionMap_first := _root_.SerrePositivity.InfinityCategories.Simplicial.simplexSubsetInclusionMap_first

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.simplexSubsetInclusionMap_last := _root_.SerrePositivity.InfinityCategories.Simplicial.simplexSubsetInclusionMap_last

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.simplexSubsetInclusionMap_triangle := _root_.SerrePositivity.InfinityCategories.Simplicial.simplexSubsetInclusionMap_triangle

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.simplexSubsetInclusionOrder_first := _root_.SerrePositivity.InfinityCategories.Simplicial.simplexSubsetInclusionOrder_first

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.simplexSubsetInclusionOrder_last := _root_.SerrePositivity.InfinityCategories.Simplicial.simplexSubsetInclusionOrder_last

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.simplexSubsetInclusionOrder_first._proof_2 := _root_.SerrePositivity.InfinityCategories.Simplicial.simplexSubsetInclusionOrder_first._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.simplexSubsetInclusionOrder_first._proof_4 := _root_.SerrePositivity.InfinityCategories.Simplicial.simplexSubsetInclusionOrder_first._proof_4
