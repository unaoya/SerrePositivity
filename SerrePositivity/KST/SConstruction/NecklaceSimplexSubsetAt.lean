module
public import SerrePositivity.KST.SConstruction.NecklaceSimplexSubsetInclusion
public import SerrePositivity.KST.SConstruction.NecklaceCubicalMapping

/-! # 元の共通端点で読む部分集合 bead の包含
概要：元の部分集合 bead を指定された同じ両端で読み、元の余極限の表示関係を得る。
方針：元の augmentation を変えず、最小・最大元との端点等号だけを使う。
規約：端点移送で元の射を置き換えない。使われ方：HA の削除成分の同じ Hom 内での比較。
-/
@[expose] public section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Simplicial SSet

/-- 元の部分集合 bead を、最小・最大元と一致する指定の両端で読む。 -/
def necklaceInSimplexSubsetAt {n : ℕ} (I : Finset (Fin (n + 1))) (a b : Fin (n + 1))
    (hI : 2 ≤ I.card) (ha : a = I.min' (Finset.card_pos.mp (by omega)))
    (hb : b = I.max' (Finset.card_pos.mp (by omega))) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn (Δ[n] : SSet.{u}) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b) where
  necklace := (necklaceInSimplexSubset I hI).necklace
  map := (necklaceInSimplexSubset I hI).map
  map_first := (necklaceInSimplexSubset I hI).map_first.trans
    (congrArg _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex ha.symm)
  map_last := (necklaceInSimplexSubset I hI).map_last.trans
    (congrArg _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex hb.symm)

/-- 元の標準の最小・最大端点で読むと、元の同じ部分集合 bead そのもの。 -/
lemma necklaceInSimplexSubsetAt_canonical {n : ℕ} (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card) :
    necklaceInSimplexSubsetAt.{u} I (I.min' (Finset.card_pos.mp (by omega)))
      (I.max' (Finset.card_pos.mp (by omega))) hI rfl rfl = necklaceInSimplexSubset I hI := rfl

/-- 元の指定端点で読んでも、元の同じ全単体的 augmentation を保つ。 -/
lemma necklaceInSimplexSubsetAt_map {n : ℕ} (I : Finset (Fin (n + 1))) (a b : Fin (n + 1))
    (hI : 2 ≤ I.card) (ha : a = I.min' (Finset.card_pos.mp (by omega)))
    (hb : b = I.max' (Finset.card_pos.mp (by omega))) :
    (necklaceInSimplexSubsetAt.{u} I a b hI ha hb).map = (necklaceInSimplexSubset I hI).map := rfl

/-- 元の同じ指定端点を持つ部分集合包含の、元の全単体的可換三角形。 -/
def necklaceInSimplexSubsetAtInclusion {n : ℕ} (I J : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (hI : 2 ≤ I.card) (hJ : 2 ≤ J.card) (hIJ : I ⊆ J)
    (haI : a = I.min' (Finset.card_pos.mp (by omega)))
    (hbI : b = I.max' (Finset.card_pos.mp (by omega)))
    (haJ : a = J.min' (Finset.card_pos.mp (by omega)))
    (hbJ : b = J.max' (Finset.card_pos.mp (by omega))) :
    necklaceInSimplexSubsetAt.{u} I a b hI haI hbI ⟶
      necklaceInSimplexSubsetAt J a b hJ haJ hbJ where
  necklaceHom := necklaceSimplexSubsetInclusion I J hI hJ hIJ
    (haI.symm.trans haJ) (hbI.symm.trans hbJ)
  w := necklaceSimplexSubsetInclusion_triangle I J hI hJ hIJ
    (haI.symm.trans haJ) (hbI.symm.trans hbJ)

/-- 元の部分集合包含の全単体的可換三角形は、元の cubical 余極限の同じ表示関係を与える。 -/
lemma necklaceInSimplexSubsetAtInclusion_cell {n : ℕ} (I J : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (hI : 2 ≤ I.card) (hJ : 2 ≤ J.card) (hIJ : I ⊆ J)
    (haI : a = I.min' (Finset.card_pos.mp (by omega)))
    (hbI : b = I.max' (Finset.card_pos.mp (by omega)))
    (haJ : a = J.min' (Finset.card_pos.mp (by omega)))
    (hbJ : b = J.max' (Finset.card_pos.mp (by omega))) :
    necklaceCubicalSet.map
        (necklaceInSimplexSubsetAtInclusion.{u} I J a b hI hJ hIJ haI hbI haJ hbJ).necklaceHom ≫
      necklaceCubicalCell (necklaceInSimplexSubsetAt J a b hJ haJ hbJ) =
        necklaceCubicalCell (necklaceInSimplexSubsetAt I a b hI haI hbI) :=
  necklaceCubicalCell_relation
    (necklaceInSimplexSubsetAtInclusion I J a b hI hJ hIJ haI hbI haJ hbJ)

end SerrePositivity.KST.SConstruction
