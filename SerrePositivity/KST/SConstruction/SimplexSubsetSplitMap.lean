module
public import SerrePositivity.KST.SConstruction.SimplexSubsetSplitBlocks
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.SimplexSubsetInclusionMap
public import SerrePositivity.KST.SConstruction.NecklaceWedgeBeadOneFace

/-! # 元の左右部分集合を連結した単体的射
概要：元の左右フィルターの二 bead を、同じ全頂点の部分集合単体へ含める。
方針：元の連結長の等号で番号を移し、左右への制限を元の包含と照合する。
規約：共有頂点を両側に含める。使われ方：元の分割 augmentation の可換三角形。
-/
@[expose] public section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Simplicial SSet
open SerrePositivity.InfinityCategories

/-- 元の二つの分割 bead の長さの和は、元の全体の bead の長さ。 -/
lemma simplexSubsetSplit_length {n : ℕ} (I : Finset (Fin (n + 1))) (j : Fin (n + 1))
    (hj : j ∈ I) (hL : 2 ≤ (I.filter (· ≤ j)).card)
    (hR : 2 ≤ (I.filter (j ≤ ·)).card) :
    ((I.filter (· ≤ j)).card - 1) + ((I.filter (j ≤ ·)).card - 1) = I.card - 1 := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.split_card hj
  omega

/-- 元の分割二 bead の全頂点番号を、同じ全体単体の番号として読む。 -/
def simplexSubsetSplitOrder {n : ℕ} (I : Finset (Fin (n + 1))) (j : Fin (n + 1))
    (hj : j ∈ I) (hL : 2 ≤ (I.filter (· ≤ j)).card)
    (hR : 2 ≤ (I.filter (j ≤ ·)).card) :
    Fin (((I.filter (· ≤ j)).card - 1) + ((I.filter (j ≤ ·)).card - 1) + 1) →o
      Fin (I.card - 1 + 1) :=
  ⟨Fin.cast (congrArg Nat.succ (simplexSubsetSplit_length I j hj hL hR)),
    fun _ _ h => h⟩

/-- 元の分割二 bead を、元の全体の部分集合単体に含める全単体的射。 -/
def simplexSubsetSplitMap {n : ℕ} (I : Finset (Fin (n + 1))) (j : Fin (n + 1))
    (hj : j ∈ I) (hL : 2 ≤ (I.filter (· ≤ j)).card)
    (hR : 2 ≤ (I.filter (j ≤ ·)).card) :
    ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single ((I.filter (· ≤ j)).card - 1)).wedge
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single ((I.filter (j ≤ ·)).card - 1))).carrier.{u} ⟶ Δ[I.card - 1] :=
  _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.inclusion _ ≫ SSet.stdSimplex.map
    (SimplexCategory.Hom.mk (simplexSubsetSplitOrder I j hj hL hR))

/-- 元の分割射の左制限は、元の左部分集合の昇順包含そのもの。 -/
lemma simplexSubsetSplitMap_inl {n : ℕ} (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card)
    (j : Fin (n + 1)) (hj : j ∈ I) (hL : 2 ≤ (I.filter (· ≤ j)).card)
    (hR : 2 ≤ (I.filter (j ≤ ·)).card) :
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single ((I.filter (· ≤ j)).card - 1)).wedgeInl
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single ((I.filter (j ≤ ·)).card - 1)) ≫
      simplexSubsetSplitMap.{u} I j hj hL hR =
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.singleSimplexIso _).hom ≫
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetInclusionMap (I.filter (· ≤ j)) I hL hI (Finset.filter_subset _ _) := by
  apply SSet.hom_ext
  intro d
  obtain ⟨⟨m⟩⟩ := d
  apply ConcreteCategory.hom_ext
  intro s
  apply SSet.stdSimplex.ext
  intro i
  apply Fin.ext
  exact (simplexSubsetSplitLeft_block I hI j hj hL (s.val i)).symm

/-- 元の分割射の右制限は、元の右部分集合の昇順包含そのもの。 -/
lemma simplexSubsetSplitMap_inr {n : ℕ} (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card)
    (j : Fin (n + 1)) (hj : j ∈ I) (hL : 2 ≤ (I.filter (· ≤ j)).card)
    (hR : 2 ≤ (I.filter (j ≤ ·)).card) :
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single ((I.filter (· ≤ j)).card - 1)).wedgeInr
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single ((I.filter (j ≤ ·)).card - 1)) ≫
      simplexSubsetSplitMap.{u} I j hj hL hR =
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.singleSimplexIso _).hom ≫
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetInclusionMap (I.filter (j ≤ ·)) I hR hI (Finset.filter_subset _ _) := by
  apply SSet.hom_ext
  intro d
  obtain ⟨⟨m⟩⟩ := d
  apply ConcreteCategory.hom_ext
  intro s
  apply SSet.stdSimplex.ext
  intro i
  apply Fin.ext
  change (I.filter (· ≤ j)).card - 1 + (s.val i).val =
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetInclusionOrder (I.filter (j ≤ ·)) I hR hI
      (Finset.filter_subset _ _) (s.val i)).val
  have hc := simplexSubsetSplitLeft_card I hI j hj hL
  have hb := simplexSubsetSplitRight_block I hI j hj hR (s.val i)
  omega

end SerrePositivity.KST.SConstruction
