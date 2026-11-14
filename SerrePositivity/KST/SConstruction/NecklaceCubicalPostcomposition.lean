module
public import SerrePositivity.KST.SConstruction.NecklaceCubicalMapping
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Subdivision.NecklacePostcomposition

/-! # cubical mapping object の入力写像
概要：元の単体集合の写像を、全 necklace の余極限上の射へ送る。
方針：固定端点 necklace の後合成による添字の前合成と余極限の普遍性を使う。
規約：元の全生成射を保持。使われ方：cubical rigidification の入力関手性。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits Simplicial SSet

/-- 元の入力の単体的写像が誘導する、同じ全 necklace の cubical 余極限の射。 -/
def necklaceCubicalMap {K L : SSet.{u}} (a : K ⟶ L) (x y : K _⦋0⦌) :
    necklaceCubicalMapping K x y ⟶ necklaceCubicalMapping L (a.app _ x) (a.app _ y) :=
  colimit.pre (necklaceCubicalDiagram L (a.app _ x) (a.app _ y))
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInPostcompose a x y)

/-- 入力の写像は、元の全 necklace の生成射をその後合成の生成射へ送る。 -/
lemma necklaceCubicalCell_map {K L : SSet.{u}} (a : K ⟶ L) {x y : K _⦋0⦌}
    (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K x y) :
    necklaceCubicalCell T ≫ necklaceCubicalMap a x y =
      necklaceCubicalCell ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInPostcompose a x y).obj T) :=
  colimit.ι_pre (necklaceCubicalDiagram L (a.app _ x) (a.app _ y))
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInPostcompose a x y) T

/-- 元の恒等入力は、同じ cubical mapping object の恒等射を与える。 -/
lemma necklaceCubicalMap_id (K : SSet.{u}) (x y : K _⦋0⦌) :
    necklaceCubicalMap (𝟙 K) x y = 𝟙 (necklaceCubicalMapping K x y) := by
  apply necklaceCubicalMapping_hom_ext
  intro T
  rw [necklaceCubicalCell_map, Category.comp_id]
  rfl

/-- 元の入力の合成は、同じ cubical 余極限の射の合成を厳密に保つ。 -/
lemma necklaceCubicalMap_comp {K L M : SSet.{u}} (a : K ⟶ L) (b : L ⟶ M)
    (x y : K _⦋0⦌) :
    necklaceCubicalMap (a ≫ b) x y =
      necklaceCubicalMap a x y ≫ necklaceCubicalMap b (a.app _ x) (a.app _ y) := by
  apply necklaceCubicalMapping_hom_ext
  intro T
  exact (necklaceCubicalCell_map (a ≫ b) T).trans
    ((necklaceCubicalCell_map b ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInPostcompose a x y).obj T)).symm.trans
      ((congrArg (fun e => e ≫ necklaceCubicalMap b (a.app _ x) (a.app _ y))
        (necklaceCubicalCell_map a T).symm).trans (Category.assoc _ _ _)))

end SerrePositivity.KST.SConstruction
