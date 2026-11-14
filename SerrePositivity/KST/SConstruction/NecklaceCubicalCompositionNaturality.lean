module
public import SerrePositivity.KST.SConstruction.NecklaceCubicalComposition
public import SerrePositivity.KST.SConstruction.NecklaceCubicalPostcomposition
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Subdivision.NecklaceWedgePostcomposition

/-! # 元の cubical 合成の入力自然性
概要：全単体集合の写像は、元の mapping object 上の Day tensor 合成を保つ。
方針：後合成と wedge の実可換三角形を使い、元の両生成射で判定する。
規約：元の全入力写像を扱う。使われ方：cubical rigidification の関手性。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Simplicial SSet

/-- 後合成した wedge と、後合成した両 necklace の wedge の実可換三角形。 -/
def necklaceInWedgePostcomposeHom {K L : SSet.{u}} (a : K ⟶ L)
    {x y z : K _⦋0⦌} (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K x y) (U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K y z) :
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInPostcompose a x z).obj (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge T U) ⟶
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInPostcompose a x y).obj T)
        ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInPostcompose a y z).obj U) where
  necklaceHom := 𝟙 (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedge T.necklace U.necklace)
  w := (Category.id_comp _).trans (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge_postcompose_map a T U)

/-- 元の生成射上で、入力の写像は同じ wedge 合成を保つ。 -/
lemma necklaceCubicalComposeCell_naturality {K L : SSet.{u}} (a : K ⟶ L)
    {x y z : K _⦋0⦌} (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K x y) (U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K y z) :
    necklaceCubicalComposeCell T U ≫ necklaceCubicalMap a x z =
      necklaceCubicalComposeCell ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInPostcompose a x y).obj T)
        ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInPostcompose a y z).obj U) := by
  have h := necklaceCubicalCell_relation (necklaceInWedgePostcomposeHom a T U)
  change necklaceCubicalSet.map (𝟙 (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedge T.necklace U.necklace)) ≫
    necklaceCubicalCell (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInPostcompose a x y).obj T)
      ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInPostcompose a y z).obj U)) =
    necklaceCubicalCell ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInPostcompose a x z).obj (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge T U)) at h
  have hc : necklaceCubicalCell (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInPostcompose a x y).obj T)
      ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInPostcompose a y z).obj U)) =
      necklaceCubicalCell ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInPostcompose a x z).obj (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge T U)) := by
    exact (Category.id_comp _).symm.trans
      ((congrArg (fun b => b ≫ necklaceCubicalCell
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInPostcompose a x y).obj T)
          ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInPostcompose a y z).obj U)))
        (necklaceCubicalSet.map_id (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedge T.necklace U.necklace)).symm).trans h)
  exact (Category.assoc _ _ _).trans
    (congrArg (fun b => (necklaceCubicalTensorIso T.necklace U.necklace).hom ≫ b)
      ((necklaceCubicalCell_map a (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge T U)).trans hc.symm))

/-- 全 mapping object の合成は、元の全入力写像について自然。 -/
lemma necklaceCubicalCompose_naturality {K L : SSet.{u}} (a : K ⟶ L)
    (x y z : K _⦋0⦌) :
    necklaceCubicalCompose K x y z ≫ necklaceCubicalMap a x z =
      cubicalDayTensorMap (necklaceCubicalMap a x y) (necklaceCubicalMap a y z) ≫
        necklaceCubicalCompose L (a.app _ x) (a.app _ y) (a.app _ z) := by
  apply necklaceCubicalTensor_hom_ext K x y z
  intro T U
  have hl := (Category.assoc
    (cubicalDayTensorMap (necklaceCubicalCell T) (necklaceCubicalCell U))
    (necklaceCubicalCompose K x y z) (necklaceCubicalMap a x z)).symm.trans
      ((congrArg (fun b => b ≫ necklaceCubicalMap a x z)
        (necklaceCubicalCompose_cell K x y z T U)).trans
          (necklaceCubicalComposeCell_naturality a T U))
  have ht := (cubicalDayTensorMap_comp (necklaceCubicalCell T) (necklaceCubicalMap a x y)
    (necklaceCubicalCell U) (necklaceCubicalMap a y z)).symm.trans
      (congrArg₂ (fun b c => cubicalDayTensorMap b c)
        (necklaceCubicalCell_map a T) (necklaceCubicalCell_map a U))
  have hr := (Category.assoc
    (cubicalDayTensorMap (necklaceCubicalCell T) (necklaceCubicalCell U))
    (cubicalDayTensorMap (necklaceCubicalMap a x y) (necklaceCubicalMap a y z))
    (necklaceCubicalCompose L (a.app _ x) (a.app _ y) (a.app _ z))).symm.trans
      ((congrArg (fun b => b ≫
        necklaceCubicalCompose L (a.app _ x) (a.app _ y) (a.app _ z)) ht).trans
          (necklaceCubicalCompose_cell L _ _ _ _ _))
  exact hl.trans hr.symm

end SerrePositivity.KST.SConstruction
