module
public import SerrePositivity.KST.SConstruction.NecklaceCubicalMonoidal
public import SerrePositivity.KST.SConstruction.NecklaceCubicalMapping
public import SerrePositivity.KST.SConstruction.NecklaceCubicalPostcomposition
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Subdivision.NecklaceInPoint

/-! # 元の一点 necklace による cubical mapping object の単位射
概要：元の Day 単位を、一点 necklace の生成射で cubical 余極限へ送る。
方針：元の強モノイダル単位比較と一点の後合成の可換三角形を使う。
規約：元の全高次 cell を保持。使われ方：cubical rigidification の合成単位。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Simplicial SSet

/-- 元の一点 necklace の生成射から得る、cubical mapping object の実単位射。 -/
def necklaceCubicalIdentity (K : SSet.{u}) (x : K _⦋0⦌) :
    cubicalDayUnit ⟶ necklaceCubicalMapping K x x :=
  cubicalDayUnitProjection ≫ cubicalYoneda.map necklaceCubeUnitIso.{u}.hom ≫
    necklaceCubicalCell (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInPoint K x)

/-- 元の cubical 単位射は、元の強モノイダル単位と一点の生成射の合成。 -/
lemma necklaceCubicalIdentity_unit (K : SSet.{u}) (x : K _⦋0⦌) :
    necklaceCubicalIdentity K x =
      (Functor.LaxMonoidal.ε necklaceCubicalDay.{u}).natTrans ≫
        necklaceCubicalCell (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInPoint K x) :=
  (Category.assoc _ _ _).symm

/-- 元の入力写像は、一点の元の生成射から来る cubical 単位射を厳密に保つ。 -/
lemma necklaceCubicalIdentity_naturality {K L : SSet.{u}} (f : K ⟶ L) (x : K _⦋0⦌) :
    necklaceCubicalIdentity K x ≫ necklaceCubicalMap f x x =
      necklaceCubicalIdentity L (f.app _ x) := by
  have h := necklaceCubicalCell_relation (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInPointPostcomposeHom f x)
  change cubicalYoneda.map (necklaceConcreteCubeMap (𝟙 _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklacePoint.{u})) ≫
    necklaceCubicalCell (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInPoint L (f.app _ x)) =
      necklaceCubicalCell ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInPostcompose f x x).obj (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInPoint K x)) at h
  have hi : necklaceConcreteCubeMap (𝟙 _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklacePoint.{u}) =
      𝟙 (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklacePoint.{u}.down.dimension) :=
    necklaceConcreteCube.map_id _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklacePoint
  rw [hi, cubicalYoneda.map_id] at h
  have ht : necklaceCubicalCell ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInPostcompose f x x).obj (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInPoint K x)) =
      necklaceCubicalCell (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInPoint L (f.app _ x)) :=
    h.symm.trans (Category.id_comp _)
  have hc := (necklaceCubicalCell_map f (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInPoint K x)).trans ht
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun e => cubicalDayUnitProjection ≫ e) (Category.assoc _ _ _)).trans
      (congrArg (fun e => cubicalDayUnitProjection ≫
        cubicalYoneda.map necklaceCubeUnitIso.{u}.hom ≫ e) hc))

end SerrePositivity.KST.SConstruction
