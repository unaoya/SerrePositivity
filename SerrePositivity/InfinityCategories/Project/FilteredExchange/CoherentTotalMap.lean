module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.Vertices
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoherentFilteredTotalDetection
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SmallLeftUnstraightening
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.ContinuousKanSequence
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoherentTotalObject

/-!
概要：coherent 余極限の指定頂点間に全空間の射から実際の射を構成する。
方針：全空間の Kan 置換を頂点表示の厳密な往復で挟む。
規約：元の単位と自然性を保持。使われ方：引き戻し交換の三つの余極限頂点の接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange
variable {B C D : SSet.{u}}
  (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
  (G : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
  (H : (SSet.uliftFunctor.{u + 1, u}).obj D ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})

/-- 概要：全空間の射が定める元の余極限頂点の値の間の射。
方針：Kan 置換と頂点表示。規約：同型だけの選択をしない。使われ方：元の二脚。 -/
def coherentTotalVertexMap (a : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraightening F ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraightening G) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityObject (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalVertex F)).obj ⟶
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityObject (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalVertex G)).obj :=
  eqToHom (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalVertex_object F) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map a ≫
    eqToHom (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalVertex_object G).symm

/-- 概要：指定頂点の射を元の Kan 模型に戻すと実際の Kan 置換射。
方針：厳密な往復を消去。規約：射の等式。使われ方：全空間の比較錐への接続。 -/
lemma coherentTotalVertexMap_factor
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraightening F ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraightening G) :
    coherentTotalVertexMap F G a ≫ eqToHom (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalVertex_object G) =
      eqToHom (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalVertex_object F) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map a := by
  simp only [coherentTotalVertexMap, Category.assoc, eqToHom_trans, eqToHom_refl,
    Category.comp_id]

/-- 概要：元の余極限頂点の射は元の両単位と厳密に可換する。
方針：Kan 置換の単位の自然性。
規約：指定された単位の等式。使われ方：余錐の指定比較との照合。 -/
lemma coherentTotalVertexMap_unit
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraightening F ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraightening G) :
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalUnit F ≫ coherentTotalVertexMap F G a =
      a ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalUnit G := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalUnit, coherentTotalVertexMap, Category.assoc,
    eqToHom_trans, eqToHom_refl, Category.id_comp]
  rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.naturality]
  rfl

/-- 概要：指定頂点間の射は元の全空間の合成を保つ。
方針：頂点表示の往復と Kan 置換の関手性。
規約：厳密な合成式。使われ方：coherent cospan の元の射の追跡。 -/
lemma coherentTotalVertexMap_comp
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraightening F ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraightening G)
    (b : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraightening G ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraightening H) :
    coherentTotalVertexMap F H (a ≫ b) =
      coherentTotalVertexMap F G a ≫ coherentTotalVertexMap G H b := by
  simp only [coherentTotalVertexMap, Functor.map_comp, Category.assoc,
    eqToHom_trans, eqToHom_refl, Category.id_comp]

end SerrePositivity.InfinityCategories.Project.FilteredExchange
