module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.CoherentConstantTargetComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SmallLeftUnstraightening
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FunctorSpace

/-!
概要：coherent な定値標的への変換を小さい unstraightening の全空間からの写像と比較する。
方針：全空間の縮小同型による前合成と内部 Hom の宇宙移送を合成する。
規約：小さい底からの任意の coherent 図式。filtered 性は不要。
使われ方：小さい全空間の Kan 模型を元の宇宙の余極限候補にする。

対応節は Kerodon 8.3（Tag 03LZ）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
variable {B : SSet.{u}}

/-- 概要：大きい全空間からの内部 Hom は小さい全空間からの内部 Hom の持ち上げ。
方針：縮小同型の前合成と内部 Hom の宇宙移送の逆を合成する。
規約：標的 Z の充填性は不要。使われ方：全パラメータでの宇宙の調整。 -/
def smallUnstraighteningHomIso
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) (Z : SSet.{u}) :
    (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraightening F)).obj ((SSet.uliftFunctor.{u + 1, u}).obj Z) ≅
      (SSet.uliftFunctor.{u + 1, u}).obj ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraightening F)).obj Z) :=
  ((internalHom (C := SSet.{u + 1})).mapIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningIso F).op).app _ ≪≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftFunctorSpaceIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraightening F) Z).symm

/-- 概要：定値標的への変換を元の小さい全空間からの写像の持ち上げへ送る。
方針：定値標的の比較の後で小さい全空間の内部 Hom へ戻す。
規約：全次数の射。使われ方：全空間の単位を coherent な変換として回収する。 -/
def coherentSmallConstantTargetMap
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (z : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningTransformationSpace F (SSet.const z) ⟶
      (SSet.uliftFunctor.{u + 1, u}).obj
        ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraightening F)).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityObject z).obj) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coherentConstantTargetMap F z ≫ (smallUnstraighteningHomIso F (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityObject z).obj).hom

/-- 概要：小さい全空間からの写像への実際の比較は同値。
方針：大きい全空間の比較に厳密な同型を合成する。
規約：任意の小さい底で成立する。使われ方：余極限候補の単位の表現。 -/
lemma coherentSmallConstantTargetMap_isQCatEquivalence
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (z : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (coherentSmallConstantTargetMap F z) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coherentConstantTargetMap_isQCatEquivalence F z).comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso
      (smallUnstraighteningHomIso F (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityObject z).obj)).isQCatEquivalence

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
