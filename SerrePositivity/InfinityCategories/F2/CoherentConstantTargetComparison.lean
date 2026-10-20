module

public import SerrePositivity.InfinityCategories.F2.RelativeFunctorConstFiberIso
public import SerrePositivity.InfinityCategories.F1.CoherentUnstraighteningMappingEquivalence
public import SerrePositivity.InfinityCategories.F1.LeftUnstraighteningFiberValue
public import SerrePositivity.InfinityCategories.Core.FunctorComposition

/-!
概要：定値図式への coherent な変換を、unstraightening の全空間からの写像と比較する。
方針：F1 の写像空間同値に、相対底変換と定値 fiber の比較を合成する。
規約：任意の底・coherent 図式を扱い、strict 図式や filtered 性を仮定しない。
使われ方：全空間の Kan 模型を実際の余極限余錐へ接続するための写像空間の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 概要：定値 unstraightening への相対 Hom は pointed-space fiber への内部 Hom。
方針：相対底変換の同型の後で、定値の底の fiber の同型を使う。
規約：定義域の底の射 a は任意。使われ方：全空間からの写像との厳密な比較。 -/
def constantUnstraighteningRelativeIso {A B : SSet.{u + 1}} (a : A ⟶ B)
    (z : SpaceInfinity.{u} _⦋0⦌) :
    relativeFunctorSpace (leftUnstraighteningProjection (SSet.const z : B ⟶ SpaceInfinity)) a ≅
      (ihom A).obj (vertexFiber pointedSpaceProjection z) := by
  let e : relativeFunctorSpace pointedSpaceProjection (a ≫ SSet.const z) ≅
      relativeFunctorSpace pointedSpaceProjection (SSet.const z : A ⟶ SpaceInfinity) :=
    eqToIso (by rw [SSet.comp_const])
  exact relativeFunctorBaseChangeIso pointedSpaceProjection (SSet.const z) a ≪≫ e ≪≫
    relativeFunctorConstFiberIso pointedSpaceProjection z

/-- 概要：coherent な定値標的への変換を全空間から元の値の持ち上げへの写像にする。
方針：既存の unstraightening 比較と定値相対 Hom の同型、fiber の値の同値を合成する。
規約：全次数の実際の射。使われ方：一般 coherent 図式の余錐の普遍性。 -/
def coherentConstantTargetMap {B : SSet.{u + 1}} (F : B ⟶ SpaceInfinity.{u})
    (z : SpaceInfinity.{u} _⦋0⦌) :
    leftUnstraighteningTransformationSpace F (SSet.const z) ⟶
      (ihom (leftUnstraightening F)).obj
        ((SSet.uliftFunctor.{u + 1, u}).obj (spaceInfinityObject z).obj) :=
  leftUnstraighteningMappingSpaceMap F (SSet.const z) ≫
    (constantUnstraighteningRelativeIso (leftUnstraighteningProjection F) z).hom ≫
      (ihom (leftUnstraightening F)).map (pointedSpaceFiberValueEquivalence z).hom

/-- 概要：定値標的への coherent な変換と全空間からの写像の実際の比較は同値。
方針：F1 の任意の底上の比較と、厳密な同型・fiber の同値による後合成を使う。
規約：底の充填性や filtered 性は不要。使われ方：一般 coherent な余錐の表現。 -/
lemma coherentConstantTargetMap_isQCatEquivalence {B : SSet.{u + 1}}
    (F : B ⟶ SpaceInfinity.{u}) (z : SpaceInfinity.{u} _⦋0⦌) :
    IsQCatEquivalence (coherentConstantTargetMap F z) :=
  (leftUnstraighteningMappingSpaceMap_isQCatEquivalence F (SSet.const z)).comp
    ((qCatEquivalenceOfIso
      (constantUnstraighteningRelativeIso
        (leftUnstraighteningProjection F) z)).isQCatEquivalence.comp
        ((pointedSpaceFiberValueEquivalence z).postcompose
          (leftUnstraightening F)).isQCatEquivalence)

end SerrePositivity.InfinityCategories.F2
