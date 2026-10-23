module

public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.CoherentConstantTargetComparison
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.SmallLeftUnstraightening
public import SerrePositivity.InfinityCategories.F1.Universe.FunctorSpace

/-!
概要：coherent な定値標的への変換を小さい unstraightening の全空間からの写像と比較する。
方針：全空間の縮小同型による前合成と内部 Hom の宇宙移送を合成する。
規約：小さい底からの任意の coherent 図式。filtered 性は不要。
使われ方：小さい全空間の Kan 模型を元の宇宙の余極限候補にする。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}

/-- 概要：大きい全空間からの内部 Hom は小さい全空間からの内部 Hom の持ち上げ。
方針：縮小同型の前合成と内部 Hom の宇宙移送の逆を合成する。
規約：標的 Z の充填性は不要。使われ方：全パラメータでの宇宙の調整。 -/
def smallUnstraighteningHomIso
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) (Z : SSet.{u}) :
    (ihom (leftUnstraightening F)).obj ((SSet.uliftFunctor.{u + 1, u}).obj Z) ≅
      (SSet.uliftFunctor.{u + 1, u}).obj ((ihom (smallLeftUnstraightening F)).obj Z) :=
  ((internalHom (C := SSet.{u + 1})).mapIso (smallLeftUnstraighteningIso F).op).app _ ≪≫
    (uliftFunctorSpaceIso (smallLeftUnstraightening F) Z).symm

/-- 概要：定値標的への変換を元の小さい全空間からの写像の持ち上げへ送る。
方針：定値標的の比較の後で小さい全空間の内部 Hom へ戻す。
規約：全次数の射。使われ方：全空間の単位を coherent な変換として回収する。 -/
def coherentSmallConstantTargetMap
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    (z : SpaceInfinity.{u} _⦋0⦌) :
    leftUnstraighteningTransformationSpace F (SSet.const z) ⟶
      (SSet.uliftFunctor.{u + 1, u}).obj
        ((ihom (smallLeftUnstraightening F)).obj (spaceInfinityObject z).obj) :=
  coherentConstantTargetMap F z ≫ (smallUnstraighteningHomIso F (spaceInfinityObject z).obj).hom

/-- 概要：小さい全空間からの写像への実際の比較は同値。
方針：大きい全空間の比較に厳密な同型を合成する。
規約：任意の小さい底で成立する。使われ方：余極限候補の単位の表現。 -/
lemma coherentSmallConstantTargetMap_isQCatEquivalence
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    (z : SpaceInfinity.{u} _⦋0⦌) : IsQCatEquivalence (coherentSmallConstantTargetMap F z) :=
  (coherentConstantTargetMap_isQCatEquivalence F z).comp
    (qCatEquivalenceOfIso
      (smallUnstraighteningHomIso F (spaceInfinityObject z).obj)).isQCatEquivalence

end SerrePositivity.InfinityCategories.F2
