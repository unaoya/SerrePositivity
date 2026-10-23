module

public import SerrePositivity.InfinityCategories.F1.Coherent.ConstantSourceComparison
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.SmallUnstraighteningSectionsIso
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraighteningFiberValue
public import SerrePositivity.InfinityCategories.F1.Universe.Kan
public import SerrePositivity.InfinityCategories.Core.FunctorComposition

/-!
概要：定値始域からの coherent な変換を、小さい全切断への内部 Hom の持ち上げへ比較する。
方針：pointed fiber の値の同値、切断の縮小同型、内部 Hom の宇宙移送を合成する。
規約：任意の小さい底と全高次パラメータを保持する。
使われ方：小さい全切断の恒等射を表す変換の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
variable {B : SSet.{u}}
  (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
local instance : KanComplex (HomotopyLimits.simplicialSections (leftUnstraighteningProjection F)) :=
  HomotopyLimits.simplicialSections_kanComplex (leftUnstraighteningProjection F)

/-- 定値始域の変換を、元の値から小さい全切断への関手空間に写す。 -/
def coherentSmallConstantSourceMap (z : SpaceInfinity.{u} _⦋0⦌) :
    leftUnstraighteningTransformationSpace (SSet.const z) F ⟶
      (SSet.uliftFunctor.{u + 1, u}).obj
        ((ihom (spaceInfinityObject z).obj).obj (coherentSpaceSectionsObject F).obj) :=
  coherentConstantSourceMap F z ≫
    ((pointedSpaceFiberValueEquivalence z).symm.precompose
      (HomotopyLimits.simplicialSections (leftUnstraighteningProjection F))).hom ≫
    (ihom ((SSet.uliftFunctor.{u + 1, u}).obj (spaceInfinityObject z).obj)).map
      (smallUnstraighteningSectionsIso F).inv ≫
    (uliftFunctorSpaceIso (spaceInfinityObject z).obj (coherentSpaceSectionsObject F).obj).inv

/-- 元の小さい全切断への内部 Hom を標的とする、同じ実際の比較自体が同値。 -/
lemma coherentSmallConstantSourceMap_isQCatEquivalence (z : SpaceInfinity.{u} _⦋0⦌) :
    IsQCatEquivalence (coherentSmallConstantSourceMap F z) :=
  (coherentConstantSourceMap_isQCatEquivalence F z).comp
    (((pointedSpaceFiberValueEquivalence z).symm.precompose
      (HomotopyLimits.simplicialSections (leftUnstraighteningProjection F))).isQCatEquivalence.comp
      ((qCatEquivalenceOfIso
        ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj (spaceInfinityObject z).obj)).mapIso
          (smallUnstraighteningSectionsIso F).symm)).isQCatEquivalence.comp
        (qCatEquivalenceOfIso
          (uliftFunctorSpaceIso (spaceInfinityObject z).obj
            (coherentSpaceSectionsObject F).obj).symm).isQCatEquivalence))

end SerrePositivity.InfinityCategories
