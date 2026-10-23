module

public import SerrePositivity.InfinityCategories.F1.Pullbacks.PullbackConstantTensor
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorExponential
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorOverIsomorphism
public import SerrePositivity.InfinityCategories.F1.Coherent.UnstraighteningMappingEquivalence
public import SerrePositivity.InfinityCategories.HomotopyLimits.SectionsKan

/-!
概要：定値始域から coherent 図式への変換を、指定 fiber から全切断への内部 Hom と比較する。
方針：定値 unstraightening の直積分解と相対関手空間の指数則を合成する。
規約：底は任意。変換・全切断の全高次パラメータを保持する。
使われ方：F1-4 の全切断を頂点とする native な極限錐の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

local instance {B : SSet.{u + 1}} (F : B ⟶ SpaceInfinity.{u}) :
    KanComplex (HomotopyLimits.simplicialSections (leftUnstraighteningProjection F)) :=
  HomotopyLimits.simplicialSections_kanComplex (leftUnstraighteningProjection F)

/-- 定値図式の unstraightening は、元の底と pointed fiber の積に底上で同型。 -/
def constantUnstraighteningSourceOverIso (B : SSet.{u + 1}) (z : SpaceInfinity.{u} _⦋0⦌) :
    Over.mk (leftUnstraighteningProjection (SSet.const z : B ⟶ SpaceInfinity.{u})) ≅
      Over.mk (fst B (vertexFiber pointedSpaceProjection z)) :=
  Over.isoMk (pullbackConstantTensorIso pointedSpaceProjection z B) (by
    dsimp only [pullbackConstantTensorIso, pullbackConstantToTensor]
    exact lift_fst _ _)

/-- 同じ定値 unstraightening からの相対関手空間は、全切断への内部 Hom と厳密に同型。 -/
def constantUnstraighteningSourceRelativeIso {B : SSet.{u + 1}}
    (F : B ⟶ SpaceInfinity.{u}) (z : SpaceInfinity.{u} _⦋0⦌) :
    relativeFunctorSpace (leftUnstraighteningProjection F)
      (leftUnstraighteningProjection (SSet.const z)) ≅
      (ihom (vertexFiber pointedSpaceProjection z)).obj
        (HomotopyLimits.simplicialSections (leftUnstraighteningProjection F)) :=
  relativeFunctorOverIso (constantUnstraighteningSourceOverIso B z)
      (Iso.refl (Over.mk (leftUnstraighteningProjection F))) ≪≫
    eqToIso (by rw [Category.comp_id]; rfl) ≪≫
    relativeFunctorExponentialIso (leftUnstraighteningProjection F) (𝟙 B)
      (vertexFiber pointedSpaceProjection z) ≪≫
    (ihom (vertexFiber pointedSpaceProjection z)).mapIso
      (HomotopyLimits.simplicialSectionsRelativeIso (leftUnstraighteningProjection F)).symm

/-- 定値始域からの実際の変換を、指定 fiber から全切断への内部 Hom へ送る。 -/
def coherentConstantSourceMap {B : SSet.{u + 1}}
    (F : B ⟶ SpaceInfinity.{u}) (z : SpaceInfinity.{u} _⦋0⦌) :
    leftUnstraighteningTransformationSpace (SSet.const z) F ⟶
      (ihom (vertexFiber pointedSpaceProjection z)).obj
        (HomotopyLimits.simplicialSections (leftUnstraighteningProjection F)) :=
  leftUnstraighteningMappingSpaceMap (SSet.const z) F ≫
    (constantUnstraighteningSourceRelativeIso F z).hom

/-- 定値始域から全切断への実際の比較は、任意の底で同値。 -/
lemma coherentConstantSourceMap_isQCatEquivalence {B : SSet.{u + 1}}
    (F : B ⟶ SpaceInfinity.{u}) (z : SpaceInfinity.{u} _⦋0⦌) :
    IsQCatEquivalence (coherentConstantSourceMap F z) :=
  (leftUnstraighteningMappingSpaceMap_isQCatEquivalence (SSet.const z) F).comp
    (qCatEquivalenceOfIso (constantUnstraighteningSourceRelativeIso F z)).isQCatEquivalence

end SerrePositivity.InfinityCategories
