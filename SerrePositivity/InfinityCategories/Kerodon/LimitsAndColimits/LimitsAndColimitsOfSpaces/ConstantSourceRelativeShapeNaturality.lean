module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.ConstantSourceRestrictedRelative
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.ConstantSourceShapeCoordinates
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.CartesianSectionsRestrictionEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.UnstraighteningSectionsRestriction

/-!
概要：元の定値始域比較の形状制限を、同じ切断制限の全評価で照合する。
方針：指定引き戻しへの後合成と定値直積表示を、相対指数則の下で計算する。
規約：全写像の厳密な等式。各頂点だけの比較に弱めない。
使われ方：元の unstraightening の写像空間の自然性を切断の全族へ写す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces

/-- 定値始域の実際の底変換射で、元の標的への相対写像を前合成する。 -/
def constantSourceRelativeShapePre {B K : SSet.{u + 1}}
    (F : B ⟶ SpaceInfinity.{u}) (i : K ⟶ B) (z : SpaceInfinity.{u} _⦋0⦌) :
    relativeFunctorSpace (leftUnstraighteningProjection F)
      (leftUnstraighteningProjection (SSet.const z : B ⟶ _)) ⟶
    relativeFunctorSpace (leftUnstraighteningProjection F)
      (leftUnstraighteningProjection (SSet.const z : K ⟶ _) ≫ i) :=
  relativeFunctorOverPre (leftUnstraighteningProjection F)
    (a := Over.mk (leftUnstraighteningProjection (SSet.const z : K ⟶ _) ≫ i))
    (b := Over.mk (leftUnstraighteningProjection (SSet.const z : B ⟶ _)))
    (Over.homMk (leftUnstraighteningMap (SSet.const z) (SSet.const z) i
      (SSet.comp_const i z)) (leftUnstraighteningMap_projection _ _ _ _))

/-- 始域の制限を元の指数同型で読むと、同じ実切断の制限への後合成。 -/
lemma constantSourceRelativeShapePre_comparison {B K T : SSet.{u + 1}}
    (F : B ⟶ SpaceInfinity.{u}) (i : K ⟶ B) (z : SpaceInfinity.{u} _⦋0⦌)
    (a : T ⟶ relativeFunctorSpace (leftUnstraighteningProjection F)
      (leftUnstraighteningProjection (SSet.const z : B ⟶ _))) :
    (a ≫ constantSourceRelativeShapePre F i z) ≫
      (constantSourceRestrictedRelativeIso F i z).hom =
    (a ≫ (constantUnstraighteningSourceRelativeIso F z).hom) ≫
      (ihom (vertexFiber pointedSpaceProjection z)).map
        (unstraighteningSectionsRestriction F i ≫
          (unstraighteningSectionsRestrictionTargetIso F i).hom) := by
  apply uncurry_injective
  apply relativeFunctorUncurry_injective
  rw [constantSourceRestrictedRelativeIso_evaluation]
  dsimp only [constantSourceRelativeShapePre]
  erw [relativeFunctorOverPre_uncurry]
  rw [uncurry_natural_right,
    relativeFunctorUncurry_parameter]
  rw [show relativeFunctorUncurry (unstraighteningSectionsRestriction F i ≫
      (unstraighteningSectionsRestrictionTargetIso F i).hom) =
      (i ▷ simplicialSections (leftUnstraighteningProjection F)) ≫
        simplicialSectionsEvaluation (leftUnstraighteningProjection F) from
      sectionsRestrictionOfIso_relative_evaluation _ _ _ _ _]
  rw [← Category.assoc (K ◁ uncurry (a ≫
      (constantUnstraighteningSourceRelativeIso F z).hom)),
    whisker_exchange, Category.assoc,
    constantUnstraighteningSourceRelativeIso_evaluation]
  rw [← Category.assoc ((constantUnstraighteningSourceOverIso K z).inv.left ▷ T),
    ← comp_whiskerRight]
  erw [constantSourceOverIso_inv_shape i z (SSet.comp_const i z)]
  rw [comp_whiskerRight]
  simp only [Category.assoc]
  rw [← Category.assoc (α_ K (vertexFiber pointedSpaceProjection z) T).inv,
    ← associator_inv_naturality_left]
  simp only [Category.assoc]

/-- 標的の底変換射による相対後合成を、同じ相対指数同型の下で読む。 -/
lemma constantSourceRelativeShapePost_comparison {B K T : SSet.{u + 1}}
    (F : B ⟶ SpaceInfinity.{u}) (i : K ⟶ B) (z : SpaceInfinity.{u} _⦋0⦌)
    (a : T ⟶ relativeFunctorSpace (leftUnstraighteningProjection (i ≫ F))
      (leftUnstraighteningProjection (SSet.const z : K ⟶ _))) :
    (a ≫ relativeFunctorSquarePost (leftUnstraighteningProjection (i ≫ F))
      (leftUnstraighteningProjection F) i (leftUnstraighteningMap (i ≫ F) F i rfl)
      (leftUnstraighteningMap_projection _ _ _ _) (leftUnstraighteningProjection
        (SSet.const z : K ⟶ _))) ≫ (constantSourceRestrictedRelativeIso F i z).hom =
    (a ≫ (constantUnstraighteningSourceRelativeIso (i ≫ F) z).hom) ≫
      (ihom (vertexFiber pointedSpaceProjection z)).map
        (unstraighteningSectionsRestrictionTargetIso F i).hom := by
  apply uncurry_injective
  apply relativeFunctorUncurry_injective
  rw [constantSourceRestrictedRelativeIso_evaluation, relativeFunctorSquarePost_uncurry,
    uncurry_natural_right]
  rw [show relativeFunctorUncurry (uncurry (a ≫
        (constantUnstraighteningSourceRelativeIso (i ≫ F) z).hom) ≫
        (unstraighteningSectionsRestrictionTargetIso F i).hom) =
      (K ◁ uncurry (a ≫ (constantUnstraighteningSourceRelativeIso (i ≫ F) z).hom)) ≫
        simplicialSectionsEvaluation (leftUnstraighteningProjection (i ≫ F)) ≫
          (leftUnstraighteningBaseChangeIso F i).hom ≫
            pullback.fst (leftUnstraighteningProjection F) i from
      sectionsRestrictionTargetIso_evaluation _ _ _ _ _ _]
  rw [leftUnstraighteningBaseChangeIso_hom_fst,
    ← Category.assoc (K ◁ uncurry (a ≫
      (constantUnstraighteningSourceRelativeIso (i ≫ F) z).hom)),
    constantUnstraighteningSourceRelativeIso_evaluation]
  simp only [Category.assoc]

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
