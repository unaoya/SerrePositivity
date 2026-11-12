module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConstantSourceRelativeEvaluation

/-!
概要：制限後の定値全空間から元の標的への相対写像を、全 fiber の写像に移す。
方針：元の定値直積同型を底の射で後合成し、既存の相対指数則を使う。
規約：元の図式の標的を保持し、底の射も全パラメータも固定する。
使われ方：unstraightening の形状自然性を切断の全族比較へ写す。
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
open SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces

/-- 定値始域の元の直積表示を、指定された底の射で後合成する。 -/
def constantSourceRestrictedOverIso {B K : SSet.{u + 1}}
    (i : K ⟶ B) (z : SpaceInfinity.{u} _⦋0⦌) :
    Over.mk (leftUnstraighteningProjection (SSet.const z : K ⟶ _) ≫ i) ≅
      Over.mk (fst K (vertexFiber pointedSpaceProjection z) ≫ i) :=
  Over.isoMk
    (f := Over.mk (leftUnstraighteningProjection (SSet.const z : K ⟶ _) ≫ i))
    (g := Over.mk (fst K (vertexFiber pointedSpaceProjection z) ≫ i))
    (SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Pullbacks.pullbackConstantTensorIso
    pointedSpaceProjection z K) (by
      change (constantUnstraighteningSourceOverIso K z).hom.left ≫
        (fst K (vertexFiber pointedSpaceProjection z) ≫ i) = _
      rw [← Category.assoc]
      exact congrArg (fun a ↦ a ≫ i) (constantUnstraighteningSourceOverIso K z).hom.w)

/-- 制限された定値始域の相対関手空間を、全 fiber からの相対関手空間へ移す。 -/
def constantSourceRestrictedRelativeIso {B K : SSet.{u + 1}}
    (F : B ⟶ SpaceInfinity.{u}) (i : K ⟶ B) (z : SpaceInfinity.{u} _⦋0⦌) :
    relativeFunctorSpace (leftUnstraighteningProjection F)
      (leftUnstraighteningProjection (SSet.const z : K ⟶ _) ≫ i) ≅
      (ihom (vertexFiber pointedSpaceProjection z)).obj
        (relativeFunctorSpace (leftUnstraighteningProjection F) i) :=
  relativeFunctorOverIso (constantSourceRestrictedOverIso i z)
    (Iso.refl (Over.mk (leftUnstraighteningProjection F))) ≪≫
      relativeFunctorExponentialIso (leftUnstraighteningProjection F) i
        (vertexFiber pointedSpaceProjection z)

/-- 同じ相対指数同型の二重評価は、定値始域の元の逆表示による全評価。 -/
lemma constantSourceRestrictedRelativeIso_evaluation {B K T : SSet.{u + 1}}
    (F : B ⟶ SpaceInfinity.{u}) (i : K ⟶ B) (z : SpaceInfinity.{u} _⦋0⦌)
    (a : T ⟶ relativeFunctorSpace (leftUnstraighteningProjection F)
      (leftUnstraighteningProjection (SSet.const z : K ⟶ _) ≫ i)) :
    relativeFunctorUncurry (uncurry (a ≫ (constantSourceRestrictedRelativeIso F i z).hom)) =
      (α_ K (vertexFiber pointedSpaceProjection z) T).inv ≫
        ((constantUnstraighteningSourceOverIso K z).inv.left ▷ T) ≫
          relativeFunctorUncurry a := by
  dsimp only [constantSourceRestrictedRelativeIso, Iso.trans_hom]
  rw [← Category.assoc, relativeFunctorExponentialIso_evaluation,
    relativeFunctorOverIso_hom]
  simp only [Iso.refl_hom, Over.id_left, relativeFunctorPost_id, Category.comp_id]
  erw [relativeFunctorOverPre_uncurry]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
