module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresheafOppositeRightKanCriterion

/-!
概要：既存の小さい元の圏から Kan 局所形状への比較は、元の底への射影を保つ。
方針：既存の Yoneda slice 比較、引き戻しの交換、反転の射影の等式を合成する。
規約：新しい比較写像を選ばず、既存の同じ比較の係数の等式を証明する。
使われ方：Kerodon §9.5（Tag 06NC）、HTT 5.1.5.6 の重み付き切断の指定値。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
variable {A : SSet.{u}} [Quasicategory A]
  (P : (SSet.uliftFunctor.{u + 1, u}).obj A.op ⟶ SpaceInfinity.{u})

/-- 小さい元の圏から左 Kan 局所形状への既存の比較は、元の底への射影を保つ。
Kerodon §9.5（Tag 06NC）、引き戻しの交換と既存の密度比較の射影の合成則。 -/
lemma presheafElementsLeftKanComparison_projection :
    presheafElementsLeftKanComparison P ≫
      leftKanProjection (yonedaInfinityMap A) (functorVertex P) =
    (SSet.uliftFunctor.{u + 1, u}).map (smallRightUnstraighteningProjection P) := by
  dsimp only [presheafElementsLeftKanComparison, leftKanProjection]
  simp only [Category.assoc]
  erw [pullbackSymmetry_inv_comp_fst]
  exact presheafElementsYonedaSliceComparison_projection P

/-- 同じ比較を反転した右 Kan 局所形状でも、元の底の射影を保つ。
Kerodon §9.5（Tag 06NC）、反転と局所形状の指定同型の射影の合成則。 -/
lemma presheafElementsRightKanComparison_projection :
    presheafElementsRightKanComparison P ≫
      rightKanProjection (SSet.opFunctor.map (yonedaInfinityMap A))
        (SSet.opObjEquiv.symm (functorVertex P)) =
    SSet.opFunctor.map
      ((SSet.uliftFunctor.{u + 1, u}).map (smallRightUnstraighteningProjection P)) := by
  rw [presheafElementsRightKanComparison, Category.assoc, kanLeftKanShapeOpIso_projection,
    ← Functor.map_comp, presheafElementsLeftKanComparison_projection]

/-- 小さい left 全空間へ反転して戻した同じ比較は、元の left 射影と反対の底同型を保つ。
Kerodon §9.5（Tag 06NC）、二重反転・宇宙変更・係数移送の合成則。 -/
lemma presheafElementsRightKanComparison_leftProjection :
    (SSet.uliftFunctor.{u + 1, u}).map (smallRightUnstraighteningOppositeIso P).inv ≫
      (uliftOppositeIso (smallRightUnstraightening P)).hom ≫
        presheafElementsRightKanComparison P ≫
          rightKanProjection (SSet.opFunctor.map (yonedaInfinityMap A))
            (SSet.opObjEquiv.symm (functorVertex P)) =
    (SSet.uliftFunctor.{u + 1, u}).map (smallLeftUnstraighteningProjection P) ≫
      (uliftOppositeIso A).hom := by
  have hn : (uliftOppositeIso (smallRightUnstraightening P)).hom ≫
      SSet.opFunctor.map ((SSet.uliftFunctor.{u + 1, u}).map
        (smallRightUnstraighteningProjection P)) =
      (SSet.uliftFunctor.{u + 1, u}).map
        (SSet.opFunctor.map (smallRightUnstraighteningProjection P)) ≫
          (uliftOppositeIso A).hom := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    rfl
  have hi : (SSet.uliftFunctor.{u + 1, u}).map (smallRightUnstraighteningOppositeIso P).inv ≫
      (SSet.uliftFunctor.{u + 1, u}).map
        (SSet.opFunctor.map (smallRightUnstraighteningProjection P)) =
      (SSet.uliftFunctor.{u + 1, u}).map (smallLeftUnstraighteningProjection P) := by
    rw [← Functor.map_comp, smallRightUnstraighteningProjection_op, Iso.inv_hom_id_assoc]
  calc
    _ = (SSet.uliftFunctor.{u + 1, u}).map (smallRightUnstraighteningOppositeIso P).inv ≫
        (uliftOppositeIso (smallRightUnstraightening P)).hom ≫
          SSet.opFunctor.map ((SSet.uliftFunctor.{u + 1, u}).map
            (smallRightUnstraighteningProjection P)) :=
      congrArg (fun f =>
        (SSet.uliftFunctor.{u + 1, u}).map (smallRightUnstraighteningOppositeIso P).inv ≫
          (uliftOppositeIso (smallRightUnstraightening P)).hom ≫ f)
        (presheafElementsRightKanComparison_projection P)
    _ = (SSet.uliftFunctor.{u + 1, u}).map (smallRightUnstraighteningOppositeIso P).inv ≫
        (SSet.uliftFunctor.{u + 1, u}).map
          (SSet.opFunctor.map (smallRightUnstraighteningProjection P)) ≫
            (uliftOppositeIso A).hom :=
      congrArg (fun f =>
        (SSet.uliftFunctor.{u + 1, u}).map (smallRightUnstraighteningOppositeIso P).inv ≫ f) hn
    _ = _ := by rw [← Category.assoc, hi]

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
