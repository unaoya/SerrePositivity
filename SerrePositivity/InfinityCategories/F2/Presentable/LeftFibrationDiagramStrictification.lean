module

public import SerrePositivity.InfinityCategories.F2.Ind.StrictLeftWeightedClassification
public import SerrePositivity.InfinityCategories.F2.Ind.UnderSectionClassification
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftStraighteningInfinityEquivalence

/-!
概要：left fibration ∞ 圏の coherent な通常添字の全図式を、同じ添字で strict 化する。
方針：元の分類像の共同評価を復元し、既存の under 切断の全分類比較を curry して戻す。
規約：元の図式との一つの全関手同型を保持し、値ごとの同値で代用しない。
使われ方：有限始域の相対 Hom の一般 coherent filtered 余極限保存。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits
variable {I : Type u} [SmallCategory I] {B : SSet.{u}} [Quasicategory B]
  (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ⟶ LeftFibrationInfinity B)

/-- 概要：元の分類像を底と添字の両変数で共同評価する。
方針：同じ全図式を uncurry し、積の宇宙持ち上げを比較する。
規約：底 B と通常添字 I の全高次単体を保持する。
使われ方：同じ積上の小さい left fibration の復元。 -/
def leftFibrationDiagramJointEvaluation :
    (SSet.uliftFunctor.{u + 1, u}).obj (B ⊗ nerve I) ⟶ SpaceInfinity.{u} :=
  (uliftTensorIso.{u, u + 1} B (nerve I)).hom ≫
    uncurry (F ≫ leftStraighteningInfinityMap B)

/-- 概要：元の共同評価から同じ底上の strict left fibration 図式を構成する。
方針：小さい unstraightening に既存の under 切断構成を適用する。
規約：strict な恒等・合成を持つ同じ通常添字を使う。
使われ方：元の coherent filtered 図式に比較する通常模型。 -/
def leftFibrationDiagramStrictification : I ⥤ LeftFibrationObject B :=
  Ind.underSectionStrictDiagram
    (smallLeftUnstraighteningProjection (leftFibrationDiagramJointEvaluation F))

/-- 概要：同じ strict 模型の coherent 実現は元の図式全体と関手同型である。
方針：共同 weighted 分類と復元の余単位を curry し、分類の充満忠実性で戻す。
規約：全添字上の自然性を保持する。
使われ方：任意の指定余錐への strict 模型の余極限保存の移送。 -/
def leftFibrationDiagramStrictificationIso :
    FunctorIso (strictCoherentDiagram (leftFibrationDiagramStrictification F)) F := by
  let p := smallLeftUnstraighteningProjection (leftFibrationDiagramJointEvaluation F)
  have h : FunctorIso
      (leftStraighteningInfinityDiagram (Ind.underSectionWeightedProjection p))
      (leftFibrationDiagramJointEvaluation F) :=
    (Ind.underSectionClassificationIso p).symm ≪≫
    leftStraighteningInfinityCounit (leftFibrationDiagramJointEvaluation F)
  have hc := (h.precomp (uliftTensorIso.{u, u + 1} B (nerve I)).inv).curry
  have hw : FunctorIso
      (Ind.strictLeftWeightedClassification (leftFibrationDiagramStrictification F))
      (F ≫ leftStraighteningInfinityMap B) := by
    have hc' : FunctorIso
        (curry ((uliftTensorIso.{u, u + 1} B (nerve I)).inv ≫
          leftStraighteningInfinityDiagram (Ind.underSectionWeightedProjection p)))
        (F ≫ leftStraighteningInfinityMap B) := by
      simpa only [leftFibrationDiagramJointEvaluation, ← Category.assoc, Iso.inv_hom_id,
        Category.id_comp, curry_uncurry] using hc
    exact hc'
  exact (leftStraighteningInfinityMap_isQCatEquivalence B).isFullyFaithful.preimageFunctorIso
    ((Ind.strictLeftWeightedClassificationIso (leftFibrationDiagramStrictification F)).symm ≪≫ hw)

end SerrePositivity.InfinityCategories.F2.Presentable
