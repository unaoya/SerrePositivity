module

public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorPostLaws
public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftFibrationInfinityEquivalence
public import SerrePositivity.InfinityCategories.F1.Coherent.OrderPostcomposition
public import SerrePositivity.InfinityCategories.F2.Ind.WeightedNerveParameter

/-!
概要：固定底上の strict left fibration 図式の全相対切断を、同じ射の作用を持つ Kan 図式にする。
方針：元の相対 Hom の豊穣評価の通常の関手を使い、元の後合成との一致を証明する。
規約：各対象で切断や同値を選び直さず、一つの図式と一つの評価自然変換を構成する。
使われ方：共同 weighted 分類と strict 分類像を底の全単体上で比較する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {I : Type u} [Category.{u} I] {B A : SSet.{u}}
  (F : I ⥤ LeftFibrationObject B) (a : A ⟶ B)

/-- 同じ strict 図式の元の全空間の図式。 -/
def leftFibrationTotalDiagram : I ⥤ SSet.{u} where
  obj i := (F.obj i).val.left
  map f := (F.map f).left

/-- 同じ各段の元の射影を束ねた自然変換。 -/
def leftFibrationDiagramProjection :
    leftFibrationTotalDiagram F ⟶ (CategoryTheory.Functor.const I).obj B where
  app i := (F.obj i).val.hom
  naturality _ _ f := (Over.w (F.map f)).trans (Category.comp_id _).symm

/-- 元の同じ相対切断空間と元の後合成からなる strict Kan 図式。 -/
def strictLeftFibrationSectionDiagram : I ⥤ KanObject.{u} :=
  F ⋙ coherentEnrichedUnderlyingFunctor (relativeFunctorEnrichedEvaluation (Over.mk a))

/-- 同じ Kan 図式の射は、元の底上の射の相対後合成そのもの。 -/
lemma strictLeftFibrationSectionDiagram_map {i j : I} (f : i ⟶ j) :
    (strictLeftFibrationSectionDiagram F a).map f =
      HomotopyLimits.relativeFunctorPost (F.obj i).val.hom (F.obj j).val.hom
        (F.map f).left (Over.w (F.map f)) a := by
  apply functorVertex_injective
  have h := coherentEnrichedUnderlyingFunctor_vertex
    (relativeFunctorEnrichedEvaluation (Over.mk a)) (F.map f)
  rw [leftFibrationHom_vertex] at h
  exact h.trans (relativeFunctorPostHom_vertex (Over.mk a) (F.obj i).val
    (F.obj j).val (F.map f))

/-- 全切断の評価は、元の係数射の作用と厳密に可換な一つの自然変換。 -/
def strictLeftSectionEvaluation :
    (strictLeftFibrationSectionDiagram F a ⋙ kanObjectForget) ⋙ tensorRight A ⟶
      leftFibrationTotalDiagram F where
  app i := (β_ _ A).hom ≫ relativeFunctorUncurry (𝟙 _)
  naturality {i j} f := by
    change ((show ((strictLeftFibrationSectionDiagram F a).obj i).obj ⟶
      ((strictLeftFibrationSectionDiagram F a).obj j).obj from
        (strictLeftFibrationSectionDiagram F a).map f) ▷ A) ≫
      (β_ _ A).hom ≫ relativeFunctorUncurry (𝟙 _) =
      ((β_ _ A).hom ≫ relativeFunctorUncurry (𝟙 _)) ≫ (F.map f).left
    rw [strictLeftFibrationSectionDiagram_map]
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    rintro ⟨s, t⟩
    rfl

end SerrePositivity.InfinityCategories.F2.Ind
