module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeSectionOrdinaryAction
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedRealizationValueHom
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SectionBaseChangeRealizationComposition

/-!
概要：指定した反復引き戻し切断比較の値を、元の全空間同型の作用として読む。
方針：同じ共同比較の係数値と、相対後合成の実現の法則を照合する。
規約：標準同型の逆射による直接引き戻しから反復引き戻しへの向きを保つ。
使われ方：Kerodon §5.6（Tag 027M）の分類における、指定底変換の貼り合わせ法則。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open Kerodon.LimitsAndColimits.LimitsAndColimits
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories
namespace ClassificationOfCocartesianFibrations

local instance sectionCompValue_pullbackLeft {E B D : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) : LeftFibration (pullback.snd p k) :=
  ⟨leftFibrations.pullback_snd p k (LeftFibration.mem (p := p))⟩

/-- 概要：反復引き戻しの指定共同比較の実現値は、同じ標準同型の逆射の作用。
方針：元の比較成分と元の相対後合成は定義から同じであることを使う。
規約：任意の反変底図式全体の射として比較する。使われ方：分類した貼り合わせ射の照合。 -/
lemma sectionBaseChangeCompComparison_value_hom {E B D T : SSet.{u}}
    {J : Type u} [Category.{u} J] (p : E ⟶ B) [LeftFibration p]
    (k : D ⟶ B) (l : T ⟶ D) (A : Jᵒᵖ ⥤ Over T) :
    (kanEnrichedRealizationValueIso (sectionBaseChangeCompComparison k l A)
      (sectionBaseChangeCompComparison_isQCatEquivalence k l A) (leftFibrationObjectOf p)).hom =
      normalizedVertexHomMap (relativeSectionEnrichedDiagram A).realization
        ((relativeSectionEnrichedDiagram A).realization_vertex
          (leftFibrationObjectOf (pullback.snd p (l ≫ k)))).symm
        ((relativeSectionEnrichedDiagram A).realization_vertex
          (leftFibrationObjectOf (pullback.snd (pullback.snd p k) l))).symm
        (Truncated.HomotopyCategory.homMk (leftFibrationInfinityEdge
          (pullback.snd p (l ≫ k)) (pullback.snd (pullback.snd p k) l)
          (pullbackLeftPullbackSndIso p k l).inv
          (pullbackLeftPullbackSndIso_inv_snd_snd p k l)).toTruncated) := by
  rw [kanEnrichedRealizationValueIso_hom, relativeSectionRealization_homMk]
  rfl

end ClassificationOfCocartesianFibrations
end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories
