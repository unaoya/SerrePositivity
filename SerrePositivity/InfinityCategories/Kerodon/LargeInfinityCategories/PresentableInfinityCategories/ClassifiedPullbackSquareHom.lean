module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ClassifiedSquareHomNaturality
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.HomClassificationLaws

/-!
概要：標準の引き戻し正方形の分類射を指定底変換同型の逆射と照合する。
方針：標準の持ち上げが恒等射であることと恒等射の分類則を使う。
規約：底変換同型を選び直さない。使われ方：E01 の始点固定の比較正方形。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open SerrePositivity.InfinityCategories
open Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories
namespace PresentableInfinityCategories

attribute [local instance] supplyClassifiedSquareHomNaturality_pullbackLeftFibration

/-- 概要：標準の引き戻し正方形を分類すると同じ指定底変換の逆射になる。
方針：持ち上げを恒等射と同定し、恒等射の分類則を適用する。
規約：任意の準圏の間の射と左 fibration を扱う。
使われ方：Kerodon Tag 03M5・03W8、HTT 5.1.3.1・5.1.5.3 の
E01 の始点固定の正方形を計算する法則。 -/
lemma leftClassificationSquareHom_pullback {A B H : SSet.{u}}
    [Quasicategory A] [Quasicategory B] (p : H ⟶ B) [LeftFibration p]
    (k : A ⟶ B) :
    leftClassificationSquareHom (pullback.snd p k) p k
      (pullback.fst p k) (pullback.condition (f := p) (g := k)) =
      (leftStraighteningInfinityDiagram_baseChangeIso p k).inv := by
  unfold leftClassificationSquareHom
  have h : pullback.lift (pullback.fst p k) (pullback.snd p k)
      (pullback.condition (f := p) (g := k)) = 𝟙 (pullback p k) := by
    apply pullback.hom_ext <;> simp
  simp only [h, leftClassificationHom_id, Category.id_comp]

end PresentableInfinityCategories
end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories
