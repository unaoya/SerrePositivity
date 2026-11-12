module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.StrictLeftSectionWeightedEvaluation

/-!
概要：strict 図式の全相対切断の制限は、一つの自然変換で全添字と両評価を保つ。
方針：相対後合成と前合成の可換性を使い、元の全切断評価で制限を照合する。
規約：底の射は任意。頂点ごとの同値の選択や追加のモデル圏仮定を置かない。
使われ方：底の単体の面・退化を同時に保つ weighted 分類の比較。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable {I : Type u} [Category.{u} I] {B A D : SSet.{u}}
  (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B) (a : A ⟶ B) (k : D ⟶ A)

/-- 同じ底上の制限を全添字で同時に適用する、相対切断図式の自然変換。 -/
def strictLeftSectionRestriction :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.strictLeftFibrationSectionDiagram F a ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.strictLeftFibrationSectionDiagram F (k ≫ a) where
  app i := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre (F.obj i).val.hom a k
  naturality {i j} f := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.strictLeftFibrationSectionDiagram_map, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.strictLeftFibrationSectionDiagram_map]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPost_pre (F.obj i).val.hom (F.obj j).val.hom
      (F.map f).left (Over.w (F.map f)) a k

/-- 係数の同じ全評価は、元の底の任意の制限と厳密に可換。 -/
lemma strictLeftSectionEvaluation_restriction (i : I) :
    ((show ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.strictLeftFibrationSectionDiagram F a).obj i).obj ⟶
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.strictLeftFibrationSectionDiagram F (k ≫ a)).obj i).obj from
        (strictLeftSectionRestriction F a k).app i) ▷ D) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.strictLeftSectionEvaluation F (k ≫ a)).app i =
        (((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.strictLeftFibrationSectionDiagram F a).obj i).obj ◁ k) ≫
          (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.strictLeftSectionEvaluation F a).app i := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨s, t⟩
  rfl

/-- 二段の元の制限は、同じ切断の全図式上で厳密に合成される。 -/
lemma strictLeftSectionRestriction_comp {K : SSet.{u}} (l : K ⟶ D) :
    strictLeftSectionRestriction F a k ≫ strictLeftSectionRestriction F (k ≫ a) l =
      strictLeftSectionRestriction F a (l ≫ k) := by
  apply NatTrans.ext
  funext i
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre_comp (F.obj i).val.hom a k l

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
