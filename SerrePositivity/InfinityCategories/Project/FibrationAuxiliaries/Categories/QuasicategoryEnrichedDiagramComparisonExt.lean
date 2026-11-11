module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagramComparison

/-!
概要：元の各比較成分が等しい豊穣図式比較は等しい。
方針：元の全対象で関数外延性を使い、自然性の証明は証明無関連性で消す。
規約：同じ図式の比較そのものの等式。
使われ方：底変換の合成比較を既存の直接の比較へ厳密に戻す。
-/

@[expose] public section
universe u v
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories

/-- 全対象の同じ各成分を持つ元の豊穣図式比較は等しい。 -/
lemma QuasicategoryEnrichedDiagramComparison.extPointwise
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {J : Type u} [Category.{u} J] {D E : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagram C J}
    {η θ : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagramComparison D E}
    (h : ∀ j X, (η.app j).val X = (θ.app j).val X) : η = θ := by
  cases η with
  | mk a ha =>
    cases θ with
    | mk b hb =>
      have hab : a = b := by
        funext j
        apply Subtype.ext
        funext X
        exact h j X
      cases hab
      rfl

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories
