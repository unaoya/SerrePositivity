module
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanHomotopyEquivalence

/-! # 両端の等式によるホモトピーの表示変更

概要：ホモトピーの積からの写像を保ち、両端だけを指定の等しい写像へ合わせる。
方針：両端条件に指定された等式を合成する。
規約：写像そのものを等式で消去しない。使われ方：D7 の具体的な四角形比較の端点正規化。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open CategoryTheory

/-- 両端の表示を変えても同じ積からの写像を使える。 -/
def homotopyOfEndpoints {A B : SSet.{u}} {f g f' g' : A ⟶ B}
    (H : SSet.Homotopy f g) (hf : f = f') (hg : g = g') : SSet.Homotopy f' g' where
  h := H.h
  h₀ := H.h₀.trans hf
  h₁ := H.h₁.trans hg
  rel := by
    ext n q
    exact False.elim q.1.2

/-- 表示変更はホモトピーの実際の写像を保つ。 -/
lemma homotopyOfEndpoints_h {A B : SSet.{u}} {f g f' g' : A ⟶ B}
    (H : SSet.Homotopy f g) (hf : f = f') (hg : g = g') :
    (homotopyOfEndpoints H hf hg).h = H.h := rfl

/-- 両端の表示変更は関手圏の h の射も Arrow として保つ。 -/
lemma homotopyOfEndpoints_functorHom_arrow {A B : SSet.{u}} {f g f' g' : A ⟶ B}
    (H : SSet.Homotopy f g) (hf : f = f') (hg : g = g') :
    Arrow.mk (SSet.Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (homotopyOfEndpoints H hf hg))) =
    Arrow.mk (SSet.Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H)) := by
  apply SSet.Truncated.HomotopyCategory.congr_arrowMk_homMk
  rfl

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
