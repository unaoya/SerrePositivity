module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomotopyClasses

/-!
概要：単体的ホモトピーの両端だけを厳密な等式で表示変更する。
方針：等式による輸送を使い、raw な円柱と辺の類を保持する。
規約：代表を選び直さない。使われ方：共通 end の四辺を同じ型付き端点へ揃える。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 両端の表示を変えても、同じホモトピー代表を使う。 -/
def homotopyEndpointTransport {A X : SSet.{u}} {f g f' g' : A ⟶ X}
    (H : SSet.Homotopy f g) (hf : f = f') (hg : g = g') : SSet.Homotopy f' g' :=
  hf ▸ hg ▸ H

/-- 端点の表示変更は、円柱の raw な射を厳密に保つ。 -/
lemma homotopyEndpointTransport_raw {A X : SSet.{u}} {f g f' g' : A ⟶ X}
    (H : SSet.Homotopy f g) (hf : f = f') (hg : g = g') :
    (homotopyEndpointTransport H hf hg).h = H.h := by
  subst f' g'
  rfl

/-- 型付き端点の表示変更後も、元の辺の類を Arrow として保持する。 -/
lemma homotopyEndpointTransport_hom_arrow {A X : SSet.{u}} {f g f' g' : A ⟶ X}
    (H : SSet.Homotopy f g) (hf : f = f') (hg : g = g') :
    Arrow.mk (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (homotopyEndpointTransport H hf hg))) =
      Arrow.mk (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H)) :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomotopy_hom_arrow_of_h_eq _ _ (homotopyEndpointTransport_raw H hf hg)

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
