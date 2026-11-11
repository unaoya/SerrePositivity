module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.PrismContraction

/-!
概要：指定 prism の元の両端・各点の辺・底を保つホモトピー表示。
方針：元の辺と正方形を保持して、標準の写像空間比較へ移す。
規約：元の cf 置換との比較と一般 coherent 極限保存は別工程。使われ方：HTT 5.2.4.6。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

/-- 元の両端を指定した prism を、同じ raw な射を持つホモトピーにする。 -/
def homotopyOfPrism {A E : SSet.{u}} {U V : A ⟶ E}
    (P : (Δ[1] : SSet.{u}) ⊗ A ⟶ E)
    (h0 : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ P = U) (h1 : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ P = V) :
    SSet.Homotopy U V where
  h := (β_ A (Δ[1] : SSet.{u})).hom ≫ P
  h₀ := by change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ P = _; exact h0
  h₁ := by change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ P = _; exact h1
  rel := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro a
    exact False.elim a.1.property

/-- 各点の評価辺は、元の prism の指定垂直辺と一致する。 -/
lemma homotopyOfPrism_vertexEdge {A E : SSet.{u}} {U V : A ⟶ E}
    (P : (Δ[1] : SSet.{u}) ⊗ A ⟶ E)
    (h0 : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ P = U) (h1 : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ P = V) (x : A _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (homotopyOfPrism P h0 h1) x).edge =
      P.app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1) := by
  have hi : SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge := by
    apply SSet.stdSimplex.ext
    intro i
    fin_cases i <;> rfl
  change P.app (Opposite.op ⦋1⦌)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge, (SSet.Truncated.Edge.id (X := (truncation 2).obj A) x).edge) = _
  rw [hi, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one]

/-- 元の標準区間上の prism は、同じ区間を底とするホモトピーを与える。 -/
lemma homotopyOfPrism_projection {A E : SSet.{u}} {U V : A ⟶ E}
    (P : (Δ[1] : SSet.{u}) ⊗ A ⟶ E)
    (h0 : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ P = U) (h1 : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ P = V)
    (p : E ⟶ (Δ[1] : SSet.{u})) (hp : P ≫ p = fst (Δ[1] : SSet.{u}) A) :
    (homotopyOfPrism P h0 h1).h ≫ p = snd A (Δ[1] : SSet.{u}) := by
  change (β_ A (Δ[1] : SSet.{u})).hom ≫ (P ≫ p) = _
  rw [hp]
  rfl

/-- 指定ホモトピーの評価は、元の標的関手による後合成と可換である。 -/
lemma functorHomEvaluate_homotopy_postcomp {A X E : SSet.{u}} {U V : A ⟶ X}
    (H : SSet.Homotopy U V) (i : X ⟶ E) (x : A _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (SSet.Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp H i))) x =
    (hoFunctor.map i).toFunctor.map (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate
      (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H)) x) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomEvaluate_homotopy, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomEvaluate_homotopy]
  change SSet.Truncated.HomotopyCategory.homMk _ =
    SSet.Truncated.HomotopyCategory.homMk _
  congr 1

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
