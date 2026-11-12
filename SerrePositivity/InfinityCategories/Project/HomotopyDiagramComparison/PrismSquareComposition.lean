module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.HomotopyPrism
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.SquareComposition

/-!
概要：元の prism 正方形の四辺から、各点の Hom の合成式を回収。
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

/-- 元の比較正方形を、指定頂点の定値単体の全次数で制限する。 -/
def prismSquareAt {A E : SSet.{u}}
    (J : (Δ[1] : SSet.{u}) ⊗ ((Δ[1] : SSet.{u}) ⊗ A) ⟶ E) (x : A _⦋0⦌) :
    (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ E :=
  ((Δ[1] : SSet.{u}) ◁ lift (𝟙 (Δ[1] : SSet.{u})) (SSet.const x)) ≫ J

/-- 元の正方形の四辺から、同じ三つの指定ホモトピーの成分の合成式を導く。 -/
lemma prismSquareAt_component_comp {A E : SSet.{u}} [Quasicategory E]
    {U V W : A ⟶ E} (Hη : SSet.Homotopy U V) (HK : SSet.Homotopy V W)
    (HL : SSet.Homotopy U W)
    (J : (Δ[1] : SSet.{u}) ⊗ ((Δ[1] : SSet.{u}) ⊗ A) ⟶ E)
    (hb : ((Δ[1] : SSet.{u}) ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A) ≫ J = snd Δ[1] A ≫ U)
    (ht : ((Δ[1] : SSet.{u}) ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A) ≫ J =
      (β_ (Δ[1] : SSet.{u}) A).hom ≫ HK.h)
    (hl : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ J = (β_ (Δ[1] : SSet.{u}) A).hom ≫ Hη.h)
    (hr : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _ ≫ J = (β_ (Δ[1] : SSet.{u}) A).hom ≫ HL.h)
    (x : A _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (SSet.Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy Hη)) x ≫
      _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy HK)) x =
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (SSet.Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy HL)) x := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomEvaluate_homotopy, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomEvaluate_homotopy, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomEvaluate_homotopy]
  let Q := prismSquareAt J x
  have hi : SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge := by
    apply SSet.stdSimplex.ext
    intro i
    fin_cases i <;> rfl
  have hq := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.homMk_comp_eq_of_square
    (SSet.Truncated.Edge.id (X := (truncation 2).obj E) (U.app (Opposite.op ⦋0⦌) x))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge HK x).toTruncated
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge Hη x).toTruncated
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge HL x).toTruncated Q ?_ ?_ ?_ ?_
  · rw [SSet.Truncated.HomotopyCategory.homMk_id, Category.id_comp] at hq
    exact hq.symm
  · have hQ : SSet.ι₀ ≫ Q = (SSet.const (U.app (Opposite.op ⦋0⦌) x) : Δ[1] ⟶ E) := by
      have hex : SSet.ι₀ ≫ ((Δ[1] : SSet.{u}) ◁
          lift (𝟙 (Δ[1] : SSet.{u})) (SSet.const x)) =
        lift (𝟙 (Δ[1] : SSet.{u})) (SSet.const x) ≫
          ((Δ[1] : SSet.{u}) ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A) := by rfl
      change SSet.ι₀ ≫ (((Δ[1] : SSet.{u}) ◁
        lift (𝟙 (Δ[1] : SSet.{u})) (SSet.const x)) ≫ J) = _
      rw [← Category.assoc, hex, Category.assoc, hb]
      change (SSet.const x : Δ[1] ⟶ A) ≫ U = _
      exact SSet.const_comp x U
    change Q.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge, _) = _
    rw [← hi]
    change SSet.yonedaEquiv (SSet.ι₀ ≫ Q) = _
    rw [hQ]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one _
  · have hQ : SSet.ι₁ ≫ Q =
        lift (𝟙 (Δ[1] : SSet.{u})) (SSet.const x) ≫
          (β_ (Δ[1] : SSet.{u}) A).hom ≫ HK.h := by
      have hex : SSet.ι₁ ≫ ((Δ[1] : SSet.{u}) ◁
          lift (𝟙 (Δ[1] : SSet.{u})) (SSet.const x)) =
        lift (𝟙 (Δ[1] : SSet.{u})) (SSet.const x) ≫
          ((Δ[1] : SSet.{u}) ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A) := by rfl
      change SSet.ι₁ ≫ (((Δ[1] : SSet.{u}) ◁
        lift (𝟙 (Δ[1] : SSet.{u})) (SSet.const x)) ≫ J) = _
      rw [← Category.assoc, hex, Category.assoc, ht]
    change Q.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge, _) = _
    rw [← hi]
    change SSet.yonedaEquiv (SSet.ι₁ ≫ Q) = _
    rw [hQ, SSet.yonedaEquiv_comp]
    change HK.h.app (Opposite.op ⦋1⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1, SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u}))) =
        HK.h.app (Opposite.op ⦋1⦌)
          ((SSet.Truncated.Edge.id (X := (truncation 2).obj A) x).edge, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge)
    rw [hi, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one]
  · have hQ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 Δ[1] ≫ Q =
        lift (𝟙 (Δ[1] : SSet.{u})) (SSet.const x) ≫
          (β_ (Δ[1] : SSet.{u}) A).hom ≫ Hη.h := by
      change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 Δ[1] ≫ (((Δ[1] : SSet.{u}) ◁
        lift (𝟙 (Δ[1] : SSet.{u})) (SSet.const x)) ≫ J) = _
      rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc, hl]
    change Q.app (Opposite.op ⦋1⦌) (_, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge) = _
    rw [← hi]
    change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 Δ[1] ≫ Q) = _
    rw [hQ, SSet.yonedaEquiv_comp]
    change Hη.h.app (Opposite.op ⦋1⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1, SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u}))) =
        Hη.h.app (Opposite.op ⦋1⦌)
          ((SSet.Truncated.Edge.id (X := (truncation 2).obj A) x).edge, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge)
    rw [hi, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one]
  · have hQ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 Δ[1] ≫ Q =
        lift (𝟙 (Δ[1] : SSet.{u})) (SSet.const x) ≫
          (β_ (Δ[1] : SSet.{u}) A).hom ≫ HL.h := by
      change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 Δ[1] ≫ (((Δ[1] : SSet.{u}) ◁
        lift (𝟙 (Δ[1] : SSet.{u})) (SSet.const x)) ≫ J) = _
      rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc, hr]
    change Q.app (Opposite.op ⦋1⦌) (_, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge) = _
    rw [← hi]
    change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 Δ[1] ≫ Q) = _
    rw [hQ, SSet.yonedaEquiv_comp]
    change HL.h.app (Opposite.op ⦋1⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1, SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u}))) =
        HL.h.app (Opposite.op ⦋1⦌)
          ((SSet.Truncated.Edge.id (X := (truncation 2).obj A) x).edge, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge)
    rw [hi, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one]

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
