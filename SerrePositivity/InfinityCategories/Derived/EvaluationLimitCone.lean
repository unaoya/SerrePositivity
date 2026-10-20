module
public import SerrePositivity.InfinityCategories.Derived.WeaklyContractibleConstantLimit
public import SerrePositivity.InfinityCategories.F2.SpecifiedLimitConeTransport
/-!
概要：弱可縮な全添字の可逆評価から、同じ頂点を持つ追跡可能な実極限錐を構成する。
方針：指定された全ホモトピーを左区間 prism として極限錐輸送に入力する。
規約：図式と頂点の全時刻の境界を保持。使われ方：反転された実分母図式の実極限錐。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
/-- 右因子のホモトピーを、同じ全時刻の左因子 prism として読む。 -/
def evaluationHomotopyPrism {K X : SSet.{u}} {f g : K ⟶ X}
    (H : SSet.Homotopy f g) : (Δ[1] : SSet.{u}) ⊗ K ⟶ X :=
  (β_ (Δ[1] : SSet.{u}) K).hom ≫ H.h
/-- 指定ホモトピーの左因子 prism の一次単体は、元の同じ成分辺。 -/
lemma evaluationHomotopyPrism_vertical {K X : SSet.{u}} {f g : K ⟶ X}
    (H : SSet.Homotopy f g) (x : K _⦋0⦌) :
    (evaluationHomotopyPrism H).app (Opposite.op ⦋1⦌)
      (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), PinchedHom.constant x 1) =
        (simplicialHomotopyVertexEdge H x).edge := by
  have hi : SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})) = homotopyIntervalEdge.edge := by
    apply SSet.stdSimplex.ext
    intro j
    fin_cases j <;> rfl
  change H.h.app (Opposite.op ⦋1⦌)
    (PinchedHom.constant x 1, SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u}))) =
      H.h.app (Opposite.op ⦋1⦌)
        ((Truncated.Edge.id (X := (truncation 2).obj K) x).edge, homotopyIntervalEdge.edge)
  rw [hi, pinchedConstant_one]
/-- 全添字の可逆評価に沿う実極限錐輸送。頂点と全境界の証拠を保持する。 -/
def evaluationLimitConeTransport {K X : SSet.{u}} [Quasicategory X]
    (hK : IsWeaklyContractible K) {f : K ⟶ X} (x : X _⦋0⦌)
    (H : SSet.Homotopy f (SSet.const x))
    (hH : ∀ a, IsInvertibleEdge (simplicialHomotopyVertexEdge H a).toTruncated) :
    F2.SpecifiedLimitConeTransport (p := f) (evaluationHomotopyPrism H)
      (constantDiagramCone K X x) :=
  F2.specifiedLimitConeTransport (evaluationHomotopyPrism H) H.h₀ H.h₁ (by
    intro a
    exact (isInvertibleEdge_congr (evaluationHomotopyPrism_vertical H a)).mpr (hH a))
    (constantDiagramCone K X x) (constantDiagramCone_isLimit K X hK x)
/-- 可逆評価から構成した実極限錐は、元の指定評価頂点を厳密に持つ。 -/
lemma evaluationLimitConeTransport_vertex {K X : SSet.{u}} [Quasicategory X]
    (hK : IsWeaklyContractible K) {f : K ⟶ X} (x : X _⦋0⦌)
    (H : SSet.Homotopy f (SSet.const x))
    (hH : ∀ a, IsInvertibleEdge (simplicialHomotopyVertexEdge H a).toTruncated) :
    (evaluationLimitConeTransport hK x H hH).cone.vertex = x :=
  (evaluationLimitConeTransport hK x H hH).vertex_eq.trans (constantDiagramCone_vertex K X x)
end SerrePositivity.InfinityCategories
