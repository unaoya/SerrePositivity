module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PrismOpposite
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianOpposite

/-!
概要：反対圏の coCartesian な輸送 prism を元の Cartesian な prism へ戻す。
方針：二重反転の式で底の辺を回収し、外側ホーンの反転で辺の性質を移す。
規約：底と全空間のモデル構造を要求しない。使われ方：右導来関手の輸送の証人。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

/-- 反転から戻す操作は、元の底写像による後合成と可換である。 -/
lemma unreversePrism_postcomp {A E B : SSet.{u}}
    (H : (Δ[1] : SSet.{u}) ⊗ A.op ⟶ E.op) (p : E ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.unreversePrism (H ≫ SSet.opFunctor.map p) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.unreversePrism H ≫ p := by rfl

/-- 反対の辺上の prism を戻すと、元の辺上の prism に一致する。 -/
lemma unreversePrism_base {A B : SSet.{u}} {a b : B _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj B) a b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.unreversePrism (A := A) (Y := B)
      (fst (Δ[1] : SSet.{u}) A.op ≫ SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp e).edge) =
      fst (Δ[1] : SSet.{u}) A ≫ SSet.yonedaEquiv.symm e.edge := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨t, v⟩
  change B.map (SimplexCategory.rev.map _).op e.edge = B.map (Quiver.Hom.op _) e.edge
  apply congrArg (fun f : ⦋d⦌ ⟶ ⦋1⦌ ↦ B.map f.op e.edge)
  apply SimplexCategory.Hom.ext
  apply DFunLike.ext
  intro i
  change ((t i.rev.rev).rev).rev = t i
  simp

/-- 反対圏の全垂直辺が coCartesian なら、元へ戻した全垂直辺は Cartesian である。 -/
lemma unreversePrism_vertical_isCartesian {A E B : SSet.{u}} (p : E ⟶ B)
    (H : (Δ[1] : SSet.{u}) ⊗ A.op ⟶ E.op)
    (hc : ∀ v : A.op _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge (SSet.opFunctor.map p)
      (H.app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant v 1)))
    (v : A _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge p
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.unreversePrism H).app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant v 1)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCartesianEdge_of_isCocartesianEdge_op p
  have he : SSet.opObjEquiv.symm ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.unreversePrism H).app (Opposite.op ⦋1⦌)
      (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant v 1)) =
    H.app (Opposite.op ⦋1⦌)
      (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})),
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (SSet.opObjEquiv.symm v) 1) := by
    change H.app _ (_, _) = H.app _ (_, _)
    congr 1
    apply Prod.ext
    · apply SSet.stdSimplex.ext
      intro i
      fin_cases i <;> rfl
    · rfl
  rw [he]
  exact hc (SSet.opObjEquiv.symm v)

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
