module
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorOpposite
/-!
概要：反対へ移した同じ全関手ホモトピーの頂点辺を、元の辺の反対へ同定する。
方針：F1B の実 prism 反転を使い、恒等辺と区間辺を全一次単体で照合する。
規約：quasicategory 性は要求しない。使われ方：普遍余単位の向きと実成分の回収。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open CategoryTheory SSet
open scoped _root_.Simplicial
/-- 反転した同じ実ホモトピーの頂点辺は、元の頂点辺の反対そのもの。 -/
lemma kanHomotopyOpposite_vertex_edge {X Y : SSet.{u}} {f g : X ⟶ Y}
    (H : SSet.Homotopy f g) (x : X _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.homotopyOpposite H) (SSet.opObjEquiv.symm x)).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H x)).edge := by
  change SSet.opObjEquiv.symm (H.h.app (Opposite.op ⦋1⦌) (_, _)) =
    SSet.opObjEquiv.symm (H.h.app (Opposite.op ⦋1⦌) (_, _))
  congr 2
  apply Prod.ext
  · change SSet.opObjEquiv (X.op.σ 0 (SSet.opObjEquiv.symm x)) = X.σ 0 x
    rw [SSet.op_σ]
    rfl
  · apply SSet.stdSimplex.ext
    intro i
    fin_cases i <;> rfl
end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
