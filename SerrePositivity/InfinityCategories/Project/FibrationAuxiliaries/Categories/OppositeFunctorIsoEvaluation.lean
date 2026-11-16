module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.OppositeFunctorIsoWhisker
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FunctorIsoVertexEvaluation
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorOppositeHom
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyRepresentative
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.HomotopyOppositeEdges
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorIsoPointEvaluation
/-!
概要：元の反転 Hom 対応と指定された全同型の逆成分の一点評価。
方針：同じホモトピーの代表と反転した円柱の辺を比較し、既存の成分評価の式を使う。
規約：元の反転対応と同じ逆成分を保持する。模型構造と計算上限は増やさない。
使われ方：元の source-frame augmentation の逆成分を反転ホモトピー圏から戻す。
-/

@[expose] public section
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries
open SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories
open SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
open CategoryTheory SSet MonoidalCategory MonoidalClosed
open scoped Simplicial
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.HA.StableInfinityCategories
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories

/-- 同じ反転ホモトピーの頂点の辺を戻すと、元の同じ頂点の辺になる。 -/
lemma oppositeHomotopyVertexEdge_unop {A D : SSet.{u}} {F G : A ⟶ D}
    (H : SSet.Homotopy F G) (x : A _⦋0⦌) :
    edgeUnop (X := D) (simplicialHomotopyVertexEdge (homotopyOpposite H)
      (SSet.opObjEquiv.symm x)).toTruncated =
        (simplicialHomotopyVertexEdge H x).toTruncated := by
  apply SSet.Truncated.Edge.ext
  change H.h.app (Opposite.op ⦋1⦌)
    (SSet.opObjEquiv (SSet.Truncated.Edge.id (X := (truncation 2).obj A.op)
      (SSet.opObjEquiv.symm x)).edge,
      SSet.opObjEquiv ((stdSimplex.opIso ⦋1⦌).inv.app (Opposite.op ⦋1⦌)
        SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge)) =
    H.h.app (Opposite.op ⦋1⦌)
      ((SSet.Truncated.Edge.id (X := (truncation 2).obj A) x).edge,
        SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge)
  congr 1
  apply Prod.ext
  · have h := edgeUnop_id (X := A) (SSet.opObjEquiv.symm x)
    exact congrArg (fun e => e.edge) h
  · apply ULift.ext
    apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    funext i
    fin_cases i <;> rfl

/-- 元の反転 Hom 対応の頂点評価を戻すと、元の評価の反対射になる。 -/
lemma functorHomEvaluate_opposite {A D : SSet.{u}} [Quasicategory D]
    {F G : A ⟶ D} (α : FunctorHom F G) (x : A _⦋0⦌) :
    (homotopyOppositeEquivalence D).functor.map
      (functorHomEvaluate (functorOppositeHomEquiv F G α) (SSet.opObjEquiv.symm x)) =
        (functorHomEvaluate α x).op := by
  rw [← functorHomHomotopy_hom α, functorOppositeHomEquiv_homotopy,
    functorHomEvaluate_homotopy, functorHomEvaluate_homotopy]
  rw [homotopyOppositeEquivalence_map_homMk, oppositeHomotopyVertexEdge_unop]

private lemma oppositeEvaluationAppHom {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {f g : X ⟶ Y} (e : FunctorIso f g) (x : X _⦋0⦌) :
    (e.app x).hom = functorHomEvaluate e.hom x := by
  rw [FunctorIso.app_eq_evaluate]
  rfl

/-- 元の全同型を反転した同じ逆成分の像は、元の同じ順成分の反対射。 -/
lemma functorIso_op_app_inv {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {f g : X ⟶ Y} (e : FunctorIso f g) (x : X _⦋0⦌) :
    (homotopyOppositeEquivalence Y).functor.map
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorIso.app
        e.op (SSet.opObjEquiv.symm x)).inv) = (e.app x).hom.op := by
  have hi := oppositeEvaluationAppHom e.op.symm (SSet.opObjEquiv.symm x)
  rw [FunctorIso.app_symm, Iso.symm_hom, Iso.symm_hom] at hi
  rw [hi, sameFunctorIso_op_inv, functorHomEvaluate_opposite, ← oppositeEvaluationAppHom]
end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories

end
