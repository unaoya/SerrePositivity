module

public import SerrePositivity.KST.Spectra.SpectrumCircleDiagonalHomotopies
public import SerrePositivity.InfinityCategories.Project.PointedSpaces.BasedIntervalSimplex

/-!
概要：元の companion 経路と普遍評価の生成 loop は、同じ基本群の元を表す。
方針：同じ元の対角への両端固定ホモトピーを、境界固定一単体のホモトピーへ移す。
規約：元の辺・経路の写像をそのまま保持。使われ方：元の円評価錐の切断の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
namespace SerrePositivity.KST.Spectra.OmegaSpectrum

/-- 元の生成 loop の区間写像の両端は、元の零 Hom 頂点。 -/
lemma circleEvaluationLoop_vertex (z : Sp.{u} _⦋0⦌) (i : Fin 2) :
    (SSet.yonedaEquiv.symm
      (circleEvaluationHomEdge (nativeCotensorInput PointedSimplicialSet.circle z).val).edge).app
        (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm i) =
      (circleEvaluationPointedHom z).basepoint := by
  have h := congrArg (fun f : (Δ[1] : SSet.{u}) ⟶ (circleEvaluationPointedHom z).right ↦
    f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm i))
      (circleEvaluationHomSquare_skipSecond z)
  change (circleEvaluationHomSquare z).app _ (stdSimplex.obj₀Equiv.symm i,
    (SSet.const (X := (Δ[1] : SSet.{u})) (stdSimplex.obj₀Equiv.symm 0)).app _
      (stdSimplex.obj₀Equiv.symm i)) = _ at h
  rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.const_vertex] at h
  exact h.symm.trans (circleEvaluationHomSquare_corner z i 0)

/-- 元の companion の区間写像の両端も、同じ零 Hom 頂点。 -/
lemma circleEvaluationCompanion_vertex (z : Sp.{u} _⦋0⦌) (i : Fin 2) :
    (circleEvaluationCompanionHomPath z).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm i) = (circleEvaluationPointedHom z).basepoint := by
  have h := congrArg (fun f : (Δ[1] : SSet.{u}) ⟶ (circleEvaluationPointedHom z).right ↦
    f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm i))
      (circleEvaluationHomSquare_skipFirst z)
  change (circleEvaluationHomSquare z).app _
    ((SSet.const (X := (Δ[1] : SSet.{u})) (stdSimplex.obj₀Equiv.symm 0)).app _
      (stdSimplex.obj₀Equiv.symm i), stdSimplex.obj₀Equiv.symm i) = _ at h
  rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.const_vertex] at h
  exact h.symm.trans (circleEvaluationHomSquare_corner z 0 i)

/-- 同じ対角経路の両端も、同じ零 Hom 頂点。 -/
lemma circleEvaluationDiagonal_vertex (z : Sp.{u} _⦋0⦌) (i : Fin 2) :
    (circleEvaluationHomDiagonal z).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm i) = (circleEvaluationPointedHom z).basepoint :=
  circleEvaluationHomSquare_corner z i i

/-- 元の生成 loop を、そのまま境界定数一単体として読む。 -/
def circleEvaluationLoopSimplex (z : Sp.{u} _⦋0⦌) :
    (circleEvaluationPointedHom z).right.PtSimplex 1 (circleEvaluationPointedHom z).basepoint :=
  _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.simplex
    (SSet.yonedaEquiv.symm
      (circleEvaluationHomEdge (nativeCotensorInput PointedSimplicialSet.circle z).val).edge)
    (circleEvaluationLoop_vertex z)

/-- 元の companion 経路を、そのまま境界定数一単体として読む。 -/
def circleEvaluationCompanionSimplex (z : Sp.{u} _⦋0⦌) :
    (circleEvaluationPointedHom z).right.PtSimplex 1 (circleEvaluationPointedHom z).basepoint :=
  _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.simplex (circleEvaluationCompanionHomPath z) (circleEvaluationCompanion_vertex z)

/-- 元の対角経路を、そのまま境界定数一単体として読む。 -/
def circleEvaluationDiagonalSimplex (z : Sp.{u} _⦋0⦌) :
    (circleEvaluationPointedHom z).right.PtSimplex 1 (circleEvaluationPointedHom z).basepoint :=
  _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.simplex (circleEvaluationHomDiagonal z) (circleEvaluationDiagonal_vertex z)

/-- 元の生成 loop から元の対角への境界固定ホモトピー。 -/
def circleEvaluationLoopDiagonalRelativeHomotopy (z : Sp.{u} _⦋0⦌) :
    (circleEvaluationLoopSimplex z).Homotopy (circleEvaluationDiagonalSimplex z) :=
  _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.relativeHomotopy (circleEvaluationLoop_vertex z)
    (circleEvaluationDiagonal_vertex z) (circleEvaluationLoopDiagonalHomotopy z)
    (circleEvaluationLoopDiagonalHomotopy_source z) (circleEvaluationLoopDiagonalHomotopy_target z)

/-- 元の companion から同じ元の対角への境界固定ホモトピー。 -/
def circleEvaluationCompanionDiagonalRelativeHomotopy (z : Sp.{u} _⦋0⦌) :
    (circleEvaluationCompanionSimplex z).Homotopy (circleEvaluationDiagonalSimplex z) :=
  _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.relativeHomotopy (circleEvaluationCompanion_vertex z)
    (circleEvaluationDiagonal_vertex z) (circleEvaluationCompanionDiagonalHomotopy z)
    (circleEvaluationCompanionDiagonalHomotopy_source z)
    (circleEvaluationCompanionDiagonalHomotopy_target z)

local instance circleComparisonPointedHomKan (z : Sp.{u} _⦋0⦌) :
    KanComplex (circleEvaluationPointedHom z).right := by
  change KanComplex (mappingSpace
    (cotensor PointedSimplicialSet.circle (nativeCotensorInput PointedSimplicialSet.circle z).val)
      (nativeCotensorInput PointedSimplicialSet.circle z).val)
  infer_instance

/-- 元の companion の経路は、元の普遍評価の生成 loop と同じ基本群の元を表す。 -/
lemma circleEvaluationCompanion_loop_class (z : Sp.{u} _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (circleEvaluationCompanionSimplex z) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (circleEvaluationLoopSimplex z) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.eq_of_relativeHomotopy
    (circleEvaluationCompanionDiagonalRelativeHomotopy z)).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.eq_of_relativeHomotopy
        (circleEvaluationLoopDiagonalRelativeHomotopy z)).symm

end SerrePositivity.KST.Spectra.OmegaSpectrum
