module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorElementDiagram
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorUniversalSimplex
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SliceTransport.SimplexTerminalParameter

/-!
概要：全単体列の終端における、元の普遍正規化 Hom 族を構成する。
方針：同じ frame 次数列の終端頂点パラメータで元の普遍族を引き戻す。
規約：元の全単体列と元の終端対象を保持する。
使われ方：全図式の実 augmentation の逆を与える大域 prism の高次成分。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.SSet
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (X Y : Complex A)

abbrev normalizedTensorElementTerminalParameter {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n) :
    ⦋n⦌ ⟶ (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDegree A X Y).obj (c.obj (Fin.last n)) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SimplexTerminalParameter.parameter (c ⋙ _root_.SerrePositivity.ComplexLimits.normalizedTensorElementDegree A X Y)

def normalizedTensorElementUniversalFamily {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n) :
    SSet.uliftFunctor.{u + 1, u}.obj (Δ[n] : SSet.{u}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A (Complex A) X
        ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDiagram A X Y).obj (c.obj (Fin.last n))) :=
  SSet.uliftFunctor.{u + 1, u}.map
    (SSet.stdSimplex.map (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementTerminalParameter A X Y c)) ≫
      _root_.SerrePositivity.ComplexLimits.normalizedTensorUniversalSimplex A X
        ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDegree A X Y).obj (c.obj (Fin.last n)))

def normalizedTensorElementUniversalSimplex {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A (Complex A) X
      ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDiagram A X Y).obj (c.obj (Fin.last n)))) _⦋n⦌ :=
  (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementUniversalFamily A X Y c).app (Opposite.op ⦋n⦌)
    (ULift.up (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋n⦌)))

end SerrePositivity.ComplexLimits
