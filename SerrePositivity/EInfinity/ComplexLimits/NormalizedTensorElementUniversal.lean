module
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorElementDiagram
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorUniversalSimplex
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SimplexTerminalParameter

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
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A] (X Y : Complex A)

abbrev normalizedTensorElementTerminalParameter {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n) :
    ⦋n⦌ ⟶ (normalizedTensorElementDegree A X Y).obj (c.obj (Fin.last n)) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SimplexTerminalParameter.parameter (c ⋙ normalizedTensorElementDegree A X Y)

def normalizedTensorElementUniversalFamily {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n) :
    SSet.uliftFunctor.{u + 1, u}.obj (Δ[n] : SSet.{u}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A (Complex A) X
        ((normalizedTensorElementDiagram A X Y).obj (c.obj (Fin.last n))) :=
  SSet.uliftFunctor.{u + 1, u}.map
    (SSet.stdSimplex.map (normalizedTensorElementTerminalParameter A X Y c)) ≫
      normalizedTensorUniversalSimplex A X
        ((normalizedTensorElementDegree A X Y).obj (c.obj (Fin.last n)))

def normalizedTensorElementUniversalSimplex {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A (Complex A) X
      ((normalizedTensorElementDiagram A X Y).obj (c.obj (Fin.last n)))) _⦋n⦌ :=
  (normalizedTensorElementUniversalFamily A X Y c).app (Opposite.op ⦋n⦌)
    (ULift.up (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋n⦌)))

end SerrePositivity.EInfinity.ComplexLimits
