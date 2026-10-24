module
public import SerrePositivity.InfinityCategories.Derived.DGVerdierOverEvaluation
public import SerrePositivity.InfinityCategories.Derived.WeaklyContractibleConstantLimit
public import SerrePositivity.InfinityCategories.Core.LimitDiagramIso
public import SerrePositivity.InfinityCategories.Derived.DGVerdierOverTerminal
public import SerrePositivity.InfinityCategories.F1B.InitialTerminalWeakContractibility
/-!
概要：任意の実分母反転関手の実 Verdier 分母図式が極限を持つことを証明する。
方針：実恒等分母の終対象性と全添字の評価同型を使う。
規約：実分母の通常の閉辺の添字へ置き換えない。使われ方：商の右 Kan 局所極限。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [IsDGPretriangulated A D]
/-- 実 Verdier 分母添字自体は弱可縮。 -/
lemma dgVerdierOver_isWeaklyContractible (P : Set D) (x : D) :
    IsWeaklyContractible (dgVerdierOver A D P x : SSet) :=
  (dgVerdierOverIdentityVertex_isTerminal A D P x).isWeaklyContractible
/-- 任意反転関手の実分母図式は、任意 quasicategory 標的で実極限を持つ。 -/
lemma dgVerdierOver_hasLimit (P : Set D) (x : D) {Y : SSet.{max u v}} [Quasicategory Y]
    (F : dgNerve A D ⟶ Y) (hF : InvertsEdges F (dgVerdierEdges A D P)) :
    HasLimit (dgVerdierOverSource A D P x ≫ F) := by
  apply (hasLimit_iff_of_functorIso (dgVerdierOverEvaluationIso A D P x F hF)).mpr
  exact ⟨constantDiagramCone _ Y _, constantDiagramCone_isLimit _ Y
    (dgVerdierOver_isWeaklyContractible A D P x) _⟩
end SerrePositivity.InfinityCategories
