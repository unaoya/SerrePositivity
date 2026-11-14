module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGVerdierOverEvaluation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.HomotopyModels.WeaklyContractibleConstantLimit
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.LimitDiagramIso
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGVerdierOverTerminal
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.InitialTerminalWeakContractibility
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]
/-- 実 Verdier 分母添字自体は弱可縮。 -/
lemma dgVerdierOver_isWeaklyContractible (P : Set D) (x : D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverIdentityVertex_isTerminal A D P x).isWeaklyContractible
/-- 任意反転関手の実分母図式は、任意 quasicategory 標的で実極限を持つ。 -/
lemma dgVerdierOver_hasLimit (P : Set D) (x : D) {Y : SSet.{max u v}} [Quasicategory Y]
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D ⟶ Y) (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverSource A D P x ≫ F) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.hasLimit_iff_of_functorIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverEvaluationIso A D P x F hF)).mpr
  exact ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.constantDiagramCone _ Y _, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.constantDiagramCone_isLimit _ Y
    (dgVerdierOver_isWeaklyContractible A D P x) _⟩
end SerrePositivity.InfinityCategories.Project.DerivedCategories
