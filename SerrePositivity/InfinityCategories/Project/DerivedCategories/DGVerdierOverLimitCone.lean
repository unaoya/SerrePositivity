module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierOverLimit
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.EvaluationLimitCone
/-!
概要：反転関手の実 Verdier 分母図式の極限錐を、元の対象の像を厳密な頂点として構成する。
方針：元の全添字評価の同じ成分辺と全 prism を使って定値極限錐を輸送する。
規約：存在だけでなく指定頂点と境界比較を保持。使われ方：右 Kan の単位成分の照合。
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
/-- 元の全評価を保持する、実分母図式の実極限錐と全錐の比較 prism。 -/
def dgVerdierOverLimitConeTransport (P : Set D) (x : D)
    {Y : SSet.{max u v}} [Quasicategory Y] (F : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D ⟶ Y)
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.evaluationLimitConeTransport (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver_isWeaklyContractible A D P x)
    (F.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverEvaluationHomotopy A D P x F)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverEvaluationHomotopy_invertible A D P x F hF)
/-- 実分母図式の実極限錐の頂点は、元の対象の像そのもの。 -/
lemma dgVerdierOverLimitConeTransport_vertex (P : Set D) (x : D)
    {Y : SSet.{max u v}} [Quasicategory Y] (F : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D ⟶ Y)
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P)) :
    (dgVerdierOverLimitConeTransport A D P x F hF).cone.vertex =
      F.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.evaluationLimitConeTransport_vertex _ _ _ _
end SerrePositivity.InfinityCategories.Project.DerivedCategories
