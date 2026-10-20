module
public import SerrePositivity.InfinityCategories.Derived.DGVerdierOverLimit
public import SerrePositivity.InfinityCategories.Derived.EvaluationLimitCone
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [IsDGPretriangulated A D]
/-- 元の全評価を保持する、実分母図式の実極限錐と全錐の比較 prism。 -/
def dgVerdierOverLimitConeTransport (P : Set D) (x : D)
    {Y : SSet.{max u v}} [Quasicategory Y] (F : dgNerve A D ⟶ Y)
    (hF : InvertsEdges F (dgVerdierEdges A D P)) :=
  evaluationLimitConeTransport (dgVerdierOver_isWeaklyContractible A D P x)
    (F.app (Opposite.op ⦋0⦌) (Simplex.vertex x)) (dgVerdierOverEvaluationHomotopy A D P x F)
    (dgVerdierOverEvaluationHomotopy_invertible A D P x F hF)
/-- 実分母図式の実極限錐の頂点は、元の対象の像そのもの。 -/
lemma dgVerdierOverLimitConeTransport_vertex (P : Set D) (x : D)
    {Y : SSet.{max u v}} [Quasicategory Y] (F : dgNerve A D ⟶ Y)
    (hF : InvertsEdges F (dgVerdierEdges A D P)) :
    (dgVerdierOverLimitConeTransport A D P x F hF).cone.vertex =
      F.app (Opposite.op ⦋0⦌) (Simplex.vertex x) :=
  evaluationLimitConeTransport_vertex _ _ _ _
end SerrePositivity.InfinityCategories
