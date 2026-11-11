module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierFiniteVertexCones

/-! # 有限実分母図式の頂点上の共通始錐

概要：頂点が有限な実分母図式へ、一つの閉分母から全頂点への実 over 辺を供給する。
方針：全頂点を有限番号へ移し、実有限共通始点の脚を元の図式頂点へ厳密に戻す。
規約：図式辺との二単体・高次整合性はまだ構造に含めない。
使われ方：指定図式の各辺の整合性ホーンの入力。
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

/-- 図式の全頂点へ向かう共通の実分母と実 over 辺。辺上の整合性は別途構成する。 -/
structure DGVerdierDiagramVertexCone (P : Set D) (x : D) {K : SSet.{max u v}}
    (f : K ⟶ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet.{max u v})) where
  denominator : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x
  leg (v : K _⦋0⦌) : Truncated.Edge (X := (truncation 2).obj
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet.{max u v}))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedVerdierDenominatorVertex A D P x denominator) (f.app (Opposite.op ⦋0⦌) v)
  leg_mem (v : K _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverSource A D P x).app (Opposite.op ⦋1⦌) (leg v).edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P

variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]

/-- 頂点が有限な任意の実分母図式は、一つの閉分母から全頂点への実脚を持つ。 -/
theorem dgVerdierDiagramVertexCone_nonempty (P : Set D) (x : D)
    {K : SSet.{max u v}} [Finite (K _⦋0⦌)]
    (f : K ⟶ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet.{max u v})) :
    Nonempty (DGVerdierDiagramVertexCone A D P x f) := by
  classical
  let : Fintype (K _⦋0⦌) := Fintype.ofFinite _
  let ε := Fintype.equivFin (K _⦋0⦌)
  obtain ⟨s, r, hr⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverFinite_exists_commonSource A D P x
    (fun i => f.app (Opposite.op ⦋0⦌) (ε.symm i))
  refine ⟨{
    denominator := s
    leg := fun v => {
      edge := (r (ε v)).edge
      src_eq := (r (ε v)).src_eq
      tgt_eq := (r (ε v)).tgt_eq.trans
        (congrArg (f.app (Opposite.op ⦋0⦌)) (ε.symm_apply_apply v)) }
    leg_mem := fun v => hr (ε v) }⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
