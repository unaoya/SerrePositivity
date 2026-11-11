module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.RelativeRoofCofinality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.RoofComparisonTransport
/-!
概要：右 Kan 比較で使う屋根比較の cofinality を、元の同じ始域の raw 屋根比較へ戻す。
方針：引き戻しの二つの可換式だけで点・添字の輸送を同定する。
規約：三角形の始対象性等をこの比較の仮定に含めない。使われ方：dg 実屋根比較への接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits SSet
open scoped _root_.Simplicial
/-- 右 Kan 用の屋根比較の cofinality は、元の同じ始域・終点の raw 屋根比較と同値。 -/
lemma relativeRoofComparison_isLeftCofinal_iff_raw {I E X Q : SSet.{u}}
    (r : E ⟶ Q) (q : X ⟶ Q) (u : I ⟶ pullback r q)
    (b : (Δ[0] : SSet.{u}) ⟶ pullback r q) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.relativeRoofComparison r q u b) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.rawRoofFunctorMap q (u ≫ pullback.snd r q) (b ≫ pullback.snd r q)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofComparisonTransport_isLeftCofinal_iff q (u ≫ pullback.snd r q)
    (b ≫ pullback.snd r q) ((b ≫ pullback.fst r q) ≫ r) ((u ≫ pullback.fst r q) ≫ r)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.slicePullbackPoint_comm r q b).symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.slicePullbackPoint_comm r q u).symm
end SerrePositivity.InfinityCategories.Project.DerivedCategories
