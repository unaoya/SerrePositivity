module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.OrdinaryPullbackStableClosure
public import Mathlib.CategoryTheory.Retract
/-!
概要：通常 pullback の対象条件は共通宇宙の実ホモトピー圏の retract で閉じる。
方針：差の関手で retract を写し、零対象の retract と零対象の実同型を構成する。
規約：同じ元 gluing と augmentation を保持する。
使われ方：D-16 の thick 閉包を通常 pullback の対象条件へ戻す際に用いる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  (D : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] (M : _root_.SerrePositivity.DifferentialGraded.Bimodule R C D)
  (hC : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R C) (hD : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R D)
include hC hD
lemma dgGluingPullbackProperty_of_retract (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
    (r : Retract
      (SSet.HomotopyCategory.mk (X :=
        (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M))) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X)))
      (SSet.HomotopyCategory.mk (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Y))))
    (hY : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPullbackProperty R C D M Y) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPullbackProperty R C D M X := by
  let F := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPullbackDifference R C D M hC hD
  have hz := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPullbackProperty_iff_difference_zero R C D M hC hD Y).mp hY
  let s := r.map (hoFunctor.map F).toFunctor
  have e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (F.app (Opposite.op ⦋0⦌) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Y)))
      (F.app (Opposite.op ⦋0⦌) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X))) :=
    { hom := s.r
      inv := s.i
      hom_inv_id := hz.isZeroHo.eq_of_src _ _
      inv_hom_id := s.retract }
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPullbackProperty_iff_difference_zero R C D M hC hD X).mpr
    (hz.of_vertexIso e)
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
