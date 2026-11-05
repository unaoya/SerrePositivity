module
public import SerrePositivity.InfinityCategories.Derived.Gluing.OrdinaryPullbackStableClosure
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (hC : IsDGPretriangulated R C) (hD : IsDGPretriangulated R D)
include hC hD
lemma dgGluingPullbackProperty_of_retract (X Y : DGGluingObject R C D M)
    (r : Retract
      (SSet.HomotopyCategory.mk (X :=
        (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
          (dgNerve R (DGGluingObject R C D M))) (ULift.up (Simplex.vertex X)))
      (SSet.HomotopyCategory.mk (ULift.up (Simplex.vertex Y))))
    (hY : dgGluingPullbackProperty R C D M Y) :
    dgGluingPullbackProperty R C D M X := by
  let F := dgGluingPullbackDifference R C D M hC hD
  have hz := (dgGluingPullbackProperty_iff_difference_zero R C D M hC hD Y).mp hY
  let s := r.map (hoFunctor.map F).toFunctor
  have e : VertexIso (F.app (Opposite.op ⦋0⦌) (ULift.up (Simplex.vertex Y)))
      (F.app (Opposite.op ⦋0⦌) (ULift.up (Simplex.vertex X))) :=
    { hom := s.r
      inv := s.i
      hom_inv_id := hz.isZeroHo.eq_of_src _ _
      inv_hom_id := s.retract }
  exact (dgGluingPullbackProperty_iff_difference_zero R C D M hC hD X).mpr
    (hz.of_vertexIso e)
end SerrePositivity.InfinityCategories
