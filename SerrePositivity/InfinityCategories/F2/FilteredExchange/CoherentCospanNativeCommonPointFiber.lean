module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentCospanNativeFiberEdgeSections
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PointedSectionTargetPointIso

/-!
概要：native 切断 cospan の共通標的を、元の同じ最後の小さい fiber へ表示する。
方針：共通点上の切断の厳密な同型と底上の終点制限の式を使う。
規約：両辺に同じ標的同型を使う。使われ方：元の fiber cospan との厳密な可換比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}
  (F X Y Z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (C : CoherentTransformationCospanCone F X Y Z) (b : B _⦋0⦌)
local notation "c" => coherentCospanConePointwiseCone F X Y Z C b
local notation "d" => joinInr Δ[0] (horn 2 2) ≫ Subtype.val c
local notation "el" => horn₂₂.ι₀₂ ≫ d
local notation "er" => horn₂₂.ι₁₂ ≫ d
local notation "t" => stdSimplex.δ (0 : Fin 2) ≫ el
/-- native 左辺の終点は、元の最後の同じ Z の値。 -/
lemma coherentCospanNativeLeftDiagramTarget_vertex :
    (el).app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 1) = Z.app _ (ULift.up b) := by
  exact (congrArg (fun k : (Δ[1] : SSet.{u + 1}) ⟶ SpaceInfinity.{u} =>
    k.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 1))
      (coherentCospanNativeLeftDiagramEdge_eq_point F X Y Z C b)).trans
        (coherentTransformationPointEdge_target X Z C.fromLeft b)

/-- native 右辺の終点も、元の最後の同じ Z の値。 -/
lemma coherentCospanNativeRightDiagramTarget_vertex :
    (er).app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 1) = Z.app _ (ULift.up b) := by
  exact (congrArg (fun k : (Δ[1] : SSet.{u + 1}) ⟶ SpaceInfinity.{u} =>
    k.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 1))
      (coherentCospanNativeRightDiagramEdge_eq_point F X Y Z C b)).trans
        (coherentTransformationPointEdge_target Y Z C.fromRight b)
local notation "hl" => coherentCospanNativeLeftDiagramTarget_vertex F X Y Z C b
local notation "hr" => coherentCospanNativeRightDiagramTarget_vertex F X Y Z C b

/-- 共通点の元の値は、元の最後の同じ Z の値である。 -/
lemma coherentCospanNativeCommonPoint_vertex :
    (t).app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0) = Z.app _ (ULift.up b) := by
  change (el).app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 1) = _
  exact hl

/-- 共通点上の切断空間を、元の同じ最後の小さい fiber へ表示する同型。 -/
def coherentCospanNativeCommonPointFiberIso :=
  pointedSectionPointFiberIso Z b t (coherentCospanNativeCommonPoint_vertex F X Y Z C b)

/-- 左の終点制限を共通標的同型で表示すると、同じ元の終点 fiber 評価になる。 -/
lemma coherentCospanNativeCommonPointFiberIso_left :
    relativeFunctorOverPre pointedSpaceProjection (relativeCospanLeftTarget d) ≫
      (coherentCospanNativeCommonPointFiberIso F X Y Z C b).hom =
      pointedSectionTargetFiber Z b el hl :=
  pointedSectionTargetFiber_eq_point_iso Z b t
    (coherentCospanNativeCommonPoint_vertex F X Y Z C b) el hl rfl

/-- 右も同じ共通標的同型を使い、同じ最後の fiber で評価する。 -/
lemma coherentCospanNativeCommonPointFiberIso_right :
    relativeFunctorOverPre pointedSpaceProjection (relativeCospanRightTarget d) ≫
      (coherentCospanNativeCommonPointFiberIso F X Y Z C b).hom =
      pointedSectionTargetFiber Z b er hr :=
  pointedSectionTargetFiber_eq_point_iso Z b t
    (coherentCospanNativeCommonPoint_vertex F X Y Z C b) er hr (relativeCospanRightTarget d).w

end SerrePositivity.InfinityCategories.F2
