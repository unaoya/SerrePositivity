module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentCospanConePointwise
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.NativeConeTriangle
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.NativeConeLeg

/-!
概要：各点の native 錐の二三角形と頂点を元の coherent な指定データへ戻す。
方針：貼り合わせの制限式と native な三角形の面の式を使う。
規約：元の全二単体を保持。使われ方：各点の普遍性による比較の同値判定。
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
local notation "el" => SSet.yonedaEquiv horn₂₂.ι₀₂
local notation "er" => SSet.yonedaEquiv horn₂₂.ι₁₂

/-- 概要：native 錐の左三角形は元の左三角形の指定一点評価。
方針：同じ三角形包含の貼り合わせ制限。
規約：二単体の厳密な等式。使われ方：元の指定可換性の保持。 -/
lemma coherentCospanConePointwiseCone_leftTriangle :
    nativeConeTriangle c el = coherentTransformationPointTriangle C.leftTriangle (ULift.up b) := by
  unfold nativeConeTriangle
  rw [Equiv.symm_apply_apply]
  exact congrArg (fun k : (Δ[2] : SSet.{u + 1}) ⟶ SpaceInfinity.{u} => SSet.yonedaEquiv k)
    (coherentCospanConePointwiseDiagram_left F X Y Z C b)

/-- 概要：native 錐の右三角形は元の右三角形の指定一点評価。
方針：同じ三角形包含の貼り合わせ制限。
規約：二単体の厳密な等式。使われ方：元の指定可換性の保持。 -/
lemma coherentCospanConePointwiseCone_rightTriangle :
    nativeConeTriangle c er = coherentTransformationPointTriangle C.rightTriangle (ULift.up b) := by
  unfold nativeConeTriangle
  rw [Equiv.symm_apply_apply]
  exact congrArg (fun k : (Δ[2] : SSet.{u + 1}) ⟶ SpaceInfinity.{u} => SSet.yonedaEquiv k)
    (coherentCospanConePointwiseDiagram_right F X Y Z C b)

/-- 概要：元の各点の native 錐の頂点は元の図式のその点の値そのもの。
方針：元の左三角形の第一辺の始点を使う。
規約：頂点の厳密な等式。使われ方：各点の元の引き戻し対象の指定。 -/
lemma coherentCospanConePointwiseCone_vertex :
    (c).vertex = F.app (Opposite.op ⦋0⦌) (ULift.up b) := by
  have h : (nativeConeLeg c ((horn 2 2 : SSet.{u + 1}).δ 1 el)).edge =
      (functorEdgeAt (intervalMappingEdgeOfVertex C.toLeft) (ULift.up b)).edge := by
    exact (nativeConeTriangle_face c el (1 : Fin 2)).symm.trans
      ((congrArg (SpaceInfinity.δ 2)
        (coherentCospanConePointwiseCone_leftTriangle F X Y Z C b)).trans
          (coherentTransformationPointTriangle_first C.leftTriangle (ULift.up b)))
  exact (nativeConeLeg c ((horn 2 2 : SSet.{u + 1}).δ 1 el)).src_eq.symm.trans
    ((congrArg (SpaceInfinity.δ 1) h).trans
      (functorEdgeAt (intervalMappingEdgeOfVertex C.toLeft) (ULift.up b)).src_eq)

end SerrePositivity.InfinityCategories.F2
