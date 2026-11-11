module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.CoconeTransformationPost
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.CoconeTransformationPoint
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.TrivialFibrationCocone

/-!
概要：指定頂点の native 余錐の変換頂点を、標的関手で評価した同じ余錐の変換へ移す。
方針：既存の全族の後合成自然性を、同じ余錐の指定点で評価する。
規約：余錐も頂点の等式も保持する。
使われ方：前層値密度余錐の標準変換から各対象での余錐の標準変換への接続。

対応節は Kerodon 8.3（Tag 03LZ）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding

/-- 同じ後合成余錐の頂点は、元の頂点の像。 -/
lemma mapJoinCocone_vertex {K X Y : SSet.{u}} (q : X ⟶ Y) {D : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone q c).vertex = q.app (Opposite.op ⦋0⦌) c.vertex := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex_eq, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex_eq]
  change SSet.yonedaEquiv (_ ≫ (c.val ≫ q)) = q.app _ (SSet.yonedaEquiv (_ ≫ c.val))
  rw [← SSet.yonedaEquiv_comp, Category.assoc]

/-- 同じ指定頂点の余錐の点は、標的への後合成で同じ写した余錐の点へ移る。 -/
lemma coconeMappingPointAt_post {K X Y : SSet.{u}} {D : K ⟶ X}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D) (z : X _⦋0⦌) (hv : c.vertex = z) (q : X ⟶ Y)
    (hw : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone q c).vertex = q.app (Opposite.op ⦋0⦌) z) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.coslicePostcompFiberMap D q z).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeMappingPointAt c z hv) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeMappingPointAt (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone q c) (q.app (Opposite.op ⦋0⦌) z) hw := by
  apply Subtype.ext
  rfl

/-- 標準変換の頂点の後合成は、元の余錐を後合成した同じ余錐の標準変換。 -/
lemma coconeTransformationPointAt_post {K X Y : SSet.{u}} {D : K ⟶ X}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D) (z : X _⦋0⦌) (hv : c.vertex = z) (q : X ⟶ Y)
    (hw : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone q c).vertex = q.app (Opposite.op ⦋0⦌) z) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.constantTransformationPost D z q).app (Opposite.op ⦋0⦌)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeTransformationMap D z).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeMappingPointAt c z hv)) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeTransformationMap (D ≫ q) (q.app (Opposite.op ⦋0⦌) z)).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeMappingPointAt (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone q c) (q.app (Opposite.op ⦋0⦌) z) hw) := by
  have h := congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeMappingPointAt c z hv))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeTransformationMap_postcomp D z q)
  change _ = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.constantTransformationPost D z q).app _
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeTransformationMap D z).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeMappingPointAt c z hv)) at h
  exact h.symm.trans (congrArg
    (fun v ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeTransformationMap (D ≫ q) (q.app (Opposite.op ⦋0⦌) z)).app
      (Opposite.op ⦋0⦌) v) (coconeMappingPointAt_post c z hv q hw))

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
