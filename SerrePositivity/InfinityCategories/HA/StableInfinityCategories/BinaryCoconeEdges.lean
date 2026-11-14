module
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.FiniteShapes
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoreCoconeLeg
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.JoinCoproductPushout

/-! # 二本の辺からの離散二点図式の余錐

概要：同じ終点へ向かう二本の辺は離散二点図式の余錐を与える。
方針：二つの点の join を共通終点で貼り、脚と余錐頂点を計算する。
規約：固定図式は任意の二点図式。使われ方：二項余積の Hom の存在。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：離散二点図式の第一点の包含。
方針：標準零単体の直和の第一包含を使う。
規約：宇宙を固定する。使われ方：余錐の第一脚。 -/
abbrev binaryPointLeft : (Δ[0] : SSet.{u}) ⟶ (Δ[0] : SSet.{u}) ⨿ Δ[0] := coprod.inl

/-- 概要：離散二点図式の第二点の包含。
方針：標準零単体の直和の第二包含を使う。
規約：宇宙を固定する。使われ方：余錐の第二脚。 -/
abbrev binaryPointRight : (Δ[0] : SSet.{u}) ⟶ (Δ[0] : SSet.{u}) ⨿ Δ[0] := coprod.inr

/-- 概要：共通終点の二本の辺から固定された二点図式の余錐を作る。
方針：join の直和の pushout に二つの辺を降ろす。
規約：始点は固定図式の二つの値。使われ方：余積からの射の入力。 -/
def binaryCoconeOfEdges {X : SSet.{u}} (p : (Δ[0] : SSet.{u}) ⨿ Δ[0] ⟶ X)
    {z : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X)
      (SSet.yonedaEquiv (binaryPointLeft ≫ p)) z)
    (g : SSet.Truncated.Edge (X := (truncation 2).obj X)
      (SSet.yonedaEquiv (binaryPointRight ≫ p)) z) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p := by
  let F := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom ≫ SSet.yonedaEquiv.symm f.edge
  let G := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom ≫ SSet.yonedaEquiv.symm g.edge
  have hF : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u}) Δ[0] ≫ F = SSet.yonedaEquiv.symm z := by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.joinStdSimplexIso_zero_inr]
    exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSimplex_target f
  have hG : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u}) Δ[0] ≫ G = SSet.yonedaEquiv.symm z := by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.joinStdSimplexIso_zero_inr]
    exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSimplex_target g
  let P := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.join_coproduct_isPushout (Δ[0] : SSet.{u}) Δ[0] Δ[0]
  let V := P.desc F G (hF.trans hG.symm)
  refine ⟨V, ?_⟩
  apply coprod.hom_ext
  · rw [← Category.assoc binaryPointLeft,
      ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap binaryPointLeft (𝟙 (Δ[0] : SSet.{u})), Category.assoc]
    rw [P.inl_desc]
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.joinStdSimplexIso_zero_inl, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSimplex_source f]
    exact (SSet.yonedaEquiv (X := X) (n := ⦋0⦌)).symm_apply_apply (binaryPointLeft ≫ p)
  · rw [← Category.assoc binaryPointRight,
      ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap binaryPointRight (𝟙 (Δ[0] : SSet.{u})), Category.assoc]
    rw [P.inr_desc]
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.joinStdSimplexIso_zero_inl, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSimplex_source g]
    exact (SSet.yonedaEquiv (X := X) (n := ⦋0⦌)).symm_apply_apply (binaryPointRight ≫ p)

/-- 概要：二本の辺から作った余錐の第一枝の制限は第一辺の join 表示。
方針：pushout の第一包含の式。規約：射の厳密な等号。
使われ方：第一脚と余錐頂点の計算。 -/
lemma binaryCoconeOfEdges_left {X : SSet.{u}} (p : (Δ[0] : SSet.{u}) ⨿ Δ[0] ⟶ X)
    {z : X _⦋0⦌} (f) (g) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap binaryPointLeft (𝟙 (Δ[0] : SSet.{u})) ≫ (binaryCoconeOfEdges p (z := z) f g).val =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom ≫ SSet.yonedaEquiv.symm f.edge := by
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.join_coproduct_isPushout (Δ[0] : SSet.{u}) Δ[0] Δ[0]).inl_desc _ _ _

/-- 概要：二本の辺から作った余錐の第二枝の制限は第二辺の join 表示。
方針：pushout の第二包含の式。規約：射の厳密な等号。
使われ方：第二脚の計算。 -/
lemma binaryCoconeOfEdges_right {X : SSet.{u}} (p : (Δ[0] : SSet.{u}) ⨿ Δ[0] ⟶ X)
    {z : X _⦋0⦌} (f) (g) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap binaryPointRight (𝟙 (Δ[0] : SSet.{u})) ≫ (binaryCoconeOfEdges p (z := z) f g).val =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom ≫ SSet.yonedaEquiv.symm g.edge := by
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.join_coproduct_isPushout (Δ[0] : SSet.{u}) Δ[0] Δ[0]).inr_desc _ _ _

/-- 概要：二本の辺から作った余錐の頂点は指定した共通終点。
方針：第一枝の終点を計算する。
規約：実際の頂点の等号。使われ方：余積からの射の終域の指定。 -/
lemma binaryCoconeOfEdges_vertex {X : SSet.{u}} (p : (Δ[0] : SSet.{u}) ⨿ Δ[0] ⟶ X)
    {z : X _⦋0⦌} (f) (g) : (binaryCoconeOfEdges p (z := z) f g).vertex = z := by
  have h := congrArg (fun a => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u}) Δ[0] ≫ a)
    (binaryCoconeOfEdges_left p f g)
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap, Category.id_comp,
    ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.joinStdSimplexIso_zero_inr, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSimplex_target f] at h
  exact (congrArg SSet.yonedaEquiv h).trans (SSet.yonedaEquiv.apply_symm_apply z)

/-- 概要：作った余錐の第一脚の一次単体は指定した第一辺の一次単体。
方針：join 表示を標準区間へ戻す。
規約：終点の表示の等号を除いて同じ辺。使われ方：ホモトピー類の比較。 -/
lemma binaryCoconeOfEdges_leg_left {X : SSet.{u}} (p : (Δ[0] : SSet.{u}) ⨿ Δ[0] ⟶ X)
    {z : X _⦋0⦌} (f) (g) :
    ((binaryCoconeOfEdges p (z := z) f g).leg binaryPointLeft).edge = f.edge := by
  change SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫ _) = _
  rw [binaryCoconeOfEdges_left, Iso.inv_hom_id_assoc]
  exact SSet.yonedaEquiv.apply_symm_apply f.edge

/-- 概要：作った余錐の第二脚の一次単体は指定した第二辺の一次単体。
方針：join 表示を標準区間へ戻す。
規約：終点の表示の等号を除いて同じ辺。使われ方：ホモトピー類の比較。 -/
lemma binaryCoconeOfEdges_leg_right {X : SSet.{u}} (p : (Δ[0] : SSet.{u}) ⨿ Δ[0] ⟶ X)
    {z : X _⦋0⦌} (f) (g) :
    ((binaryCoconeOfEdges p (z := z) f g).leg binaryPointRight).edge = g.edge := by
  change SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫ _) = _
  rw [binaryCoconeOfEdges_right, Iso.inv_hom_id_assoc]
  exact SSet.yonedaEquiv.apply_symm_apply g.edge

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
