module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoreLimit
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalUniqueness

/-!
概要：join 錐の各脚を標準辺と実際の辺で表示する。
方針：点同士の join を正規化し、右因子の頂点で制限する。
規約：錐の頂点と元の図式の値を端点として厳密に保持する。
使われ方：Cat_∞ の極限錐の二射影の読み戻し。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

/-- 概要：錐の頂点から形状の指定頂点への標準辺の包含。
方針：二点の join を正規化し、右因子を指定頂点へ写す。
規約：標準区間の先頭が錐の頂点。
使われ方：錐全体のホモトピーを各脚へ制限する。 -/
def coneLegInclusion {K : SSet.{u}} (k : K _⦋0⦌) :
    (Δ[1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) K :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) (SSet.yonedaEquiv.symm k)
/-- 概要：標準の錐の脚の先頭は join の左包含。
方針：二点 join の最初の面を計算する。
規約：射の厳密な等式。
使われ方：各脚の始域を錐の頂点と同定する。 -/
lemma coneLegInclusion_source {K : SSet.{u}} (k : K _⦋0⦌) :
    stdSimplex.δ (1 : Fin 2) ≫ coneLegInclusion k = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[0] K := by
  rw [coneLegInclusion, ← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.joinStdSimplexIso_zero_inl]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, Category.id_comp]
/-- 概要：標準の錐の脚の終端は指定頂点の右包含。
方針：二点 join の最後の面を計算する。
規約：元の指定頂点を保持する。
使われ方：各脚の終域を図式の値と同定する。 -/
lemma coneLegInclusion_target {K : SSet.{u}} (k : K _⦋0⦌) :
    stdSimplex.δ (0 : Fin 2) ≫ coneLegInclusion k =
      SSet.yonedaEquiv.symm k ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] K := by
  rw [coneLegInclusion, ← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.joinStdSimplexIso_zero_inr]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap]
/-- 概要：錐の形状内の標準の脚を両端を明示した辺にする。
方針：標準区間からの包含を Yoneda で一次単体へ送る。
規約：錐の頂点と右の指定頂点を端点とする。
使われ方：全錐の比較の自然性を適用する辺。 -/
def coneDomainLeg {K : SSet.{u}} (k : K _⦋0⦌) :
    SSet.Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) K))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[0] K).app (Opposite.op ⦋0⦌) (SSet.yonedaEquiv (𝟙 Δ[0])))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] K).app (Opposite.op ⦋0⦌) k) where
  edge := SSet.yonedaEquiv (coneLegInclusion k)
  src_eq := by
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) K).δ 1 (SSet.yonedaEquiv (coneLegInclusion k)) = _
    rw [← stdSimplex.yonedaEquiv_δ_comp, coneLegInclusion_source]
    rfl
  tgt_eq := by
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) K).δ 0 (SSet.yonedaEquiv (coneLegInclusion k)) = _
    rw [← stdSimplex.yonedaEquiv_δ_comp, coneLegInclusion_target,
      SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
/-- 概要：任意の join 錐の指定頂点への実際の脚。
方針：形状内の標準辺を錐の射で写す。
規約：始域は錐の頂点、終域は元の図式の値。
使われ方：Cat_∞ 内の錐の脚を小さい圏の関手へ戻す。 -/
def nativeConeLeg {K X : SSet.{u}} {p : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (k : K _⦋0⦌) :
    SSet.Truncated.Edge (X := (truncation 2).obj X) c.vertex
      (p.app (Opposite.op ⦋0⦌) k) where
  edge := c.val.app (Opposite.op ⦋1⦌) (coneDomainLeg k).edge
  src_eq := by
    have h := (coneDomainLeg k).map ((truncation 2).map c.val) |>.src_eq
    exact h
  tgt_eq := by
    have h := (coneDomainLeg k).map ((truncation 2).map c.val) |>.tgt_eq
    refine h.trans ?_
    exact ConcreteCategory.congr_hom (NatTrans.congr_app c.property (Opposite.op ⦋0⦌)) k

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
