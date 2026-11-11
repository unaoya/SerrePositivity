module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeVertexTriangles

/-!
概要：余錐の脚と図式の辺の合成三角形を、指定した実際の始点へ正規化する。
方針：端点の等号を辺の構造へ入れ、元の三角形の式を等号消去で移す。
規約：辺そのものの一致を要求する。使われ方：部分余極限対象の span の脚の接続。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
noncomputable section
variable {K X : SSet.{u}} {p : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p)

/-- 図式での像と等しい指定始点を持つ、余錐の実際の脚。 -/
def coconeVertexLegAt (a : K _⦋0⦌) (z : X _⦋0⦌)
    (h : p.app (Opposite.op ⦋0⦌) a = z) : X.Edge z c.vertex :=
  ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeVertexLeg c a).edge, (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeVertexLeg c a).src_eq.trans h,
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeVertexLeg c a).tgt_eq⟩

/-- 指定した実際の辺と正規化した二脚も、ホモトピー圏で可換な三角形を成す。 -/
lemma coconeVertexLegAt_comp {a b : K _⦋0⦌} (e : K.Edge a b)
    {z₀ z₁ : X _⦋0⦌} (h₀ : p.app (Opposite.op ⦋0⦌) a = z₀)
    (h₁ : p.app (Opposite.op ⦋0⦌) b = z₁) (k : X.Edge z₀ z₁)
    (hk : k.edge = (e.map p).edge) :
    SSet.Truncated.HomotopyCategory.homMk k.toTruncated ≫
        SSet.Truncated.HomotopyCategory.homMk (coconeVertexLegAt c b z₁ h₁).toTruncated =
      SSet.Truncated.HomotopyCategory.homMk (coconeVertexLegAt c a z₀ h₀).toTruncated := by
  cases h₀
  cases h₁
  have he : k = e.map p := by
    apply SSet.Edge.ext
    exact hk
  subst k
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeVertexLeg_comp c e

end
end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
