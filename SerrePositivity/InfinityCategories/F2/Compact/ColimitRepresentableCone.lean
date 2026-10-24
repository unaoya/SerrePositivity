module

public import SerrePositivity.InfinityCategories.F2.Compact.RepresentableDiagramLimits
public import SerrePositivity.InfinityCategories.F1B.NerveComparison.CoconeVertex

/-!
概要：元の余極限余錐から、同じ頂点からの全共変 Hom を頂点とする極限錐を構成。
方針：同じ余錐を反転し、元の反変な全共変表現可能図式を適用する。
規約：元の頂点・全図式・全錐と、その全係数での極限性を保持。
使われ方：compact 対象の有限余極限閉性と κ-filtered 余極限との交換。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Compact
variable {K C : SSet.{u}} [Quasicategory C] {D : K ⟶ C}

/-- 同じ元の余錐から作る、反変な全共変 Hom 関手の図式上の全錐。 -/
def colimitRepresentableCone (c : JoinCocone D) :
    JoinCone ((SSet.uliftFunctor.{u + 1, u}).map (SSet.opFunctor.map D) ≫
      covariantRepresentableDiagram C) :=
  mapJoinCone (covariantRepresentableDiagram C)
    (JoinCone.ulift.{u, u + 1} (SerrePositivity.InfinityCategories.F1B.coconeReverseCone c))

/-- 構成した全錐の頂点は、元の指定余錐の頂点からの同じ全共変 Hom。 -/
lemma colimitRepresentableCone_vertex (c : JoinCocone D) :
    (colimitRepresentableCone c).vertex =
      functorVertex (covariantRepresentableInfinity c.vertex) := by
  rw [colimitRepresentableCone, mapJoinCone_vertex, JoinCone.ulift_vertex,
    SerrePositivity.InfinityCategories.F1B.coconeReverseCone_vertex, covariantRepresentableDiagram_vertex]

/-- 元の余極限余錐からの全 Hom の錐は、全係数で同じ各点極限錐になる。 -/
lemma colimitRepresentableCone_isPointwiseLimit (c : JoinCocone D) (hc : IsColimitCone c) :
    IsPointwiseLimitCone (colimitRepresentableCone c) :=
  covariantRepresentableDiagram_isPointwiseLimit (SerrePositivity.InfinityCategories.F1B.coconeReverseCone c)
    ((SerrePositivity.InfinityCategories.F1B.isColimitCone_iff_reverseCone c).mp hc)

/-- 元の余極限余錐からの同じ全 Hom は、関手 ∞ 圏内の元の図式の極限。 -/
lemma colimitRepresentableCone_isLimit (c : JoinCocone D) (hc : IsColimitCone c) :
    IsLimitCone (colimitRepresentableCone c) :=
  isLimitCone_of_pointwise _ (colimitRepresentableCone_isPointwiseLimit c hc)

end SerrePositivity.InfinityCategories.F2.Compact
