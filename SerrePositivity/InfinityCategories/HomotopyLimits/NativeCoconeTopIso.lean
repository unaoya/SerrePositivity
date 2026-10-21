module

public import SerrePositivity.InfinityCategories.HomotopyLimits.NativeCoconeIsoRepresentative

/-!
概要：同じ coslice 同型の代表辺の頂点変換を、同じ射を持つ同型として保持する。
方針：元の可逆辺を全余錐の族と頂点制限へ写す。
規約：各点で選択した代表を変更せず、自然な族の存在は要求しない。
使われ方：実際の余極限脚と標準余極限脚の可換式の合成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
open SSet.Truncated.HomotopyCategory
variable {K X : SSet.{u}} [Quasicategory X] {p : K ⟶ X} {q d : JoinCocone p}
  (e : VertexIso (X := sliceUnder p) q d)

/-- 同じ元の coslice 同型の代表を全余錐へ写した辺は可逆。 -/
lemma nativeCoconeIsoWholeEdge_isInvertible :
    IsInvertibleEdge (X := (ihom (join K (Δ[0] : SSet.{u}))).obj X)
      (nativeCoconeFunctorEdge (nativeCoconeIsoRepresentative e)).toTruncated := by
  have h := (nativeCoconeIsoRepresentative_isInvertible e).map
    (nativeCoconeFunctorFamily p)
  exact (isInvertibleEdge_congr
    (e := (nativeCoconeIsoRepresentative e).map
      ((truncation 2).map (nativeCoconeFunctorFamily p)))
    (f := (nativeCoconeFunctorEdge (nativeCoconeIsoRepresentative e)).toTruncated) rfl).mp h

/-- 同じ元の coslice 同型の代表の頂点変換は可逆。 -/
lemma nativeCoconeIsoTopEdge_isInvertible :
    IsInvertibleEdge (X := (ihom K).obj X)
      (coconeWholeEdgeTop q d
        (nativeCoconeFunctorEdge (nativeCoconeIsoRepresentative e)).toTruncated).toTruncated := by
  have h := (nativeCoconeIsoWholeEdge_isInvertible e).map
    ((pre (SSet.const (coconeRightApexVertex K) : K ⟶ join K Δ[0])).app X)
  exact (isInvertibleEdge_congr
    (e := (nativeCoconeFunctorEdge (nativeCoconeIsoRepresentative e)).toTruncated.map
      ((truncation 2).map
        ((pre (SSet.const (coconeRightApexVertex K) : K ⟶ join K Δ[0])).app X)))
    (f := (coconeWholeEdgeTop q d
      (nativeCoconeFunctorEdge (nativeCoconeIsoRepresentative e)).toTruncated).toTruncated)
    rfl).mp h

/-- 同じ元の coslice 比較辺の頂点変換を、その同じ Hom 類を持つ同型として保持。 -/
def nativeCoconeIsoTopIso :
    VertexIso (X := (ihom K).obj X)
      (functorVertex (SSet.const q.vertex)) (functorVertex (SSet.const d.vertex)) := by
  have : IsIso (homMk (coconeWholeEdgeTop q d
      (nativeCoconeFunctorEdge (nativeCoconeIsoRepresentative e)).toTruncated).toTruncated) :=
    nativeCoconeIsoTopEdge_isInvertible e
  exact asIso (homMk (coconeWholeEdgeTop q d
    (nativeCoconeFunctorEdge (nativeCoconeIsoRepresentative e)).toTruncated).toTruncated)

/-- 元の頂点同型の順方向は、同じ元の代表辺の頂点変換の類そのもの。 -/
lemma nativeCoconeIsoTopIso_hom :
    (nativeCoconeIsoTopIso e).hom = homMk (coconeWholeEdgeTop q d
      (nativeCoconeFunctorEdge (nativeCoconeIsoRepresentative e)).toTruncated).toTruncated := rfl

end SerrePositivity.InfinityCategories.HomotopyLimits
