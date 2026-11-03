module

public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.PrecompositionHomotopy
public import SerrePositivity.InfinityCategories.HomotopyLimits.CoconeDomainHomotopy

/-!
概要：元の全余錐間の変換の底と頂点は、両余錐の元の変換とホモトピー圏で可換。
方針：元の標準形状ホモトピーの前合成自然変換に、元の全余錐の代表辺を入力する。
規約：元の同じ辺・全余錐を保持し、標的の quasicategory 性は不要。
使われ方：指定前層余極限頂点の実際の有限錐像の全脚を標準余錐へ照合する。
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

/-- 元の右頂点への定値写像を指定全余錐で写すと、同じ元の余錐頂点への定値写像。 -/
lemma cocone_const_rightApex {K X : SSet.{u}} {p : K ⟶ X} (q : JoinCocone p) :
    (SSet.const (coconeRightApexVertex K) : K ⟶ join K (Δ[0] : SSet.{u})) ≫ q.val =
      SSet.const q.vertex := by
  rw [SSet.const_comp, cocone_vertex_at_rightApex]

/-- 元の全余錐の代表辺は、標準形状円柱の評価とホモトピー圏で自然。 -/
lemma coconeWholeEdge_domain_naturality {K X : SSet.{u}} {p r : K ⟶ X}
    (q : JoinCocone p) (d : JoinCocone r)
    (e : SSet.Truncated.Edge
      (X := (truncation 2).obj ((ihom (join K (Δ[0] : SSet.{u}))).obj X))
      (functorVertex q.val) (functorVertex d.val)) :
    homMk (e.map ((truncation 2).map ((pre (joinInl K Δ[0])).app X))) ≫
      homMk (functorEdgeOfSimplicialHomotopy
        (functorHomotopyPostcomp (coconeDomainHomotopy K) d.val)) =
    homMk (functorEdgeOfSimplicialHomotopy
      (functorHomotopyPostcomp (coconeDomainHomotopy K) q.val)) ≫
      homMk (e.map ((truncation 2).map
        ((pre (SSet.const (coconeRightApexVertex K) : K ⟶ join K Δ[0])).app X))) := by
  have h := (SerrePositivity.InfinityCategories.F1B.precompositionNatTrans (coconeDomainHomotopy K) X).naturality (homMk e)
  erw [SerrePositivity.InfinityCategories.F1B.precompositionNatTrans_app (coconeDomainHomotopy K) d.val,
    SerrePositivity.InfinityCategories.F1B.precompositionNatTrans_app (coconeDomainHomotopy K) q.val] at h
  exact h

end SerrePositivity.InfinityCategories.HomotopyLimits
