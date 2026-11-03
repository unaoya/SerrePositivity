module
public import SerrePositivity.InfinityCategories.Core.TerminalBoundaryTransport
public import SerrePositivity.InfinityCategories.Core.FunctorPointwiseLimitCriterion
public import SerrePositivity.InfinityCategories.Core.Cocone
public import SerrePositivity.InfinityCategories.Core.ConeFamily
public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.Core.Join
public import SerrePositivity.InfinityCategories.Core.Limit
public import SerrePositivity.InfinityCategories.Core.Slice
public import SerrePositivity.InfinityCategories.Core.VertexFiber
public import SerrePositivity.InfinityCategories.PinchedHom.Basic
public import SerrePositivity.InfinityCategories.F1.CosliceCoconeDiagramEvaluation

/-! # 関手同型による錐・四角形の普遍性の移送

概要：全錐・全余錐の関手同型は極限性・余極限性を保つ。
方針：制限射の相対境界充填を同型で輸送し、正方形の形状同型で四角形に適用する。
規約：固定図式は異なってよい。使われ方：D7 の標準四角形から任意の四角形への移送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial

/-- 全余錐の関手同型は余極限性を保つ。 -/
lemma IsColimitCone.of_functorIso {K X : SSet.{u}} [Quasicategory X]
    {p q : K ⟶ X} {c : JoinCocone p} {d : JoinCocone q}
    (hc : IsColimitCone c) (e : FunctorIso c.val d.val) : IsColimitCone d := by
  apply isColimitCone_of_initialBoundaryLifting_coconeRestriction d
  exact InitialBoundaryLifting.of_vertexIso (coconeRestriction K X) hc.initialBoundaryLifting e

/-- 全錐の関手同型は極限性を保つ。 -/
lemma IsLimitCone.of_functorIso {K X : SSet.{u}} [Quasicategory X]
    {p q : K ⟶ X} {c : JoinCone p} {d : JoinCone q}
    (hc : IsLimitCone c) (e : FunctorIso c.val d.val) : IsLimitCone d := by
  apply isLimitCone_of_terminalBoundaryLifting_coneRestriction d
  exact TerminalBoundaryLifting.of_vertexIso (coneRestriction K X)
    (terminalBoundaryLifting_coneRestriction_of_isLimitCone c hc) e

/-- 四角形全体の関手同型は押し出し性を保つ。 -/
lemma IsPushoutSquare.of_functorIso {X : SSet.{u}} [Quasicategory X]
    {F G : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X}
    (hF : IsPushoutSquare F) (e : FunctorIso F G) : IsPushoutSquare G :=
  IsColimitCone.of_functorIso hF (e.precomp spanCoconeSquareIso.hom)

/-- 四角形全体の関手同型は引き戻し性を保つ。 -/
lemma IsPullbackSquare.of_functorIso {X : SSet.{u}} [Quasicategory X]
    {F G : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X}
    (hF : IsPullbackSquare F) (e : FunctorIso F G) : IsPullbackSquare G :=
  IsLimitCone.of_functorIso hF (e.precomp cospanConeSquareIso.hom)

/-- 同じ図式の錐の slice 内の同型を全錐の関手同型へ写す。 -/
def coneFunctorIsoOfVertexIso {K X : SSet.{u}} [Quasicategory X] {p : K ⟶ X}
    (c d : JoinCone p) (e : VertexIso (X := sliceOver p) c d) :
    FunctorIso c.val d.val := by
  let q := sliceConeFamilyMap p ≫ vertexFiberι (coneRestriction K X) (functorVertex p)
  have hc : q.app (Opposite.op ⦋0⦌) c = functorVertex c.val :=
    congrArg Subtype.val (sliceConeFamilyMap_app_zero p c)
  have hd : q.app (Opposite.op ⦋0⦌) d = functorVertex d.val :=
    congrArg Subtype.val (sliceConeFamilyMap_app_zero p d)
  have h := VertexIso.map e q
  change VertexIso (q.app (Opposite.op ⦋0⦌) c) (q.app (Opposite.op ⦋0⦌) d) at h
  rw [hc, hd] at h
  exact h

/-- 同じ図式の余錐の coslice 内の同型を全余錐の関手同型へ写す。 -/
def coconeFunctorIsoOfVertexIso {K X : SSet.{u}} [Quasicategory X] {p : K ⟶ X}
    (c d : JoinCocone p) (e : VertexIso (X := sliceUnder p) c d) :
    FunctorIso c.val d.val := by
  have h := VertexIso.map e (cosliceCoconeDiagramMap p)
  change VertexIso ((cosliceCoconeDiagramMap p).app (Opposite.op ⦋0⦌) c)
    ((cosliceCoconeDiagramMap p).app (Opposite.op ⦋0⦌) d) at h
  rw [cosliceCoconeDiagramMap_vertex, cosliceCoconeDiagramMap_vertex] at h
  exact h

end SerrePositivity.InfinityCategories
