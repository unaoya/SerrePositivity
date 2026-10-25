module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.SmallPresentationComparison
public import SerrePositivity.InfinityCategories.F2.Presentable.SmallPosetColimitCompactUniverse

/-!
概要：対象上の小部分表示の余極限は、底の圏で同じ濃度に関して compact。
方針：射影の余極限保存と、小 poset 余極限の compact 閉性を使う。
規約：指定余極限頂点を変えない。使われ方：共通小部分表示の compact な比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization
open HomotopyLimits Compact

/-- 対象上の指定小 poset 余極限は、底の compact 頂点を保つ。 -/
lemma smallSlicePresentation_projection_compact
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {C : SSet.{u + 1}} [Quasicategory C] (hC : HasSmallColimits C)
    (x : (Δ[0] : SSet.{u + 1}) ⟶ C)
    (P : Type u) [PartialOrder P] (hP : HasCardinalLT P μ)
    (E : (SSet.uliftFunctor.{u + 1, u}).obj (nerve P) ⟶ sliceOver x)
    (a : JoinCocone E) (ha : IsColimitCone a)
    (hE : ∀ k, IsKappaCompact.{u, u + 1} μ
      ((E ≫ sliceOverProjection x).app (Opposite.op ⦋0⦌) k)) :
    IsKappaCompact.{u, u + 1} μ ((sliceOverProjection x).app _ a.vertex) := by
  have hc := sliceOverProjection_preservesSmallColimits hC x (nerve P) E a ha
  have h := isKappaCompact_smallPosetColimit_universe hμ P hP
    (mapJoinCocone (sliceOverProjection x) a) hc hE
  rw [Ind.mapJoinCocone_vertex] at h
  exact h

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
