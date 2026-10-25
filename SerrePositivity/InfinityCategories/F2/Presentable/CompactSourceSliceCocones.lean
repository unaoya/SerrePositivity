module

public import SerrePositivity.InfinityCategories.F2.Presentable.SmallCompactSourceSlices
public import SerrePositivity.InfinityCategories.F2.Presentable.PredicateOverCocones
public import SerrePositivity.InfinityCategories.F2.Presentable.SmallQuasicategoryColimitCompact
public import SerrePositivity.InfinityCategories.F2.Presentable.SmallQuasicategoryDiagramFactorization

/-!
概要：compact 始域 slice の任意の小試験図式へ内部余錐を与える。
方針：元の始域の余極限と compact 閉性を使い、有界 Hull で一般形状へ戻す。
規約：固定対象と全図式を保持し、元の圏の accessibility は不要。
使われ方：fiber の compact comma 射影の cofinal 判定における下方余錐。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：compact 始域 slice の μ-small quasicategory 図式は内部余錐を持つ。
方針：元の始域図式の余極限を compact 性とともに slice へ持ち上げる。
規約：元の固定対象は任意であり compact 性は不要。
使われ方：一般小試験形状へ移す前の余錐構成。 -/
lemma nonempty_compactSourceSlice_cocone_of_smallQuasicategory
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {K : SSet.{u}} [Quasicategory K] (hK : IsKappaSmall μ K)
    {C : SSet.{u + 1}} [Quasicategory C] (hC : HasSmallColimits C)
    (x : (Δ[0] : SSet.{u + 1}) ⟶ C)
    (r : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ compactSourceSlice μ x) :
    Nonempty (JoinCocone r) := by
  let P : C _⦋0⦌ → Prop := Compact.IsKappaCompact.{u, u + 1} μ
  let j := (fullSubcomplexOnVertices (sliceOver x)
    (fun v ↦ P ((sliceOverProjection x).app _ v))).ι
  let F := (r ≫ j) ≫ sliceOverProjection x
  obtain ⟨c, hc⟩ := hC K F
  have hF : ∀ k, P (F.app (Opposite.op ⦋0⦌) k) := by
    intro k
    exact fullSubcomplexOnVertices_vertex (r.app (Opposite.op ⦋0⦌) k)
  have hv : P c.vertex :=
    isKappaCompact_smallQuasicategoryColimit_universe hμ K hK c hc hF
  obtain ⟨d, _⟩ := exists_predicateOver_cocone_lifting_colimit P x r c hc hv
  exact ⟨d⟩

/-- 概要：compact 始域 slice の任意 μ-small 図式は内部余錐を持つ。
方針：同じ濃度の有界 Hull へ因子化し、全余錐を元の図式へ制限する。
規約：強極限濃度も試験形状の quasicategory 性も要求しない。
使われ方：元の coslice の全余錐と cofinal 判定。 -/
lemma nonempty_compactSourceSlice_cocone_of_small
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {K : SSet.{u}} (hK : IsKappaSmall μ K)
    {C : SSet.{u + 1}} [Quasicategory C] (hC : HasSmallColimits C)
    (x : (Δ[0] : SSet.{u + 1}) ⟶ C)
    (r : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ compactSourceSlice μ x) :
    Nonempty (JoinCocone r) :=
  nonempty_cocone_of_smallQuasicategory_tests hμ
    (fun L _ hL s ↦ nonempty_compactSourceSlice_cocone_of_smallQuasicategory hμ hL hC x s)
    K hK r

end SerrePositivity.InfinityCategories.F2.Presentable
