module

public import SerrePositivity.InfinityCategories.F2.Ind.YonedaConeFamily
public import SerrePositivity.InfinityCategories.F2.Ind.FilteredLimitConeCompletion
public import SerrePositivity.InfinityCategories.F2.Ind.DiagramFilteredPresentation
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.FunctorCoconeReindex
public import SerrePositivity.InfinityCategories.F1B.Cones.LimitDiagramIsoImage

/-!
概要：元の有限図式の単一 filtered 表示から、同じ図式の有限極限を構成する。
方針：C の全極限錐族を同じ添字で補完し、下方の余極限の一意性で元の図式へ戻す。
規約：有限交換は明示入力とし、表示の頂点は元の全図式そのもの。
使われ方：有限半順序形状の Ind 極限存在の結論。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 元の有限図式の単一 filtered 表示と明示交換から、その同じ図式の極限が存在する。 -/
lemma ind_exists_limitCone_of_singleFilteredDiagramPresentation (κ : Cardinal.{u})
    (hκ : Cardinal.aleph0 ≤ κ) (hex : IndFiniteLimitExchangeInput.{u})
    {K C : SSet.{u}} [K.Finite] [Quasicategory C] [HasFiniteLimits C]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ IndInfinity κ C)
    (hD : HasSingleFilteredDiagramPresentation κ D) :
    ∃ c : JoinCone D, IsLimitCone c ∧
      IsLimitCone (mapJoinCone (indInclusionPresheaf κ C) c) := by
  obtain ⟨I, hI, hfiltered, a, d, hdv, hd⟩ := hD
  letI := hI
  letI := hfiltered
  obtain ⟨l, hl, hlim⟩ := exists_yoneda_finiteLimit_coneFamily a
  let p := indYonedaConeFamily κ l
  obtain ⟨c, hc, hp, hinc⟩ := exists_indFunctor_kappaFiltered_colimit κ p
  have hr : ∀ i : I _⦋0⦌, IsLimitCone (mapJoinCone (indInclusionPresheaf κ C)
      (functorVertexCone (p.app (Opposite.op ⦋0⦌) (ULift.up i)))) :=
    indYonedaConeFamily_inclusion_isLimit κ l (fun i ↦ (hlim i).1)
  have ht := ind_filteredLimitCone_isLimit κ hκ (hex.exchange K) p c hinc hr
  let j := joinInr (Δ[0] : SSet.{u + 1}) ((SSet.uliftFunctor.{u + 1, u}).obj K)
  let q := reindexFunctorCocone c j
  have hq : IsColimitCone q := isColimitCone_functor_of_pointwise q (hp.reindex j)
  have he : p ≫ (pre j).app (IndInfinity κ C) =
      (SSet.uliftFunctor.{u + 1, u}).map a ≫ diagramYoneda κ K C := by
    change indYonedaConeFamily κ l ≫ coneRestriction _ _ = _
    rw [indYonedaConeFamily_restriction, hl]
  let q' : JoinCocone ((SSet.uliftFunctor.{u + 1, u}).map a ≫ diagramYoneda κ K C) :=
    ⟨q.val, q.property.trans he⟩
  have hq' : IsColimitCone q' :=
    (isColimitCone_iff_of_coconeMap_eq q' q rfl).mpr hq
  have e := colimitVertexIso q' d hq' hd
  have hv : functorVertex (j ≫ (functorVertexCone c.vertex).val) = q'.vertex := by
    change functorVertex (j ≫ (functorVertexEquiv _ _).symm c.vertex) =
      ((pre j).app (IndInfinity κ C)).app (Opposite.op ⦋0⦌) c.vertex
    apply (functorVertexEquiv _ _).symm.injective
    change (functorVertexEquiv _ _).symm
      ((functorVertexEquiv _ _) (j ≫ (functorVertexEquiv _ _).symm c.vertex)) = _
    rw [Equiv.symm_apply_apply, functorVertexMap_precomp]
  have e' : FunctorIso (j ≫ (functorVertexCone c.vertex).val) D := by
    change VertexIso (functorVertex (j ≫ (functorVertexCone c.vertex).val))
      (functorVertex D)
    rw [hv, ← hdv]
    exact e
  exact exists_limitCone_of_functorIso_with_image (indInclusionPresheaf κ C) e'
    (functorVertexCone c.vertex) ht.1 ht.2

end SerrePositivity.InfinityCategories.F2.Ind
