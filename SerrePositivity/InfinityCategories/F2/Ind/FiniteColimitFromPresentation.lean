module

public import SerrePositivity.InfinityCategories.F2.Ind.YonedaCoconeFamily
public import SerrePositivity.InfinityCategories.F2.Ind.FunctorFilteredColimits
public import SerrePositivity.InfinityCategories.F2.Ind.DiagramFilteredPresentation
public import SerrePositivity.InfinityCategories.Core.ColimitDiagramIso

/-!
概要：元の有限全図式の単一 filtered 表示から、その同じ図式の余極限を構成する。
方針：元の C 全余極限族を補完し、余極限同士の交換と下方全余錐の一意性を使う。
規約：Yoneda の有限余極限保存の交換入力を明示し、元の全図式へ戻す。
使われ方：有限半順序形状の Ind 余極限の公開結論。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 元の有限図式の単一 filtered 表示と明示交換から、同じ全図式の余極限が存在する。 -/
lemma ind_hasColimit_of_singleFilteredDiagramPresentation (κ : Cardinal.{u})
    (hκ : Cardinal.aleph0 ≤ κ) (hex : IndFiniteLimitExchangeInput.{u})
    {K C : SSet.{u}} [K.Finite] [Quasicategory C] [HasFiniteColimits C]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ IndInfinity κ C)
    (hD : HasSingleFilteredDiagramPresentation κ D) : HasColimit D := by
  obtain ⟨I, hI, hfiltered, a, d, hdv, hd⟩ := hD
  letI := hI
  letI := hfiltered
  obtain ⟨l, hl, hlim⟩ := exists_indYoneda_finiteColimit_coconeFamily κ hκ hex a
  let p := indYonedaCoconeFamily κ l
  obtain ⟨c, hc, hp, _⟩ := exists_indFunctor_kappaFiltered_colimit κ p
  have hr : ∀ i, IsColimitCone (functorVertexCocone (p.app (Opposite.op ⦋0⦌) i)) := by
    rintro ⟨i⟩
    exact indYonedaCoconeFamily_isColimit κ l (fun i ↦ (hlim i).2) i
  have ht := colimitCoconeFamily_completion_isColimit p c hp hr
  let j := joinInl ((SSet.uliftFunctor.{u + 1, u}).obj K) (Δ[0] : SSet.{u + 1})
  let q := reindexFunctorCocone c j
  have hq : IsColimitCone q := isColimitCone_functor_of_pointwise q (hp.reindex j)
  have he : p ≫ (pre j).app (IndInfinity κ C) =
      (SSet.uliftFunctor.{u + 1, u}).map a ≫ diagramYoneda κ K C := by
    change indYonedaCoconeFamily κ l ≫ coconeRestriction _ _ = _
    rw [indYonedaCoconeFamily_restriction, hl]
  let q' : JoinCocone ((SSet.uliftFunctor.{u + 1, u}).map a ≫ diagramYoneda κ K C) :=
    ⟨q.val, q.property.trans he⟩
  have hq' : IsColimitCone q' :=
    (isColimitCone_iff_of_coconeMap_eq q' q rfl).mpr hq
  have e := colimitVertexIso q' d hq' hd
  have hv : functorVertex (j ≫ (functorVertexCocone c.vertex).val) = q'.vertex := by
    change functorVertex (j ≫ (functorVertexEquiv _ _).symm c.vertex) =
      ((pre j).app (IndInfinity κ C)).app (Opposite.op ⦋0⦌) c.vertex
    apply (functorVertexEquiv _ _).symm.injective
    change (functorVertexEquiv _ _).symm
      ((functorVertexEquiv _ _) (j ≫ (functorVertexEquiv _ _).symm c.vertex)) = _
    rw [Equiv.symm_apply_apply, functorVertexMap_precomp]
  have e' : FunctorIso (j ≫ (functorVertexCocone c.vertex).val) D := by
    change VertexIso (functorVertex (j ≫ (functorVertexCocone c.vertex).val))
      (functorVertex D)
    rw [hv, ← hdv]
    exact e
  exact (hasColimit_iff_of_functorIso e').mp ⟨functorVertexCocone c.vertex, ht⟩

end SerrePositivity.InfinityCategories.F2.Ind
