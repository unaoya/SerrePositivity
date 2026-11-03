module

public import SerrePositivity.InfinityCategories.F2.Ind.FiniteHornDiagramPresentation
public import SerrePositivity.InfinityCategories.F2.Ind.CoconeCompletionBaseIso
public import SerrePositivity.InfinityCategories.F2.Ind.SpanSquareCompletion
public import SerrePositivity.InfinityCategories.F2.Ind.YonedaSpanSquareFamily
public import SerrePositivity.InfinityCategories.F2.Ind.FiniteLimitsColimits
public import SerrePositivity.InfinityCategories.F1.Joins.ColimitCoconeDiagramComparison
public import SerrePositivity.InfinityCategories.F1.SquareFunctorTransport

/-!
概要：安定な C の Ind の指定 span は、実引き戻しでもある余極限全余錐を持つ。
方針：同じ単一 filtered 表示の全余極限族を補完し、両普遍性を元の図式へ輸送する。
規約：明示交換入力と C の有限全存在を保持し、元の全図式を結論する。
使われ方：I-2 c の零角列の一致と Ind の安定性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 元の指定 span の余極限全余錐を、同時に実引き戻し四角形として構成する。 -/
lemma ind_exists_bicartesianColimitCocone (κ : Cardinal.{u}) [Fact κ.IsRegular]
    (hκ : Cardinal.aleph0 ≤ κ) (hex : IndFiniteLimitExchangeInput.{u})
    {C : SSet.{u}} [Quasicategory C] [IsStable C]
    [HasFiniteLimits C] [HasFiniteColimits C]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj (horn 2 0) ⟶ IndInfinity κ C) :
    ∃ d : JoinCocone D, IsColimitCone d ∧
      IsPullbackSquare ((uliftSpanSquareReadingIso.{u, u + 1}).inv ≫ d.val) := by
  obtain ⟨I, hI, hfiltered, a, d0, hdv, hd⟩ :=
    ind_span_has_singleFilteredDiagramPresentation κ D
  letI := hI
  letI := hfiltered
  obtain ⟨l, hl, hcol⟩ := exists_indYoneda_finiteColimit_coconeFamily κ hκ hex a
  let p := indYonedaCoconeFamily κ l
  obtain ⟨c, hc, hp, hinc⟩ := exists_indFunctor_kappaFiltered_colimit κ p
  have hr (i : ((SSet.uliftFunctor.{u + 1, u}).obj I) _⦋0⦌) :
      IsColimitCone (functorVertexCocone (p.app (Opposite.op ⦋0⦌) i)) := by
    obtain ⟨i⟩ := i
    exact indYonedaCoconeFamily_isColimit κ l (fun i => (hcol i).2) i
  have ht := colimitCoconeFamily_completion_isColimit p c hp hr
  let r := (uliftSpanSquareReadingIso.{u, u + 1}).inv
  have hs (i : I _⦋0⦌) : IsPullbackSquare
      ((r ≫ (functorVertexCocone (p.app (Opposite.op ⦋0⦌) (ULift.up i))).val) ≫
        indInclusionPresheaf κ C) := by
    have h := (indYonedaSpanSquareFamily_bicartesian κ hκ hex l
      (fun i => (hcol i).1) i).1
    change IsPullbackSquare ((functorVertexEquiv _ _).symm
      (((pre r).app (IndInfinity κ C)).app _ (p.app _ (ULift.up i))) ≫
        indInclusionPresheaf κ C) at h
    rw [functorVertexMap_precomp] at h
    exact h
  have hb := ind_spanSquare_completion_isPullback κ hκ (hex.exchange (horn 2 2)) p c hinc hs
  letI : HasFiniteColimits (IndInfinity κ C) := ind_hasFiniteColimits κ hκ hex C
  letI : ((SSet.uliftFunctor.{u + 1, u}).obj (horn 2 0 : SSet.{u})).Finite :=
    SSet.finite_of_iso (uliftHornIso.{u, u + 1} 2 0).symm
  obtain ⟨d, hdc⟩ := HasFiniteColimits.hasColimit D
  have e := indCoconeCompletionBaseIso κ a l hl c hp D d0 hd hdv
  have ec := colimitCoconeDiagramIso (fun q => HasFiniteColimits.hasColimit q)
    (functorVertexCocone c.vertex) d ht hdc e
  exact ⟨d, hdc, hb.of_functorIso (ec.precomp r)⟩

end SerrePositivity.InfinityCategories.F2.Ind
