module

public import SerrePositivity.InfinityCategories.F2.Ind.FiniteHornDiagramPresentation
public import SerrePositivity.InfinityCategories.F2.Ind.ConeCompletionBaseIso
public import SerrePositivity.InfinityCategories.F2.Ind.CospanSquareCompletion
public import SerrePositivity.InfinityCategories.F2.Ind.YonedaCospanSquareFamily
public import SerrePositivity.InfinityCategories.F2.Ind.FiniteLimitsColimits
public import SerrePositivity.InfinityCategories.F1.Joins.LimitConeDiagramComparison
public import SerrePositivity.InfinityCategories.Stable.SquareFunctorTransport

/-!
概要：安定な C の Ind の指定 cospan は、実押し出しでもある極限全錐を持つ。
方針：同じ単一 filtered 表示の全極限錐族を補完し、両普遍性を元の図式へ輸送する。
規約：明示交換入力と C の有限極限存在を保持し、元の全図式を結論する。
使われ方：I-2 c の Ind の零角列の一致と安定性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 指定した元の cospan の極限全錐を、同時に実押し出し四角形として構成する。 -/
lemma ind_exists_bicartesianLimitCone (κ : Cardinal.{u}) [Fact κ.IsRegular]
    (hκ : Cardinal.aleph0 ≤ κ) (hex : IndFiniteLimitExchangeInput.{u})
    {C : SSet.{u}} [Quasicategory C] [IsStable C] [HasFiniteLimits C]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj (horn 2 2) ⟶ IndInfinity κ C) :
    ∃ d : JoinCone D, IsLimitCone d ∧
      IsPushoutSquare ((uliftCospanSquareReadingIso.{u, u + 1}).inv ≫ d.val) := by
  obtain ⟨I, hI, hfiltered, a, d0, hdv, hd⟩ :=
    ind_cospan_has_singleFilteredDiagramPresentation κ D
  letI := hI
  letI := hfiltered
  obtain ⟨l, hl, hlim⟩ := exists_yoneda_finiteLimit_coneFamily a
  let p := indYonedaConeFamily κ l
  obtain ⟨c, hc, hp, hinc⟩ := exists_indFunctor_kappaFiltered_colimit κ p
  have hr (i : I _⦋0⦌) : IsLimitCone (mapJoinCone (indInclusionPresheaf κ C)
      (functorVertexCone (p.app (Opposite.op ⦋0⦌) (ULift.up i)))) :=
    indYonedaConeFamily_inclusion_isLimit κ l (fun i => (hlim i).1) i
  have ht := ind_filteredLimitCone_isLimit κ hκ (hex.exchange (horn 2 2)) p c hinc hr
  let r := (uliftCospanSquareReadingIso.{u, u + 1}).inv
  have hs (i : ((SSet.uliftFunctor.{u + 1, u}).obj I) _⦋0⦌) :
      IsPushoutSquare (r ≫ (functorVertexCone (p.app (Opposite.op ⦋0⦌) i)).val) := by
    obtain ⟨i⟩ := i
    have h := (indYonedaCospanSquareFamily_bicartesian κ hκ hex l
      (fun i => (hlim i).1) i).2
    change IsPushoutSquare ((functorVertexEquiv _ _).symm
      (((pre r).app (IndInfinity κ C)).app _ (p.app _ (ULift.up i)))) at h
    rw [functorVertexMap_precomp] at h
    exact h
  have hb := ind_cospanSquare_completion_isPushout κ p c hp hs
  letI : HasFiniteLimits (IndInfinity κ C) := ind_hasFiniteLimits κ hκ hex C
  letI : ((SSet.uliftFunctor.{u + 1, u}).obj (horn 2 2 : SSet.{u})).Finite :=
    SSet.finite_of_iso (uliftHornIso.{u, u + 1} 2 2).symm
  obtain ⟨d, hdl⟩ := HasFiniteLimits.hasLimit D
  have e := indConeCompletionBaseIso κ a l hl c hp D d0 hd hdv
  have ec := limitConeDiagramIso (fun q => HasFiniteLimits.hasLimit q)
    (functorVertexCone c.vertex) d ht.1 hdl e
  exact ⟨d, hdl, hb.of_functorIso (ec.precomp r)⟩

end SerrePositivity.InfinityCategories.F2.Ind
