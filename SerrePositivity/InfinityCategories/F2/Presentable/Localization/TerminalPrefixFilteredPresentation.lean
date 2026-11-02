module

public import SerrePositivity.InfinityCategories.F2.Presentable.TerminalSourceCoslice
public import SerrePositivity.InfinityCategories.F2.Presentable.SourceCosliceRestrictedVertex
public import SerrePositivity.InfinityCategories.F2.Filtered.FilteredCosliceCofinality
public import SerrePositivity.InfinityCategories.F1B.Cofinality.TrivialFibrationCofinality
public import SerrePositivity.InfinityCategories.HomotopyLimits.UniverseCosliceProjection

/-!
概要：終頂点を持つ既存の全前置図式を固定した、元の filtered 表示を構成する。
方針：前置図式の coslice の共終性と公開 P の全余錐の射影判定を使う。
規約：元の全余錐を制限し、元の表示頂点と全脚を保つ。
使われ方：HTT 5.5.4.13 の相対一段因子化へ渡す、既存前置図式の下の表示。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization
open HomotopyLimits

/-- 終頂点を持つ全前置図式の coslice は、filtered 添字圏へ共終に射影する。 -/
lemma terminalPrefix_cosliceProjection_isRightCofinal
    {K I : SSet.{u}} [Quasicategory K] [Quasicategory I] [IsFilteredInfinity I]
    (t : K _⦋0⦌) (ht : IsTerminalVertex t) (a : K ⟶ I) :
    IsRightCofinal (sliceUnderProjection a) := by
  let j := SSet.yonedaEquiv.symm t
  have : Mono j := cofinalPointInclusion_mono t
  have : TrivialKanFibration (sliceUnderRestrict a j) :=
    sliceUnderRestrict_trivialKanFibration a j (F1B.terminalPoint_rightAnodyne ht)
  have h := (isRightCofinal_of_trivialKanFibration (sliceUnderRestrict a j)).comp
    (isRightCofinal_sliceUnderProjection_of_filtered (j ≫ a))
  rwa [sliceUnderRestrict_projection] at h

/-- 元の全前置図式の下に制限した同じ指定余錐も、filtered 余極限となる。 -/
lemma terminalPrefix_restrictedCocone_isColimit
    {μ : Cardinal.{u}} [Fact μ.IsRegular]
    {K I : SSet.{u}} [Quasicategory K] [Quasicategory I] [IsKappaFiltered μ I]
    (hK : IsKappaSmall μ K) (t : K _⦋0⦌) (ht : IsTerminalVertex t) (a : K ⟶ I)
    {C : SSet.{u + 1}} [Quasicategory C]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ C)
    (c : JoinCocone D) (hc : IsColimitCone c) :
    IsColimitCone (sourceCosliceRestrictedCocone ((SSet.uliftFunctor.{u + 1, u}).map a)
      (uliftSliceUnderIso.{u, u + 1} a).hom D c) := by
  have hμ : μ.IsRegular := Fact.out
  have : IsKappaFiltered μ (sliceUnder a) := isKappaFiltered_sliceUnder hμ hK a
  have : IsFilteredInfinity I := isFilteredInfinity_of_isKappaFiltered hμ.aleph0_le I
  let b := (SSet.uliftFunctor.{u + 1, u}).map a
  let s := (uliftSliceUnderIso.{u, u + 1} a).hom
  have hs : IsRightCofinal (s ≫ sliceUnderProjection b) := by
    dsimp only [s, b]
    rw [uliftSliceUnderIso_projection]
    exact Ind.isRightCofinal_ulift _ (terminalPrefix_cosliceProjection_isRightCofinal t ht a)
  have ht' := (isTerminalVertex_iff_ulift.{u, u + 1} t).mp ht
  apply (terminalSourceCoslice_isColimitCone_iff_projection hμ (ULift.up t) ht'
    (b ≫ D) _ (sourceCosliceRestrictedCocone b s D c)).mpr
  apply (isColimitCone_iff_of_cocone_val_eq _ (c.restrict (s ≫ sliceUnderProjection b))
    (sourceCosliceRestrictedCocone_projection b s D c)).mpr
  exact (Ind.isColimitCone_iff_restrict_rightCofinal (s ≫ sliceUnderProjection b) hs c).mp hc

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
