module

public import SerrePositivity.InfinityCategories.F2.Presentable.TerminalSourceCoslice
public import SerrePositivity.InfinityCategories.F2.Ind.ConeTerminalSliceComparison
public import SerrePositivity.InfinityCategories.Core.ColimitCosliceRestriction

/-!
概要：余極限を持つ全前置図式の coslice を、同じ余極限点の coslice と比較する。
方針：余極限余錐全体からの二つの自明 Kan 制限を使う。
規約：比較は元の終点射影と厳密に可換。
使われ方：極限前置図式を固定する compact 性と filtered 余極限の判定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback

/-- 概要：前置図式とその余極限点の coslice は終点を保って同値となる。
方針：全余極限余錐の coslice への切断と、右余錐点への制限を合成する。
規約：終点射影の比較は元の射の等式。
使われ方：小さい全前置図式の相対因子化。 -/
lemma exists_colimitSourceCosliceComparison
    {K C : SSet.{u}} [Quasicategory K] [Quasicategory C]
    {q : K ⟶ C} (cq : JoinCocone q) (hcq : IsColimitCone cq) :
    ∃ H : sliceUnder q ⟶ sliceUnder (joinInr K Δ[0] ≫ cq.val),
      IsQCatEquivalence H ∧ H ≫ sliceUnderProjection (joinInr K Δ[0] ≫ cq.val) =
        sliceUnderProjection q := by
  let r := colimitCosliceRestriction cq
  have : TrivialKanFibration r := colimitCosliceRestriction_trivialKanFibration cq hcq
  obtain ⟨s, hs⟩ := trivialKanFibration_exists_section r
  have hr := isQCatEquivalence_of_trivialKanFibration r
  have hseq : IsQCatEquivalence s := by
    apply hr.cancel_right
    rw [hs]
    exact (QCatEquivalence.refl _).isQCatEquivalence
  let j := joinInr K (Δ[0] : SSet.{u})
  let g := sliceUnderRestrict cq.val j
  have : TrivialKanFibration g :=
    sliceUnderRestrict_trivialKanFibration cq.val j (Ind.coneTip_rightAnodyne K)
  refine ⟨s ≫ g, hseq.comp (isQCatEquivalence_of_trivialKanFibration g), ?_⟩
  calc
    _ = s ≫ sliceUnderProjection cq.val := by
      rw [Category.assoc, sliceUnderRestrict_projection]
    _ = s ≫ (r ≫ sliceUnderProjection q) :=
      congrArg (fun z ↦ s ≫ z) (colimitCosliceRestriction_projection cq).symm
    _ = sliceUnderProjection q := by rw [← Category.assoc, hs, Category.id_comp]

/-- 概要：余極限を持つ前置図式の全 coslice の filtered 余極限は終点で判定できる。
方針：終点を保つ一点 coslice との同値で、同じ指定余錐を比較する。
規約：元の全余錐を保持し、前置図式に終対象を要求しない。
使われ方：前層内で全前置図式を固定した filtered 表示の余極限判定。 -/
lemma colimitSourceCoslice_isColimitCone_iff_projection
    {μ : Cardinal.{u}} (hμ : μ.IsRegular)
    {K C : SSet.{u + 1}} [Quasicategory K] [Quasicategory C]
    {q : K ⟶ C} (cq : JoinCocone q) (hcq : IsColimitCone cq)
    {I : SSet.{u}} [Quasicategory I] [IsKappaFiltered μ I]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ sliceUnder q) (c : JoinCocone D) :
    IsColimitCone c ↔ IsColimitCone (mapJoinCocone (sliceUnderProjection q) c) := by
  obtain ⟨H, hH, hHp⟩ := exists_colimitSourceCosliceComparison cq hcq
  have hp := pointSourceCoslice_isColimitCone_iff_projection hμ
    (joinInr K Δ[0] ≫ cq.val) (D ≫ H) (mapJoinCocone H c)
  have hval : (mapJoinCocone (sliceUnderProjection (joinInr K Δ[0] ≫ cq.val))
      (mapJoinCocone H c)).val = (mapJoinCocone (sliceUnderProjection q) c).val := by
    change (c.val ≫ H) ≫ sliceUnderProjection (joinInr K Δ[0] ≫ cq.val) =
      c.val ≫ sliceUnderProjection q
    rw [Category.assoc, hHp]
  exact (equivalence_isColimitCone_iff hH c).trans
    (hp.trans (isColimitCone_iff_of_cocone_val_eq _ _ hval))

end SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback
