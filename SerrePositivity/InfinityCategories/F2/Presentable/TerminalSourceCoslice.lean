module

public import SerrePositivity.InfinityCategories.F2.Presentable.PointCosliceCompactVertices
public import SerrePositivity.InfinityCategories.F2.Presentable.SourceCosliceRestrictedColimit
public import SerrePositivity.InfinityCategories.F2.Presentable.CompactEquivalenceUniverse
public import SerrePositivity.InfinityCategories.F1B.Cofinality.TerminalPointAnodyne

/-!
概要：終頂点を持つ元の図式の coslice の compact 性と filtered 余極限を終点で判定する。
方針：終頂点への right anodyne 制限の全同値で、一点 coslice の判定へ戻す。
規約：元の全図式を保ち、有限前置図式の各脚だけの比較にしない。
使われ方：可算交互構成の全有限前置図式を保つ因子化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits

/-- 概要：終頂点を持つ図式の余錐は、終頂点の像と頂点が compact なら coslice 内で compact。
方針：終頂点への全同値制限で compact 性を反映する。
規約：図式全体の余錐そのものを compact と判定する。
使われ方：全有限前置図式を固定した相対因子化。 -/
lemma isKappaCompact_terminalSourceCosliceVertex
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {K C : SSet.{u + 1}} [Quasicategory K] [Quasicategory C]
    (t : K _⦋0⦌) (ht : IsTerminalVertex t) (p : K ⟶ C) (c : JoinCocone p)
    (hp : Compact.IsKappaCompact.{u, u + 1} μ (p.app _ t))
    (hc : Compact.IsKappaCompact.{u, u + 1} μ c.vertex) :
    Compact.IsKappaCompact.{u, u + 1} μ (C := sliceUnder p) c := by
  let i := SSet.yonedaEquiv.symm t
  have : Mono i := cofinalPointInclusion_mono t
  have : TrivialKanFibration (sliceUnderRestrict p i) :=
    sliceUnderRestrict_trivialKanFibration p i (F1B.terminalPoint_rightAnodyne ht)
  let e := qCatEquivalenceOfTrivialKanFibration (sliceUnderRestrict p i)
  apply (isKappaCompact_iff_equivalence_universe e c).mpr
  apply isKappaCompact_pointCosliceVertex hμ (i ≫ p) (c.restrict i)
  · dsimp only [i]
    simpa only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] using hp
  · simpa only [JoinCocone.vertex_restrict] using hc

/-- 概要：終頂点を持つ図式の coslice の指定 filtered 余錐は底で判定できる。
方針：終頂点への制限同値と一点 coslice の全余錐判定を合成する。
規約：元の圏の余極限存在を要求しない。
使われ方：全前置図式の下での元の表示余極限の検出。 -/
lemma terminalSourceCoslice_isColimitCone_iff_projection
    {κ : Cardinal.{u}} (hκ : κ.IsRegular)
    {K C : SSet.{u + 1}} [Quasicategory K] [Quasicategory C]
    (t : K _⦋0⦌) (ht : IsTerminalVertex t) (p : K ⟶ C)
    {I : SSet.{u}} [Quasicategory I] [IsKappaFiltered κ I]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ sliceUnder p) (c : JoinCocone D) :
    IsColimitCone c ↔ IsColimitCone (mapJoinCocone (sliceUnderProjection p) c) := by
  let i := SSet.yonedaEquiv.symm t
  have : Mono i := cofinalPointInclusion_mono t
  let q := sliceUnderRestrict p i
  have : TrivialKanFibration q :=
    sliceUnderRestrict_trivialKanFibration p i (F1B.terminalPoint_rightAnodyne ht)
  have hq := (qCatEquivalenceOfTrivialKanFibration q).isQCatEquivalence
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.equivalence_isColimitCone_iff hq c).trans
  apply (pointSourceCoslice_isColimitCone_iff_projection hκ (i ≫ p)
    (D ≫ q) (mapJoinCocone q c)).trans
  apply isColimitCone_iff_of_cocone_val_eq
  change (c.val ≫ q) ≫ sliceUnderProjection (i ≫ p) = c.val ≫ sliceUnderProjection p
  rw [Category.assoc, sliceUnderRestrict_projection]

end SerrePositivity.InfinityCategories.F2.Presentable
