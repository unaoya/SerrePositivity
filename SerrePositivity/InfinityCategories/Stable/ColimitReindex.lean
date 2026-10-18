module
public import SerrePositivity.InfinityCategories.Stable.ColimitRestriction
public import SerrePositivity.InfinityCategories.Stable.ConeOpposite
public import SerrePositivity.InfinityCategories.F1.CosliceRestrictionIso

/-! # 同型な図式による余極限性の判定

概要：基底図式の同型による制限は余極限性を保存し反映する。
方針：coslice の制限同型と始頂点の同型不変性を使う。
規約：値域の quasicategory 性は不要。
使われ方：反転した cospan の余錐を標準 span に取り替える。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：図式の同型に沿う余錐の制限は余極限性を保存し反映する。
方針：coslice の制限同型を始頂点の同型不変性に適用する。
規約：値域は任意。使われ方：反転した四角形の標準表示との比較。 -/
lemma isColimitCone_iff_restrict_of_isIso {K₀ K X : SSet.{u}}
    {p : K ⟶ X} (c : JoinCocone p) (f : K₀ ⟶ K) [IsIso f] :
    IsColimitCone c ↔ IsColimitCone (c.restrict f) := by
  exact isInitialVertex_iff_of_isIso (sliceUnderRestrict p f) c

/-- 概要：反転した極限錐を同型な基底に制限して余極限性を判定する。
方針：極限錐の反転と図式の同型による余極限性の同値を合成する。
規約：反転後の基底への同型を与える。使われ方：cospan と標準 span の比較。 -/
lemma isLimitCone_iff_reverseCocone_restrict {K L X : SSet.{u}}
    {p : K ⟶ X} (c : JoinCone p) (f : L ⟶ K.op) [IsIso f] :
    IsLimitCone c ↔ IsColimitCone (c.reverseCocone.restrict f) :=
  (isLimitCone_iff_reverseCocone c).trans
    (isColimitCone_iff_restrict_of_isIso c.reverseCocone f)

end SerrePositivity.InfinityCategories
