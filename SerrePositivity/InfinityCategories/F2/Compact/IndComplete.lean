module

public import SerrePositivity.InfinityCategories.F2.Compact.IdemFiltered
public import SerrePositivity.InfinityCategories.F2.Compact.IndCompact
public import SerrePositivity.InfinityCategories.F2.Compact.Subcategory
public import SerrePositivity.InfinityCategories.F2.Idempotent.IdemUniverse
public import SerrePositivity.InfinityCategories.F2.Idempotent.StrongSplittingExistence
public import SerrePositivity.InfinityCategories.F1B.KanLimitColimitOpposite

/-!
概要：元の Indκ は、同じ全 coherent 冪等図式について冪等完備。
方針：小さい Idem の κ-filtered 性と元の Ind 内の指定余極限の存在を使う。
規約：元の大きい全 Idem 図式を厳密な宇宙同型で回収する。単一表示は仮定しない。
使われ方：元の Idem(C) から compact Ind 対象への実際の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Compact

/-- 元の Indκ の任意の全 coherent 冪等図式は、同じ元の図式の余極限を持つ。 -/
lemma indIdempotent_hasColimit (κ : Cardinal.{u}) {C : SSet.{u}} [Quasicategory C]
    (d : Idempotent.CoherentIdempotent (Ind.IndInfinity κ C)) : HasColimit d := by
  have := idemShape_isKappaFiltered κ
  exact (F1B.kanHasColimit_iff_restrict_of_isIso d
    (Idempotent.idemShapeUniverseIso.{u, u + 1}).hom).mpr (Ind.ind_hasColimit κ _)

/-- 元の Indκ 自身は、同じ全 coherent 冪等図式について冪等完備。 -/
lemma ind_isIdempotentComplete (κ : Cardinal.{u}) (C : SSet.{u}) [Quasicategory C] :
    Idempotent.IsIdempotentComplete (Ind.IndInfinity κ C) :=
  fun d ↦ Idempotent.strongSplitting_exists_of_hasColimit d (indIdempotent_hasColimit κ d)

/-- 元の Indκ 内の κ-compact 全部分圏も、全 coherent 分裂について冪等完備。 -/
lemma compactInd_isIdempotentComplete (κ : Cardinal.{u}) (C : SSet.{u}) [Quasicategory C] :
    Idempotent.IsIdempotentComplete
      (kappaCompactObjects.{u, u + 1} κ (Ind.IndInfinity κ C)) :=
  kappaCompactObjects_isIdempotentComplete κ (ind_isIdempotentComplete κ C)

end SerrePositivity.InfinityCategories.F2.Compact
