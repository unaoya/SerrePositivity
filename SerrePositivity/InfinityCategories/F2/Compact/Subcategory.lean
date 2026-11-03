module

public import SerrePositivity.InfinityCategories.F2.Compact.RepresentableRetractions
public import SerrePositivity.InfinityCategories.Core.Idempotent.FullSubcomplexSplitting
public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.FullSubcomplexMapping

/-!
概要：κ-compact 対象の全部分 ∞ 圏と、その coherent 冪等完備性を構成。
方針：証明済みの retract 閉性と元の全分裂の全部分圏への反映を使う。
規約：Ind の単一 filtered 表示や Yoneda 像の compact 性をここで仮定しない。
使われ方：Ind の compact 部分と Idem(C) の全 ∞ 圏としての比較。
-/

@[expose] public section
noncomputable section
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Compact
open Idempotent

/-- 小さい κ-filtered 添字について compact な対象の、元の圏の全部分 ∞ 圏。 -/
def kappaCompactObjects (κ : Cardinal.{u}) (C : SSet.{max u v}) [Quasicategory C] :
    SSet.{max u v} :=
  fullSubcomplexOnVertices C (IsKappaCompact.{u, v} κ)

/-- κ-compact 対象は元の全辺・全高次を保持する quasicategory をなす。 -/
instance kappaCompactObjects_quasicategory (κ : Cardinal.{u}) (C : SSet.{max u v})
    [Quasicategory C] : Quasicategory (kappaCompactObjects.{u, v} κ C) :=
  fullSubcomplexOnVertices_quasicategory _ _

/-- 元の圏への κ-compact 全部分圏の包含。 -/
def kappaCompactInclusion (κ : Cardinal.{u}) (C : SSet.{max u v}) [Quasicategory C] :
    kappaCompactObjects.{u, v} κ C ⟶ C :=
  (fullSubcomplexOnVertices C (IsKappaCompact.{u, v} κ)).ι

/-- 元の包含は全写像空間で充満忠実。 -/
lemma kappaCompactInclusion_isFullyFaithful (κ : Cardinal.{u}) (C : SSet.{max u v})
    [Quasicategory C] : IsFullyFaithful (kappaCompactInclusion.{u, v} κ C) :=
  isFullyFaithful_fullSubcomplexOnVertices_ι _ _

/-- 冪等完備な元の圏の κ-compact 全部分圏は、全 coherent 分裂について冪等完備。 -/
lemma kappaCompactObjects_isIdempotentComplete (κ : Cardinal.{u})
    {C : SSet.{max u v}} [Quasicategory C] (hC : IsIdempotentComplete C) :
    IsIdempotentComplete (kappaCompactObjects.{u, v} κ C) :=
  fullSubcomplex_isIdempotentComplete (IsKappaCompact.{u, v} κ)
    (fun r hy ↦ IsKappaCompact.of_retract r hy) hC

end SerrePositivity.InfinityCategories.F2.Compact
