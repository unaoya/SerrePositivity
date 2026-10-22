module

public import SerrePositivity.InfinityCategories.F2.Compact.FullCompactReflection
public import SerrePositivity.InfinityCategories.F2.Compact.YonedaCompact
public import SerrePositivity.InfinityCategories.F2.Ind.KappaColimits

/-!
概要：元の Indκ 内の表現可能前層は、元の全共変 Hom による意味で κ-compact。
方針：元の全部分包含の全 Hom 比較と、同じ κ-filtered 余極限の保存を合成する。
規約：元の Yoneda 因子化を厳密に保持。Ind の単一 filtered 表示は使わない。
使われ方：HTT 5.3.5.5、compact な Ind 対象と Yoneda retract 閉包の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Compact
variable {C : SSet.{u}} [Quasicategory C]

/-- 元の Ind 包含は、前層内の同じ対象の κ-compact 性を反映する。 -/
lemma ind_isKappaCompact_of_presheaf (κ : Cardinal.{u}) (x : Ind.IndInfinity κ C _⦋0⦌)
    (hx : IsKappaCompact.{u, u + 1} κ ((Ind.indInclusionPresheaf κ C).app _ x)) :
    IsKappaCompact.{u, u + 1} κ x :=
  isKappaCompact_fullSubcomplex_of_image κ (Ind.IsIndVertex κ C) x
    (fun _ _ _ D c hc ↦ Ind.ind_inclusion_isColimit κ D c hc) hx

/-- 元の Indκ 内へ因子化した同じ Yoneda 像は κ-compact。 -/
lemma indYoneda_isKappaCompact (κ : Cardinal.{u}) (y : C _⦋0⦌) :
    IsKappaCompact.{u, u + 1} κ
      ((Ind.indYoneda κ C).app (Opposite.op ⦋0⦌) (ULift.up y)) := by
  apply ind_isKappaCompact_of_presheaf
  change IsKappaCompact.{u, u + 1} κ
    ((Ind.indYoneda κ C ≫ Ind.indInclusionPresheaf κ C).app _ (ULift.up y))
  rw [Ind.indYoneda_inclusion]
  exact yonedaInfinityMap_isKappaCompact κ y

end SerrePositivity.InfinityCategories.F2.Compact
