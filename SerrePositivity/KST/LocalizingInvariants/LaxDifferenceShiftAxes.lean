module

public import SerrePositivity.KST.LocalizingInvariants.LaxDifferenceCComparison
public import SerrePositivity.KST.LocalizingInvariants.LaxDifferenceDComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxVerdierProjectionFiber

/-!
概要：実差関手の値の C 軸は E(p) の後の E(Σ)、D 軸は元の E(q) となる。
方針：全関手同型を stableValueFunctor で射の類の等式へ移し、積の軸の式に接続する。
規約：E(Σ) を負恒等とする段階は未証明。使われ方：Tamme の符号付き cospan。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants
variable (Φ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} ⟶ Sp.{u})
  {C D E : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D E)

lemma valueMap_fromC_difference :
    SpectrumHo.hom (valueMap Φ (LaxInclusion.exactFromC p q)) ≫
        SpectrumHo.hom (valueMap Φ (exactLaxDifference p q)) =
      SpectrumHo.hom (valueMap Φ p) ≫
        SpectrumHo.hom (valueMap Φ (SuspensionExact.exactMap E)) := by
  change (stableValueFunctor Φ).map (LaxInclusion.exactFromC p q) ≫
    (stableValueFunctor Φ).map (exactLaxDifference p q) =
      (stableValueFunctor Φ).map p ≫ (stableValueFunctor Φ).map (SuspensionExact.exactMap E)
  let f : C ⟶ E := LaxInclusion.exactFromC p q ≫ exactLaxDifference p q
  let g : C ⟶ E := p ≫ SuspensionExact.exactMap E
  have e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f.hom g.hom := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (LaxInclusion.fromC p q ≫ laxDifference p q)
      (p.hom ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.map E.obj)
    exact fromC_differenceIso p q
  have h := valueMap_hom_eq_of_functorIso Φ e
  change (stableValueFunctor Φ).map f = (stableValueFunctor Φ).map g at h
  simpa only [f, g, CategoryTheory.Functor.map_comp] using h

lemma valueMap_fromD_difference :
    SpectrumHo.hom (valueMap Φ (LaxInclusion.exactFromD p q)) ≫
      SpectrumHo.hom (valueMap Φ (exactLaxDifference p q)) = SpectrumHo.hom (valueMap Φ q) := by
  change (stableValueFunctor Φ).map (LaxInclusion.exactFromD p q) ≫
    (stableValueFunctor Φ).map (exactLaxDifference p q) = (stableValueFunctor Φ).map q
  let f : D ⟶ E := LaxInclusion.exactFromD p q ≫ exactLaxDifference p q
  have e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f.hom q.hom := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (LaxInclusion.fromD p q ≫ laxDifference p q) q.hom
    exact fromD_differenceIso p q
  have h := valueMap_hom_eq_of_functorIso Φ e
  change (stableValueFunctor Φ).map f = (stableValueFunctor Φ).map q at h
  simpa only [f, CategoryTheory.Functor.map_comp] using h

namespace IsLocalizingInvariant
variable {Φ} (hΦ : IsLocalizingInvariant Φ)

lemma laxQuotientProjectionDifferenceHom_cofiber_C :
    SpectrumHo.hom (Binary.inl (value Φ C) (value Φ D)) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientProjectionDifferenceHom hΦ) p q (exactLaxDifference p q) =
      SpectrumHo.hom (valueMap Φ p) ≫
        SpectrumHo.hom (valueMap Φ (SuspensionExact.exactMap E)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientProjectionDifferenceHom_C]
  exact valueMap_fromC_difference Φ p q

lemma laxQuotientProjectionDifferenceHom_cofiber_D :
    SpectrumHo.hom (Binary.inr (value Φ C) (value Φ D)) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientProjectionDifferenceHom hΦ) p q (exactLaxDifference p q) =
        SpectrumHo.hom (valueMap Φ q) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientProjectionDifferenceHom_D]
  exact valueMap_fromD_difference Φ p q

end IsLocalizingInvariant
end SerrePositivity.KST.LocalizingInvariants
