module

public import SerrePositivity.KST.LocalizingInvariants.SuspensionExactDiagrams
public import SerrePositivity.KST.LocalizingInvariants.LaxVerdierProjectionFiber

/-!
概要：一般商 Q の二脚を、C 側の逆 shift を明示して元の完全関手から定める。
方針：C 包含の後の商を Q 内で逆 suspension し、ΣΩ の全関手同型を値へ移す。
規約：Q と商の普遍性は入力のまま。使われ方：d8 の符号付き cospan の二脚。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants
variable {C D E Q : StableCategory.{u}} (p : ExactMap C E) (q : ExactMap D E)
  (r : ExactMap (laxCategory p q) Q)

def laxQuotientCLeg : C ⟶ Q :=
  LaxInclusion.exactFromC p q ≫ r ≫ SuspensionExact.inverseExactMap Q

def laxQuotientDLeg : D ⟶ Q := LaxInclusion.exactFromD p q ≫ r

def laxQuotientCLeg_suspensionIso : FunctorIso
    ((laxQuotientCLeg p q r).hom ≫ SuspensionExact.map Q.obj)
    (LaxInclusion.fromC p q ≫ r.hom) := by
  change FunctorIso
    ((LaxInclusion.fromC p q ≫ r.hom ≫ (SuspensionExact.equivalence Q.obj).inv) ≫
      (SuspensionExact.equivalence Q.obj).hom) (LaxInclusion.fromC p q ≫ r.hom)
  have e := FunctorIso.precomp (SuspensionExact.equivalence Q.obj).invHomIso
    (LaxInclusion.fromC p q ≫ r.hom)
  simpa only [Category.assoc, Category.comp_id] using e

variable (Φ : StableInfinity.{u} ⟶ Sp.{u})

lemma valueMap_quotientFromC_shift :
    SpectrumHo.hom (valueMap Φ (LaxInclusion.exactFromC p q)) ≫
        SpectrumHo.hom (valueMap Φ r) =
      SpectrumHo.hom (valueMap Φ (laxQuotientCLeg p q r)) ≫
        SpectrumHo.hom (valueMap Φ (SuspensionExact.exactMap Q)) := by
  change (stableValueFunctor Φ).map (LaxInclusion.exactFromC p q) ≫
    (stableValueFunctor Φ).map r = (stableValueFunctor Φ).map (laxQuotientCLeg p q r) ≫
      (stableValueFunctor Φ).map (SuspensionExact.exactMap Q)
  let f : C ⟶ Q := LaxInclusion.exactFromC p q ≫ r
  let g : C ⟶ Q := laxQuotientCLeg p q r ≫ SuspensionExact.exactMap Q
  have e : FunctorIso f.hom g.hom := (laxQuotientCLeg_suspensionIso p q r).symm
  have h := valueMap_hom_eq_of_functorIso Φ e
  change (stableValueFunctor Φ).map f = (stableValueFunctor Φ).map g at h
  simpa only [f, g, CategoryTheory.Functor.map_comp] using h

lemma valueMap_quotientFromD :
    SpectrumHo.hom (valueMap Φ (LaxInclusion.exactFromD p q)) ≫
      SpectrumHo.hom (valueMap Φ r) = SpectrumHo.hom (valueMap Φ (laxQuotientDLeg p q r)) := by
  exact ((stableValueFunctor Φ).map_comp (LaxInclusion.exactFromD p q) r).symm

namespace IsLocalizingInvariant
variable {Φ} (hΦ : IsLocalizingInvariant Φ)

lemma laxQuotientProjectionDifferenceHom_shift_C :
    SpectrumHo.hom (Binary.inl (value Φ C) (value Φ D)) ≫
        hΦ.laxQuotientProjectionDifferenceHom p q r =
      SpectrumHo.hom (valueMap Φ (laxQuotientCLeg p q r)) ≫
        SpectrumHo.hom (valueMap Φ (SuspensionExact.exactMap Q)) := by
  rw [laxQuotientProjectionDifferenceHom_C]
  exact valueMap_quotientFromC_shift p q r Φ

lemma laxQuotientProjectionDifferenceHom_shift_D :
    SpectrumHo.hom (Binary.inr (value Φ C) (value Φ D)) ≫
      hΦ.laxQuotientProjectionDifferenceHom p q r =
        SpectrumHo.hom (valueMap Φ (laxQuotientDLeg p q r)) := by
  rw [laxQuotientProjectionDifferenceHom_D]
  exact valueMap_quotientFromD p q r Φ

end IsLocalizingInvariant
end SerrePositivity.KST.LocalizingInvariants
