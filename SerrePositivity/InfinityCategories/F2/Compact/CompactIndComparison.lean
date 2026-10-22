module

public import SerrePositivity.InfinityCategories.F2.Compact.IdemToInd

/-!
概要：元の Idem(C) から、元の Indκ(C) の κ-compact 全部分圏への実比較を構成する。
方針：元の包含の像の compact 性で全単体を因子化し、両 Yoneda を厳密に照合する。
規約：全包含・全 Yoneda・全 Hom の充満忠実性を保持。本質全射性はまだ主張しない。
使われ方：F2N-3(d) と F2N-4(e) の比較。
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

/-- 元の Ind-Yoneda を、同じ Ind 内の元の κ-compact 全部分圏へ因子化する。 -/
def compactIndYoneda (κ : Cardinal.{u}) (C : SSet.{u}) [Quasicategory C] :
    (SSet.uliftFunctor.{u + 1, u}).obj C ⟶
      kappaCompactObjects.{u, u + 1} κ (Ind.IndInfinity κ C) :=
  fullSubcomplexLift (IsKappaCompact.{u, u + 1} κ) (Ind.indYoneda κ C)
    (fun x ↦ by rcases x with ⟨x⟩; exact indYoneda_isKappaCompact κ x)

/-- 同じ compact 因子化は、元の全 Ind-Yoneda を厳密に回収する。 -/
lemma compactIndYoneda_inclusion (κ : Cardinal.{u}) :
    compactIndYoneda κ C ≫ kappaCompactInclusion.{u, u + 1} κ (Ind.IndInfinity κ C) =
      Ind.indYoneda κ C := fullSubcomplexLift_ι _ _ _

/-- 元の Idem(C) の包含を、元の Indκ の同じ compact 全部分圏へ因子化する。 -/
def idemToCompactInd (κ : Cardinal.{u}) (C : SSet.{u}) [Quasicategory C] :
    Idempotent.Idem C ⟶ kappaCompactObjects.{u, u + 1} κ (Ind.IndInfinity κ C) :=
  fullSubcomplexLift (IsKappaCompact.{u, u + 1} κ) (idemToInd κ C)
    (idemToInd_isKappaCompact κ)

/-- 元の Ind 内への同じ全写像を、厳密に回収する。 -/
lemma idemToCompactInd_inclusion (κ : Cardinal.{u}) :
    idemToCompactInd κ C ≫ kappaCompactInclusion.{u, u + 1} κ (Ind.IndInfinity κ C) =
      idemToInd κ C := fullSubcomplexLift_ι _ _ _

/-- 元の Idem(C) から compact Ind 対象への同じ実比較は充満忠実。 -/
lemma idemToCompactInd_isFullyFaithful (κ : Cardinal.{u}) :
    IsFullyFaithful (idemToCompactInd κ C) := by
  apply (kappaCompactInclusion_isFullyFaithful.{u, u + 1} κ (Ind.IndInfinity κ C)).cancel_right
  rw [idemToCompactInd_inclusion]
  exact idemToInd_isFullyFaithful κ

/-- 元の Idem-Yoneda と Ind-Yoneda の全図式は、同じ前層包含を介して厳密に一致。 -/
lemma idemYoneda_toInd (κ : Cardinal.{u}) :
    Idempotent.idemYoneda C ≫ idemToInd κ C = Ind.indYoneda κ C := by
  have : Mono (Ind.indInclusionPresheaf κ C) :=
    inferInstanceAs (Mono (fullSubcomplexOnVertices (PresheafInfinity C)
      (Ind.IsIndVertex κ C)).ι)
  apply (cancel_mono (Ind.indInclusionPresheaf κ C)).mp
  rw [Category.assoc, idemToInd_inclusion, Idempotent.idemYoneda_inclusion,
    Ind.indYoneda_inclusion]

/-- compact Ind への実比較は、元の二つの全 Yoneda 因子化を厳密に照合する。 -/
lemma idemYoneda_toCompactInd (κ : Cardinal.{u}) :
    Idempotent.idemYoneda C ≫ idemToCompactInd κ C = compactIndYoneda κ C := by
  have : Mono (kappaCompactInclusion.{u, u + 1} κ (Ind.IndInfinity κ C)) :=
    inferInstanceAs (Mono (fullSubcomplexOnVertices (Ind.IndInfinity κ C)
      (IsKappaCompact.{u, u + 1} κ)).ι)
  apply (cancel_mono (kappaCompactInclusion.{u, u + 1} κ (Ind.IndInfinity κ C))).mp
  rw [Category.assoc, idemToCompactInd_inclusion, compactIndYoneda_inclusion, idemYoneda_toInd]

end SerrePositivity.InfinityCategories.F2.Compact
