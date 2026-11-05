module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.KST.LocalizingInvariants.LaxVerdierProductFiberComponents

/-!
概要：実 product fiber の下辺は、元の包含と両 lax 射影の組を同時に保持する。
方針：全図式同型の自然性と指定中項成分を合成し、既存の両射影の式へ移す。
規約：同じ fiber 四角形と左項の比較を使用。使われ方：d8 の元の二脚。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant
end SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant
namespace SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant
open SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant
local instance productLegsSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
local instance productLegsSquareQuasicategory :
    Quasicategory (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) := F2.quasicategory_tensor _ _
variable {Φ : StableInfinity.{u} ⟶ Sp.{u}} (hΦ : IsLocalizingInvariant Φ)
  {C D E A Q : StableCategory.{u}} (p : ExactMap C E) (q : ExactMap D E)
  (i : ExactMap A (laxCategory p q)) (r : ExactMap (laxCategory p q) Q)
  (h : IsVerdierSequence i r)

lemma laxQuotientProductFiberComparison_bottom :
    squareHoBottom (hΦ.laxQuotientProductFiberSquare p q i r h).square ≫
        (hΦ.laxQuotientProductFiberMiddleIso p q i r h).hom =
      (FunctorIso.app (hΦ.laxQuotientProductFiberComparison p q i r h)
        (stdSimplex.obj₀Equiv.symm (0 : Fin 2), stdSimplex.obj₀Equiv.symm (0 : Fin 2))).hom ≫
          squareHoBottom (hΦ.laxQuotientFiberTriangle p q i r h).square ≫
            (hΦ.laxQuotientProjectionMiddleIso p q i r h).hom := by
  have hn := (hΦ.laxQuotientProductFiberComparison p q i r h).toNatIso.hom.naturality
    (Truncated.HomotopyCategory.homMk
      (squareBottomArrow (𝟙 (Δ[1] ⊗ Δ[1] : SSet.{u + 1}))))
  change squareHoBottom (hΦ.laxQuotientProductFiberSquare p q i r h).square ≫
      (FunctorIso.app (hΦ.laxQuotientProductFiberComparison p q i r h)
        (stdSimplex.obj₀Equiv.symm (1 : Fin 2), stdSimplex.obj₀Equiv.symm (0 : Fin 2))).hom =
    (FunctorIso.app (hΦ.laxQuotientProductFiberComparison p q i r h)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2), stdSimplex.obj₀Equiv.symm (0 : Fin 2))).hom ≫
        squareHoBottom (hΦ.laxQuotientFiberTriangle p q i r h).square at hn
  rw [hΦ.laxQuotientProductFiberComparison_middle p q i r h] at hn
  have ht := congrArg (fun k => k ≫ (hΦ.laxQuotientProjectionMiddleIso p q i r h).hom) hn
  simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
    Category.comp_id] using ht

lemma laxQuotientProductFiber_bottom_fst :
    squareHoBottom (hΦ.laxQuotientProductFiberSquare p q i r h).square ≫
        (hΦ.laxQuotientProductFiberMiddleIso p q i r h).hom ≫
          SpectrumHo.hom (Binary.fst (value Φ C) (value Φ D)) =
      (hΦ.laxQuotientProductFiberLeftIso p q i r h).hom ≫
        SpectrumHo.hom (valueMap Φ i) ≫ SpectrumHo.hom (valueMap Φ (laxFst p q)) := by
  rw [← Category.assoc, laxQuotientProductFiberComparison_bottom, Category.assoc,
    Category.assoc, laxQuotientProjectionMiddleIso_bottom_fst]
  simp only [laxQuotientProductFiberLeftIso, Iso.trans_hom, Category.assoc]

lemma laxQuotientProductFiber_bottom_snd :
    squareHoBottom (hΦ.laxQuotientProductFiberSquare p q i r h).square ≫
        (hΦ.laxQuotientProductFiberMiddleIso p q i r h).hom ≫
          SpectrumHo.hom (Binary.snd (value Φ C) (value Φ D)) =
      (hΦ.laxQuotientProductFiberLeftIso p q i r h).hom ≫
        SpectrumHo.hom (valueMap Φ i) ≫ SpectrumHo.hom (valueMap Φ (laxSnd p q)) := by
  rw [← Category.assoc, laxQuotientProductFiberComparison_bottom, Category.assoc,
    Category.assoc, laxQuotientProjectionMiddleIso_bottom_snd]
  simp only [laxQuotientProductFiberLeftIso, Iso.trans_hom, Category.assoc]

end SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant.laxQuotientProductFiberComparison_bottom := _root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientProductFiberComparison_bottom

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant.laxQuotientProductFiber_bottom_fst := _root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientProductFiber_bottom_fst

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant.laxQuotientProductFiber_bottom_snd := _root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientProductFiber_bottom_snd

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.productLegsSimplicialCategory (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant.productLegsSimplicialCategory := _root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.productLegsSimplicialCategory

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant.productLegsSquareQuasicategory := _root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.productLegsSquareQuasicategory
