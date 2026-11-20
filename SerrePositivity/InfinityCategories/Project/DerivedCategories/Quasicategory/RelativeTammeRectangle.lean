module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalDifferenceOuter
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.RelativeVerdierPullback
public import SerrePositivity.KST.LocalizingInvariants.RelativeInvariant
public import SerrePositivity.KST.LocalizingInvariants.RelativeVerdierPullback

/-!
概要：元の Tamme 比較長方形の S 内の持ち上げから、相対 d8 の実 pullback を得る。
方針：ν の像の等式だけで右面・外周を既存 Verdier 提示に同定し、相対定理を適用する。
規約：E の StableInfinity への延長を要求しない。使われ方：dg gluing・商の持ち上げ。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference
end SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory
open _root_.SerrePositivity.KST
open _root_.SerrePositivity.KST.LocalizingInvariants
open _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference
variable {S : SSet.{u + 1}} (ν : S ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u})
  {C D B A Q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C B) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D B)
  (i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A (laxCategory p q)) (r : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (laxCategory p q) Q)
  (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i r)
  (F : (Δ[2] ⊗ Δ[1] : SSet.{u + 1}) ⟶ S)
  (hF : F ≫ ν = (rectangle p q i r h).diagram)

/-- 指定した同じ S 長方形を、ν 像の元の二つの Verdier 列で認証する。 -/
def relativeRectangle : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.RelativeVerdierRectangle ν :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.RelativeVerdierRectangle.ofImage F (identityDiagram Q) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.outerDiagram p q i r h)
    (by rw [hF]; exact (rectangle p q i r h).right_eq)
    (by
      rw [hF]
      change _ = (β_ _ _).hom ≫ (β_ _ _).hom ≫ _
      rw [← Category.assoc, SymmetricCategory.symmetry, Category.id_comp])

/-- S 内の比較正方形の E 像は実 pullback。ν 像だけで E を定義し直さない。 -/
lemma relative_comparison_isPullback {E : S ⟶ Spectra.Sp.{u}}
    (hE : IsRelativeLocalizingInvariant ν E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.relativeRectangle ν p q i r h F hF).comparisonSquare ≫ E) :=
  RelativeVerdierRectangle.comparisonSquare_isPullback _ hE

/-- 同じ相対比較は元の絶対比較正方形を ν 像として持つ。 -/
lemma relative_comparison_image :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.relativeRectangle ν p q i r h F hF).comparisonSquare ≫ ν =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalDifferenceSquare.comparisonSquare p q i r h := by
  change ((β_ _ _).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 2) ≫ ν = _
  rw [Category.assoc]
  change (β_ _ _).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare (F ≫ ν) 2 = _
  rw [hF, (rectangle p q i r h).left_eq, ← Category.assoc,
    SymmetricCategory.symmetry, Category.id_comp]

/-- 恒等提示源では同じ元の絶対 Tamme 比較正方形に戻る。 -/
lemma relative_id_comparison :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.relativeRectangle (𝟙 _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u}) p q i r h
      (rectangle p q i r h).diagram (Category.comp_id _)).comparisonSquare =
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalDifferenceSquare.comparisonSquare p q i r h := by
  simpa only [Category.comp_id] using
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.relative_comparison_image (𝟙 _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u}) p q i r h
      (rectangle p q i r h).diagram (Category.comp_id _)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
