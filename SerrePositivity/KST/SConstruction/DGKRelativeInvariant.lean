module
public import SerrePositivity.KST.SConstruction.DGKFixedInterface
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativeTammeRectangle

/-! # 固定 dg 始域上の相対局所化不変量と K-10 の接続
概要：K-10 の不変量を、固定 ν でパラメータ化した同じ S 上の関手として量化する。
方針：Sp 正本の相対条件・相対 Tamme 長方形を読み取り専用で特殊化する。
規約：一般の安定 ∞ 圏への E の延長も K の局所化性も仮定しない。
使われ方：dg gluing と商からの具体的長方形を、相対切除へ接続する。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet Spectra
open SerrePositivity.InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (A : Type u) [CommRing A]

/-- 固定 ν に相対的な局所化不変量。値関手の始域は同じ厳密 dg 入力 S。 -/
abbrev DGKRelativeLocalizingInvariant := RelativeLocalizingInvariant (dgKInputNu.{u, v} A)

/-- 同じ S 上の任意の E に要求する相対局所化条件。 -/
abbrev IsDGKRelativeLocalizingInvariant (E : dgKInputInfinity.{u, v} A ⟶ Sp) :=
  IsRelativeLocalizingInvariant (dgKInputNu A) E

/-- 元の dg 入力の四角形と、その ν 像の実 Verdier 提示。 -/
abbrev DGKRelativeVerdierDiagram := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.RelativeVerdierDiagram (dgKInputNu.{u, v} A)

/-- K-10：同じ S の長方形の ν 像を固定すれば、相対 E は比較四角形を pullback に送る。 -/
lemma dgKRelativeTammeComparison_isPullback
    {C D B X Q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{max (u + 1) v}}
    (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C B) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D B)
    (i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap X (laxCategory p q)) (r : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (laxCategory p q) Q)
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i r)
    (F : (Δ[2] ⊗ Δ[1] : SSet.{max (u + 1) v + 1}) ⟶ dgKInputInfinity.{u, v} A)
    (hF : F ≫ dgKInputNu A = (LaxUniversalDifference.rectangle p q i r h).diagram)
    {E : dgKInputInfinity.{u, v} A ⟶ Sp.{max (u + 1) v}}
    (hE : IsDGKRelativeLocalizingInvariant A E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.relativeRectangle
      (dgKInputNu A) p q i r h F hF).comparisonSquare ≫ E) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.relative_comparison_isPullback
    (dgKInputNu A) p q i r h F hF hE

/-- 元の比較四角形の ν 像は、元の Tamme 比較四角形そのもの。 -/
lemma dgKRelativeTammeComparison_image
    {C D B X Q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{max (u + 1) v}}
    (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C B) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D B)
    (i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap X (laxCategory p q)) (r : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (laxCategory p q) Q)
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i r)
    (F : (Δ[2] ⊗ Δ[1] : SSet.{max (u + 1) v + 1}) ⟶ dgKInputInfinity.{u, v} A)
    (hF : F ≫ dgKInputNu A = (LaxUniversalDifference.rectangle p q i r h).diagram) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.relativeRectangle
      (dgKInputNu A) p q i r h F hF).comparisonSquare ≫ dgKInputNu A =
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalDifferenceSquare.comparisonSquare p q i r h :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.relative_comparison_image (dgKInputNu A) p q i r h F hF

end SerrePositivity.KST.SConstruction
