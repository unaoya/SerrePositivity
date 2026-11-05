module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.KST.LocalizingInvariants.LaxDifferenceAdjunction
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.TammeSplitting
public import SerrePositivity.KST.LocalizingInvariants.InvariantLongExact

/-!
概要：充満忠実な右随伴を持つ q に対する局所化不変量の実 fiber 列。
方針：実際に構成した差の Verdier 列を K-5 に渡し、中項を元の二因子の積へ比較する。
規約：Sp の安定性は不使用。使われ方：Tamme の抽象 fiber 列と全整数長完全列。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant
end SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant
namespace SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.IsLocalizingInvariant
open SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant
variable {Φ : _root_.SerrePositivity.InfinityCategories.Stable.Infinity.StableInfinity.{u} ⟶ Sp.{u}} (hΦ : IsLocalizingInvariant Φ)
  {C D E : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap D E)
  (v : E.obj ⟶ D.obj) (a : QCatAdjunction q.hom v) (hv : IsFullyFaithful v)

/-- 元の通常 pullback・lax pullback・差の項の値を結ぶ零角付き実四角形。 -/
def tammeFiberTriangle : ZeroTriangle Sp.{u} :=
  hΦ.abstractFiberTriangle (tammeVerdierSequence p q v a hv)

lemma tammeFiberTriangle_isFiber : IsFiberSequence (hΦ.tammeFiberTriangle p q v a hv) :=
  hΦ.abstractFiberTriangle_isFiber (tammeVerdierSequence p q v a hv)

lemma tammeFiberTriangle_bottom :
    squareBottomEdge ≫ (hΦ.tammeFiberTriangle p q v a hv).square =
      SSet.yonedaEquiv.symm (Φ.app (Opposite.op ⦋1⦌)
        (_root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableArrow (pullbackInclusion p q)).edge) :=
  hΦ.abstractFiberTriangle_bottom (tammeVerdierSequence p q v a hv)

lemma tammeFiberTriangle_right :
    squareRightEdge ≫ (hΦ.tammeFiberTriangle p q v a hv).square =
      SSet.yonedaEquiv.symm (Φ.app (Opposite.op ⦋1⦌)
        (_root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableArrow (exactLaxDifference p q)).edge) :=
  hΦ.abstractFiberTriangle_right (tammeVerdierSequence p q v a hv)

/-- 実 fiber 列の中項から、元の C,D の値の実 ∞ 積への比較同型。 -/
def tammeFiberMiddleIso : SpectrumHo.obj (value Φ (laxCategory p q)) ≅
    SpectrumHo.obj (Binary.obj (value Φ C) (value Φ D)) :=
  hΦ.tammeSplitEquivalence p q

/-- fiber 四角形の実中頂点を、元の二つの値の実 ∞ 積へ同定する。 -/
def tammeFiberSquareMiddleIso : squareHoVertex (hΦ.tammeFiberTriangle p q v a hv).square 1 0 ≅
    SpectrumHo.obj (Binary.obj (value Φ C) (value Φ D)) :=
  hΦ.fiberMiddleIso (tammeVerdierSequence p q v a hv) ≪≫ hΦ.tammeFiberMiddleIso p q

/-- 二因子の積から差の項の値への射。元の差の像との比較を保持する。 -/
def tammeDifferenceHom : SpectrumHo.obj (Binary.obj (value Φ C) (value Φ D)) ⟶
    SpectrumHo.obj (value Φ E) :=
  (hΦ.tammeSplitComparison p q).hom ≫ SpectrumHo.hom (valueMap Φ (exactLaxDifference p q))

lemma tammeFiberSquareMiddleIso_right :
    (hΦ.tammeFiberSquareMiddleIso p q v a hv).hom ≫ hΦ.tammeDifferenceHom p q =
      squareHoRight (hΦ.tammeFiberTriangle p q v a hv).square ≫
        (hΦ.fiberRightIso (tammeVerdierSequence p q v a hv)).hom := by
  change ((hΦ.fiberMiddleIso (tammeVerdierSequence p q v a hv)).hom ≫
    (hΦ.tammeSplitComparison p q).inv) ≫ ((hΦ.tammeSplitComparison p q).hom ≫ _) = _
  rw [Category.assoc, Iso.inv_hom_id_assoc]
  exact hΦ.fiber_right_naturality (tammeVerdierSequence p q v a hv)

lemma tammeDifferenceHom_C : SpectrumHo.hom (Binary.inl (value Φ C) (value Φ D)) ≫
    hΦ.tammeDifferenceHom p q = SpectrumHo.hom (valueMap Φ (LaxInclusion.exactFromC p q)) ≫
      SpectrumHo.hom (valueMap Φ (exactLaxDifference p q)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.IsLocalizingInvariant.tammeDifferenceHom, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.IsLocalizingInvariant.tammeSplitComparison_C]

lemma tammeDifferenceHom_D : SpectrumHo.hom (Binary.inr (value Φ C) (value Φ D)) ≫
    hΦ.tammeDifferenceHom p q = SpectrumHo.hom (valueMap Φ (LaxInclusion.exactFromD p q)) ≫
      SpectrumHo.hom (valueMap Φ (exactLaxDifference p q)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.IsLocalizingInvariant.tammeDifferenceHom, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.IsLocalizingInvariant.tammeSplitComparison_D]

/-- 元の包含と元の差の作用に適合する全整数次数の接続準同型。 -/
def tammeConnecting (j : ℤ) : valueHomotopyGroup Φ E (j + 1) →*
    valueHomotopyGroup Φ (pullbackCategory p q) j :=
  hΦ.connecting (tammeVerdierSequence p q v a hv) j

include hΦ a hv in
lemma tamme_exact_middle (j : ℤ) (x : valueHomotopyGroup Φ (laxCategory p q) j) :
    valueHomotopyMap Φ (exactLaxDifference p q) j x = 1 ↔
      ∃ z : valueHomotopyGroup Φ (pullbackCategory p q) j,
        valueHomotopyMap Φ (pullbackInclusion p q) j z = x :=
  hΦ.exact_middle (tammeVerdierSequence p q v a hv) j x

lemma tamme_exact_left (j : ℤ) (x : valueHomotopyGroup Φ (pullbackCategory p q) j) :
    valueHomotopyMap Φ (pullbackInclusion p q) j x = 1 ↔
      ∃ z : valueHomotopyGroup Φ E (j + 1), hΦ.tammeConnecting p q v a hv j z = x :=
  hΦ.exact_left (tammeVerdierSequence p q v a hv) j x

lemma tamme_exact_right (j : ℤ) (x : valueHomotopyGroup Φ E (j + 1)) :
    hΦ.tammeConnecting p q v a hv j x = 1 ↔
      ∃ z : valueHomotopyGroup Φ (laxCategory p q) (j + 1),
        valueHomotopyMap Φ (exactLaxDifference p q) (j + 1) z = x :=
  hΦ.exact_right (tammeVerdierSequence p q v a hv) j x

end SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.IsLocalizingInvariant

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.IsLocalizingInvariant.tammeConnecting (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant.tammeConnecting := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.IsLocalizingInvariant.tammeConnecting

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.IsLocalizingInvariant.tammeDifferenceHom (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant.tammeDifferenceHom := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.IsLocalizingInvariant.tammeDifferenceHom

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant.tammeDifferenceHom_C := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.IsLocalizingInvariant.tammeDifferenceHom_C

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant.tammeDifferenceHom_D := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.IsLocalizingInvariant.tammeDifferenceHom_D

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.IsLocalizingInvariant.tammeFiberMiddleIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant.tammeFiberMiddleIso := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.IsLocalizingInvariant.tammeFiberMiddleIso

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.IsLocalizingInvariant.tammeFiberSquareMiddleIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant.tammeFiberSquareMiddleIso := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.IsLocalizingInvariant.tammeFiberSquareMiddleIso

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant.tammeFiberSquareMiddleIso_right := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.IsLocalizingInvariant.tammeFiberSquareMiddleIso_right

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.IsLocalizingInvariant.tammeFiberTriangle (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant.tammeFiberTriangle := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.IsLocalizingInvariant.tammeFiberTriangle

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant.tammeFiberTriangle_bottom := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.IsLocalizingInvariant.tammeFiberTriangle_bottom

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant.tammeFiberTriangle_isFiber := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.IsLocalizingInvariant.tammeFiberTriangle_isFiber

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant.tammeFiberTriangle_right := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.IsLocalizingInvariant.tammeFiberTriangle_right

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant.tamme_exact_left := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.IsLocalizingInvariant.tamme_exact_left

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant.tamme_exact_middle := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.IsLocalizingInvariant.tamme_exact_middle

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant.tamme_exact_right := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.IsLocalizingInvariant.tamme_exact_right

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant.tammeDifferenceHom.eq_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.IsLocalizingInvariant.tammeDifferenceHom.eq_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant.tammeFiberSquareMiddleIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.IsLocalizingInvariant.tammeFiberSquareMiddleIso._proof_1
