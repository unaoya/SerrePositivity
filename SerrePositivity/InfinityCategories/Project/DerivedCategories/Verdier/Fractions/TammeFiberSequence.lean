module


public meta import SerrePositivity.Util.Citation
public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.KST.LocalizingInvariants.LaxDifferenceAdjunction
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.TammeSplitting
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions
open _root_.SerrePositivity.KST.LocalizingInvariants
open _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant
variable {Φ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} ⟶ Sp.{u}} (hΦ : IsLocalizingInvariant Φ)
  {C D E : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D E)
  (v : E.obj ⟶ D.obj) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction q.hom v) (hv : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful v)

/-- 元の通常 pullback・lax pullback・差の項の値を結ぶ零角付き実四角形。 -/
def tammeFiberTriangle : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle Sp.{u} :=
  hΦ.abstractFiberTriangle (tammeVerdierSequence p q v a hv)

lemma tammeFiberTriangle_isFiber : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsFiberSequence ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.tammeFiberTriangle hΦ) p q v a hv) :=
  hΦ.abstractFiberTriangle_isFiber (tammeVerdierSequence p q v a hv)

lemma tammeFiberTriangle_bottom :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.tammeFiberTriangle hΦ) p q v a hv).square =
      SSet.yonedaEquiv.symm (Φ.app (Opposite.op ⦋1⦌)
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (pullbackInclusion p q)).edge) :=
  hΦ.abstractFiberTriangle_bottom (tammeVerdierSequence p q v a hv)

lemma tammeFiberTriangle_right :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.tammeFiberTriangle hΦ) p q v a hv).square =
      SSet.yonedaEquiv.symm (Φ.app (Opposite.op ⦋1⦌)
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (exactLaxDifference p q)).edge) :=
  hΦ.abstractFiberTriangle_right (tammeVerdierSequence p q v a hv)

/-- 実 fiber 列の中項から、元の C,D の値の実 ∞ 積への比較同型。 -/
def tammeFiberMiddleIso : SpectrumHo.obj (value Φ (laxCategory p q)) ≅
    SpectrumHo.obj (Binary.obj (value Φ C) (value Φ D)) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.tammeSplitEquivalence hΦ) p q

/-- fiber 四角形の実中頂点を、元の二つの値の実 ∞ 積へ同定する。 -/
def tammeFiberSquareMiddleIso : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoVertex ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.tammeFiberTriangle hΦ) p q v a hv).square 1 0 ≅
    SpectrumHo.obj (Binary.obj (value Φ C) (value Φ D)) :=
  hΦ.fiberMiddleIso (tammeVerdierSequence p q v a hv) ≪≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.tammeFiberMiddleIso hΦ) p q

/-- 二因子の積から差の項の値への射。元の差の像との比較を保持する。 -/
def tammeDifferenceHom : SpectrumHo.obj (Binary.obj (value Φ C) (value Φ D)) ⟶
    SpectrumHo.obj (value Φ E) :=
  ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.tammeSplitComparison hΦ) p q).hom ≫ SpectrumHo.hom (valueMap Φ (exactLaxDifference p q))

lemma tammeFiberSquareMiddleIso_right :
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.tammeFiberSquareMiddleIso hΦ) p q v a hv).hom ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.tammeDifferenceHom hΦ) p q =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoRight ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.tammeFiberTriangle hΦ) p q v a hv).square ≫
        (hΦ.fiberRightIso (tammeVerdierSequence p q v a hv)).hom := by
  change ((hΦ.fiberMiddleIso (tammeVerdierSequence p q v a hv)).hom ≫
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.tammeSplitComparison hΦ) p q).inv) ≫ (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.tammeSplitComparison hΦ) p q).hom ≫ _) = _
  rw [Category.assoc, Iso.inv_hom_id_assoc]
  exact hΦ.fiber_right_naturality (tammeVerdierSequence p q v a hv)

lemma tammeDifferenceHom_C : SpectrumHo.hom (Binary.inl (value Φ C) (value Φ D)) ≫
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.tammeDifferenceHom hΦ) p q = SpectrumHo.hom (valueMap Φ (LaxInclusion.exactFromC p q)) ≫
      SpectrumHo.hom (valueMap Φ (exactLaxDifference p q)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.tammeDifferenceHom, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.tammeSplitComparison_C]

lemma tammeDifferenceHom_D : SpectrumHo.hom (Binary.inr (value Φ C) (value Φ D)) ≫
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.tammeDifferenceHom hΦ) p q = SpectrumHo.hom (valueMap Φ (LaxInclusion.exactFromD p q)) ≫
      SpectrumHo.hom (valueMap Φ (exactLaxDifference p q)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.tammeDifferenceHom, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.tammeSplitComparison_D]

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
      ∃ z : valueHomotopyGroup Φ E (j + 1), (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.tammeConnecting hΦ) p q v a hv j z = x :=
  hΦ.exact_left (tammeVerdierSequence p q v a hv) j x

lemma tamme_exact_right (j : ℤ) (x : valueHomotopyGroup Φ E (j + 1)) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.tammeConnecting hΦ) p q v a hv j x = 1 ↔
      ∃ z : valueHomotopyGroup Φ (laxCategory p q) (j + 1),
        valueHomotopyMap Φ (exactLaxDifference p q) (j + 1) z = x :=
  hΦ.exact_right (tammeVerdierSequence p q v a hv) j x

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

















/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite Tamme "Eq (13)" (partial := stronger-hyp) "仮定：小安定圏自体の引き戻しと右脚の充満忠実な右随伴、Sp 値の局所化型不変量（Lean が強い：Ind 上の右随伴に加え小圏上で与える）。結論：引き戻しの値から lax 引き戻しの値を経て余ファイバー先の値に至るファイバー列（原典と同じ射）。"] _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.tammeFiberTriangle_bottom
attribute [cite Tamme "Eq (13)" (partial := stronger-hyp) "仮定：小安定圏自体の引き戻しと右脚の充満忠実な右随伴、Sp 値の局所化型不変量（Lean が強い：Ind 上の右随伴に加え小圏上で与える）。結論：引き戻しの値から lax 引き戻しの値を経て余ファイバー先の値に至るファイバー列（原典と同じ射）。"] _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.tammeFiberTriangle_isFiber
attribute [cite Tamme "Eq (13)" (partial := stronger-hyp) "仮定：小安定圏自体の引き戻しと右脚の充満忠実な右随伴、Sp 値の局所化型不変量（Lean が強い：Ind 上の右随伴に加え小圏上で与える）。結論：引き戻しの値から lax 引き戻しの値を経て余ファイバー先の値に至るファイバー列（原典と同じ射）。"] _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.tammeFiberTriangle_right
