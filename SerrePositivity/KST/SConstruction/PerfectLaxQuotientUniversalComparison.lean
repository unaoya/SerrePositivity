module
public import SerrePositivity.KST.SConstruction.PerfectLaxQuotientComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalDifferenceSquare

/-! # 完備化後の商と恒等 lax 差を結ぶ全関手同型
概要：完備化後の射を厳密商と仮定せず、包含上の普遍差を恒等対角へ比較する。
方針：元の包含の零化だけで接続矢印の可逆性を示し、全矢印族を恒等族へ送る。
規約：元の完備化後の射と全比較道を保持する。使われ方：LT の二つの実 fiber 列。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories LocalizingInvariants
open scoped Simplicial
namespace PerfectLaxQuotient
variable {C D B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D B}
  (d : PerfectLaxQuotient p q)

/-- 元の完備化後の商に対する普遍差も、同じ包含の全対象を零に送る。 -/
lemma universalDifference_zero (x : d.left.obj _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (((d.inclusion.hom ≫ LaxUniversalDifference.lift p q d.sequence.projection) ≫
      laxDifference (𝟙 d.sequence.right) (𝟙 d.sequence.right)).app (Opposite.op ⦋0⦌) x) := by
  have e := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp
    (LaxUniversalDifference.differenceIso p q d.sequence.projection) d.inclusion.hom
  have hz := (d.sequence.projection_kills_inclusion x).of_vertexIso (e.app x).symm
  simpa only [Category.assoc] using hz

/-- 同じ包含上の接続矢印族は、完備化後の商で可逆な矢印からなる。 -/
lemma universalConnectingArrow_invertible (x : d.left.obj _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex ((d.inclusion.hom ≫
      LaxUniversalDifference.connectingArrow p q d.sequence.projection).app
        (Opposite.op ⦋0⦌) x) := by
  have hi := (laxDifference_zero_iff (𝟙 d.sequence.right) (𝟙 d.sequence.right) _).mp
    (d.universalDifference_zero x)
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex (((d.inclusion.hom ≫
    LaxUniversalDifference.lift p q d.sequence.projection) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackArrow (𝟙 d.sequence.right.obj) (𝟙 d.sequence.right.obj)).app
        (Opposite.op ⦋0⦌) x) at hi
  erw [Category.assoc, LaxUniversalDifference.lift_arrow] at hi
  exact hi

/-- 同じ全接続矢印族と、その始点の恒等矢印族の関手同型。 -/
def universalArrowComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (d.inclusion.hom ≫ LaxUniversalDifference.connectingArrow p q d.sequence.projection)
    ((d.inclusion.hom ≫ LaxUniversalDifference.first p q d.sequence.projection) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap (Δ[1] : SSet.{u}) d.sequence.right.obj) := by
  have e := EquivalenceArrowFamily.comparison
    (d.inclusion.hom ≫ LaxUniversalDifference.connectingArrow p q d.sequence.projection)
    d.universalConnectingArrow_invertible
  have hf := LaxUniversalDifference.lift_fst p q d.sequence.projection
  change LaxUniversalDifference.first p q d.sequence.projection = _ at hf
  erw [hf]
  simpa only [Category.assoc] using e

/-- 元の完備化後の商の普遍差への比較は、包含上で同じ恒等 lax 対角へ移る。 -/
def universalDiagonalIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (d.inclusion.hom ≫ LaxUniversalDifference.lift p q d.sequence.projection)
    ((d.inclusion.hom ≫ LaxUniversalDifference.first p q d.sequence.projection) ≫
      IdentityLax.diagonal d.sequence.right) := by
  have e := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp d.universalArrowComparison (_root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.arrowLaxInverse d.sequence.right.obj)
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (d.inclusion.hom ≫ (LaxUniversalDifference.connectingArrow p q d.sequence.projection ≫
      _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.arrowLaxInverse d.sequence.right.obj))
    ((d.inclusion.hom ≫ LaxUniversalDifference.first p q d.sequence.projection) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap (Δ[1] : SSet.{u}) d.sequence.right.obj ≫
        _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.arrowLaxInverse d.sequence.right.obj))
  simpa only [Category.assoc] using e

/-- 元の全比較道を持つ、二つの合成を比較する実三角形。 -/
def universalDiagonalTriangle : SSet.Edge.CompStruct
    (SSet.Edge.id (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex d.left))
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalDifferenceSquare.inclusionComposite p q d.inclusion d.sequence.projection))
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalDifferenceSquare.diagonalComposite p q d.inclusion d.sequence.projection)) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.exactMapComparisonTriangle
    (F := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalDifferenceSquare.diagonalComposite p q d.inclusion d.sequence.projection)
    (G := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalDifferenceSquare.inclusionComposite p q d.inclusion d.sequence.projection)
    d.universalDiagonalIso.symm

/-- 元の比較三角形を保持する、実 StableInfinity 値の普遍差の比較正方形。 -/
def universalRawSquare : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} :=
  PathComparisonSquare.square
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalDifferenceSquare.lower p q d.inclusion d.sequence.projection)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalDifferenceSquare.upper p q d.inclusion d.sequence.projection)
    d.universalDiagonalTriangle

/-- 元の比較正方形の四辺を、その元の完全関手として回収する。 -/
lemma universalRawSquare_edges :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ d.universalRawSquare =
        SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow d.inclusion).edge ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ d.universalRawSquare = SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (IdentityLax.exactDiagonal d.sequence.right)).edge ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ d.universalRawSquare = SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalDifferenceSquare.kernelMap p q d.inclusion d.sequence.projection)).edge ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ d.universalRawSquare = SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow
          (LaxUniversalDifference.exactLift p q d.sequence.projection)).edge :=
  ⟨PathComparisonSquare.square_bottom _ _ _, PathComparisonSquare.square_top _ _ _,
    PathComparisonSquare.square_left _ _ _, PathComparisonSquare.square_right _ _ _⟩

end PerfectLaxQuotient
end SerrePositivity.KST.SConstruction
