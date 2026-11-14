module
public import SerrePositivity.KST.NonConnective.DGKappaSuspensionDescent
public import SerrePositivity.KST.NonConnective.DGKappaConePerfectChoiceComparison

/-!
概要：実 cone／perfect 包含の選択比較を、元の実平坦懸垂間の完全関手へ下降する。
方針：包含四角形の指定同型で零化を証明し、同じ Verdier 普遍性へ代入する。
規約：現行 I・P・固定 κ を保持する。厳密 dg 射や反復列の比較は別工程。
使われ方：K-7 d4・e の実商の模型選択比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {κ : Cardinal.{u}} (I J : DGKappaConeInput R D κ)
  (P : DGKappaPerfectInput R D I) (Q : DGKappaPerfectInput R D J)
local instance choiceConeStable (L : DGKappaConeInput R D κ) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (DGKappaCone R D L)) := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Pretriangulated.dgNerve_isStable_of_pretriangulated R _
local instance choiceKernelStable (L : DGKappaConeInput R D κ) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableClosureNerve R (DGKappaCone R D L) (dgKappaConePerfectObjects R D L)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableClosureNerve_isStable R _ _
local instance choiceSuspensionStable (L : DGKappaConeInput R D κ) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable (dgKappaSuspensionInfinity R D L) := dgKappaSuspensionInfinity_isStable R D L

/-- 同じ選択比較を、標的の元の実平坦商射へ続けた全関手。 -/
def dgKappaSuspensionChoiceSource :=
  (dgKappaConeChoiceEquivalence R D I J).hom ≫ dgKappaSuspensionProjection R D J

theorem dgKappaSuspensionChoiceSource_isExact :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (dgKappaSuspensionChoiceSource R D I J) := by
  let : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (dgKappaConeChoiceEquivalence R D I J).hom :=
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence (dgKappaConeChoiceEquivalence R D I J).isQCatEquivalence
  let : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (dgKappaSuspensionProjection R D J) :=
    (dgKappaSuspension_isStableVerdierSequence R D J).quotientExact
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.isExactFunctor_comp _ _

include P Q in
/-- 同じ包含四角形で比較した全関手は、元の指定 perfect 閉包を実際に零化する。 -/
theorem dgKappaSuspensionChoiceSource_kills :
    ∀ x ∈ Set.range ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableClosureInclusion R (DGKappaCone R D I)
      (dgKappaConePerfectObjects R D I)).app (Opposite.op ⦋0⦌)),
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((dgKappaSuspensionChoiceSource R D I J).app (Opposite.op ⦋0⦌) x) := by
  rintro _ ⟨z, rfl⟩
  have e := ((dgKappaConePerfectChoiceInclusionIso R D I J P Q).postcomp
    (dgKappaSuspensionProjection R D J)).app z
  have hz := (dgKappaSuspension_isStableVerdierSequence R D J).kills
    ((dgKappaConePerfectChoiceEquivalence R D I J P Q).hom.app (Opposite.op ⦋0⦌) z)
  exact hz.of_vertexIso e.symm

/-- 元の実平坦懸垂間に下降した、同じ模型選択比較の完全関手。 -/
def dgKappaSuspensionChoiceMap :
    dgKappaSuspensionInfinity R D I ⟶ dgKappaSuspensionInfinity R D J :=
  dgKappaSuspensionDesc R D I (dgKappaSuspensionInfinity R D J)
    (dgKappaSuspensionChoiceSource R D I J) (dgKappaSuspensionChoiceSource_isExact R D I J)
    (dgKappaSuspensionChoiceSource_kills R D I J P Q)

theorem dgKappaSuspensionChoiceMap_isExact :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (dgKappaSuspensionChoiceMap R D I J P Q) :=
  dgKappaSuspensionDesc_isExact R D I _ _ _ _

/-- 元の実商射との比較は、同じ全零化完全関手圏の余単位から回収する。 -/
def dgKappaSuspensionChoiceMap_facIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (dgKappaSuspensionProjection R D I ≫ dgKappaSuspensionChoiceMap R D I J P Q)
      ((dgKappaConeChoiceEquivalence R D I J).hom ≫ dgKappaSuspensionProjection R D J) :=
  dgKappaSuspensionDesc_facIso R D I _ _ _ _

end SerrePositivity.KST.NonConnective
