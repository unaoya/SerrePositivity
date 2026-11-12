module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.GeneralConeComparisonReflection
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.ComparisonFiberFunctor
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.ComparisonFiberBasePoint

/-!
概要：任意の小圏で反転係数の錐の比較の導来 fiber を元の比較の導来 fiber へ直接移す。
方針：edgewise 共通解像の二つの可換正方形で源と標的を順に同値移送する。
規約：fiber 全体の反転を残さず、底の点の逆像の選択と path による移送を含める。
使われ方：HTT 4.2.4.1、Kerodon 7.5.4.6（Tag 03BB）、pinched Hom の元の q_x の fiber 模型。

対応節は Kerodon 7.5（Tag 039Y）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
noncomputable section
variable {I : Type u} [SmallCategory I]

local instance generalFiberReflection_edgewiseKan (H : I ⥤ SSet.{u})
    [∀ i, KanComplex (H.obj i)] : ∀ i, KanComplex ((H ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionFunctor).obj i) :=
  fun i ↦ inferInstanceAs (KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision (H.obj i)))

local instance generalFiberReflection_opKan (H : I ⥤ SSet.{u})
    [∀ i, KanComplex (H.obj i)] : ∀ i, KanComplex ((H ⋙ SSet.opFunctor).obj i) :=
  fun i ↦ inferInstanceAs (KanComplex (H.obj i).op)

local instance generalFiberReflection_holimKan (H : I ⥤ SSet.{u})
    [∀ i, KanComplex (H.obj i)] : KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim H) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim_kanComplex H

local instance generalFiberReflection_opPointKan {H : I ⥤ SSet.{u}} (c : Cone H)
    [KanComplex c.pt] : KanComplex (SSet.opFunctor.mapCone c).pt :=
  inferInstanceAs (KanComplex c.pt.op)

local instance generalFiberReflection_edgewisePointKan {H : I ⥤ SSet.{u}} (c : Cone H)
    [KanComplex c.pt] : KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionFunctor.mapCone c).pt :=
  inferInstanceAs (KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision c.pt))

/-- 概要：反転 end の任意の点に対応する元の非反転 end の点。
方針：edgewise end の左射影の逆で点を回収し、右射影で元の end へ移す。
規約：元の宇宙を保持し、逆の像と元の点のずれは fiber の path 移送で扱う。
使われ方：Kerodon 7.5.4.6（Tag 03BB）、一般形状の元の q_x の導来 fiber の固定点。 -/
def bousfieldKanGeneralReflectedFiberPoint (H : I ⥤ SSet.{u}) [∀ i, KanComplex (H.obj i)]
    (b : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (H ⋙ SSet.opFunctor)) _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim H) _⦋0⦌ :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.diagramEdgewiseRight H)).app _
    ((Classical.choose (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanEdgewiseLeft_homotopyEquivalence H)).app _ b)

/-- 概要：一般の反転係数の比較の導来 fiber は元の比較の導来 fiber と反転なしで同値。
方針：左右の頂点射影の同値で源を移し、左 end 射影の逆と右 end 射影で標的を移す。
規約：添字の形状・錐の極限性・遷移の fibration 性・厳密極限の Kan 性は要求しない。
使われ方：HTT 4.2.4.1、Kerodon 7.5.4.6（Tag 03BB）、任意の錐の pinched Hom の直接模型への移送。 -/
def bousfieldKanConeFiber_generalReflection_equivalence {H : I ⥤ SSet.{u}} (c : Cone H)
    [KanComplex c.pt] [∀ i, KanComplex (H.obj i)]
    (b : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (H ⋙ SSet.opFunctor)) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.comparisonFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison (SSet.opFunctor.mapCone c)) b)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.comparisonFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison c)
        (bousfieldKanGeneralReflectedFiberPoint H b)) := by
  let p := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionFunctor.mapCone c)
  let L := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.diagramEdgewiseLeft H)
  let R := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.diagramEdgewiseRight H)
  have hL := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanEdgewiseLeft_homotopyEquivalence H
  have hR := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanEdgewiseRight_homotopyEquivalence H
  let a := (Classical.choose hL).app (Opposite.op ⦋0⦌) b
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft_trivialKanFibration c.pt
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight_trivialKanFibration c.pt
  have hl₀ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft c.pt)
  have hr₀ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight c.pt)
  have hl := hl₀.isSimplicialHomotopyEquivalence
  have hr := hr₀.isSimplicialHomotopyEquivalence
  let eL := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.comparisonFiberMap_homotopyEquivalence (p ≫ L)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison (SSet.opFunctor.mapCone c)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft c.pt)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison_edgewiseLeft c) hl b).isQCatEquivalence.choose
  let eP := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.comparisonFiberPostInverseEquivalence p L hL b
  let eR := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.comparisonFiberPost_homotopyEquivalence p R hR a).isQCatEquivalence.choose
  let eS := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.comparisonFiberMap_homotopyEquivalence (p ≫ R)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison c) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight c.pt)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison_edgewiseRight c) hr (R.app _ a)).isQCatEquivalence.choose
  exact eL.symm.trans (eP.symm.trans (eR.trans eS))

end
end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
