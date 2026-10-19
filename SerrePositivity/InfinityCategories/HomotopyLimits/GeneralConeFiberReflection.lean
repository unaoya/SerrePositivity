module

public import SerrePositivity.InfinityCategories.HomotopyLimits.GeneralConeComparisonReflection
public import SerrePositivity.InfinityCategories.HomotopyLimits.ComparisonFiberFunctor
public import SerrePositivity.InfinityCategories.HomotopyLimits.ComparisonFiberBasePoint

/-!
概要：任意の小圏で反転係数の錐の比較の導来 fiber を元の比較の導来 fiber へ直接移す。
方針：edgewise 共通解像の二つの可換正方形で源と標的を順に同値移送する。
規約：fiber 全体の反転を残さず、底の点の逆像の選択と path による移送を含める。
使われ方：HTT 4.2.4.1、Kerodon 7.5.4.6、pinched Hom の元の q_x の fiber 模型。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {I : Type u} [SmallCategory I]

local instance generalFiberReflection_edgewiseKan (H : I ⥤ SSet.{u})
    [∀ i, KanComplex (H.obj i)] : ∀ i, KanComplex ((H ⋙ edgewiseSubdivisionFunctor).obj i) :=
  fun i ↦ inferInstanceAs (KanComplex (edgewiseSubdivision (H.obj i)))

local instance generalFiberReflection_opKan (H : I ⥤ SSet.{u})
    [∀ i, KanComplex (H.obj i)] : ∀ i, KanComplex ((H ⋙ SSet.opFunctor).obj i) :=
  fun i ↦ inferInstanceAs (KanComplex (H.obj i).op)

local instance generalFiberReflection_holimKan (H : I ⥤ SSet.{u})
    [∀ i, KanComplex (H.obj i)] : KanComplex (bousfieldKanHolim H) :=
  bousfieldKanHolim_kanComplex H

local instance generalFiberReflection_opPointKan {H : I ⥤ SSet.{u}} (c : Cone H)
    [KanComplex c.pt] : KanComplex (SSet.opFunctor.mapCone c).pt :=
  inferInstanceAs (KanComplex c.pt.op)

local instance generalFiberReflection_edgewisePointKan {H : I ⥤ SSet.{u}} (c : Cone H)
    [KanComplex c.pt] : KanComplex (edgewiseSubdivisionFunctor.mapCone c).pt :=
  inferInstanceAs (KanComplex (edgewiseSubdivision c.pt))

/-- 概要：反転 end の任意の点に対応する元の非反転 end の点。
方針：edgewise end の左射影の逆で点を回収し、右射影で元の end へ移す。
規約：元の宇宙を保持し、逆の像と元の点のずれは fiber の path 移送で扱う。
使われ方：Kerodon 7.5.4.6、一般形状の元の q_x の導来 fiber の固定点。 -/
def bousfieldKanGeneralReflectedFiberPoint (H : I ⥤ SSet.{u}) [∀ i, KanComplex (H.obj i)]
    (b : (bousfieldKanHolim (H ⋙ SSet.opFunctor)) _⦋0⦌) :
    (bousfieldKanHolim H) _⦋0⦌ :=
  (weightedSectionsMap (bousfieldKanWeight I) (diagramEdgewiseRight H)).app _
    ((Classical.choose (bousfieldKanEdgewiseLeft_homotopyEquivalence H)).app _ b)

/-- 概要：一般の反転係数の比較の導来 fiber は元の比較の導来 fiber と反転なしで同値。
方針：左右の頂点射影の同値で源を移し、左 end 射影の逆と右 end 射影で標的を移す。
規約：添字の形状・錐の極限性・遷移の fibration 性・厳密極限の Kan 性は要求しない。
使われ方：HTT 4.2.4.1、Kerodon 7.5.4.6、任意の錐の pinched Hom の直接模型への移送。 -/
def bousfieldKanConeFiber_generalReflection_equivalence {H : I ⥤ SSet.{u}} (c : Cone H)
    [KanComplex c.pt] [∀ i, KanComplex (H.obj i)]
    (b : (bousfieldKanHolim (H ⋙ SSet.opFunctor)) _⦋0⦌) :
    QCatEquivalence (comparisonFiber (bousfieldKanConeComparison (SSet.opFunctor.mapCone c)) b)
      (comparisonFiber (bousfieldKanConeComparison c)
        (bousfieldKanGeneralReflectedFiberPoint H b)) := by
  let p := bousfieldKanConeComparison (edgewiseSubdivisionFunctor.mapCone c)
  let L := weightedSectionsMap (bousfieldKanWeight I) (diagramEdgewiseLeft H)
  let R := weightedSectionsMap (bousfieldKanWeight I) (diagramEdgewiseRight H)
  have hL := bousfieldKanEdgewiseLeft_homotopyEquivalence H
  have hR := bousfieldKanEdgewiseRight_homotopyEquivalence H
  let a := (Classical.choose hL).app (Opposite.op ⦋0⦌) b
  have := edgewiseLeft_trivialKanFibration c.pt
  have := edgewiseRight_trivialKanFibration c.pt
  have hl₀ := isQCatEquivalence_of_trivialKanFibration (edgewiseLeft c.pt)
  have hr₀ := isQCatEquivalence_of_trivialKanFibration (edgewiseRight c.pt)
  have hl := hl₀.isSimplicialHomotopyEquivalence
  have hr := hr₀.isSimplicialHomotopyEquivalence
  let eL := (comparisonFiberMap_homotopyEquivalence (p ≫ L)
    (bousfieldKanConeComparison (SSet.opFunctor.mapCone c)) (edgewiseLeft c.pt)
    (bousfieldKanConeComparison_edgewiseLeft c) hl b).isQCatEquivalence.choose
  let eP := comparisonFiberPostInverseEquivalence p L hL b
  let eR := (comparisonFiberPost_homotopyEquivalence p R hR a).isQCatEquivalence.choose
  let eS := (comparisonFiberMap_homotopyEquivalence (p ≫ R)
    (bousfieldKanConeComparison c) (edgewiseRight c.pt)
    (bousfieldKanConeComparison_edgewiseRight c) hr (R.app _ a)).isQCatEquivalence.choose
  exact eL.symm.trans (eP.symm.trans (eR.trans eS))

end
end SerrePositivity.InfinityCategories.HomotopyLimits
