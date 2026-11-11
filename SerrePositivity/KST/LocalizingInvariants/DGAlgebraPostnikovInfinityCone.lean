module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraQuasiIsoInfinity
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovAlgebraPullback
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeLeg
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.F1BNerveComparisonLimit
public import Mathlib.CategoryTheory.Adjunction.Limits
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.EquivalenceLimits

/-!
概要：元の隣接 Postnikov 拡大の指定錐を、dg 代数の準同型 ∞ 局所化へ送る。
方針：元の厳密な代数 pullback 錐の nerve と、既存の実局所化射を合成する。
規約：同じ頂点・包含・遷移・class を保つ。局所化後の極限性はここでは主張しない。
使われ方：全導来写像空間で検証する Postnikov 錐の固定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra

abbrev PostnikovInfinityShape := AsSmall.{u+1} WalkingCospan

def postnikovInfinityShapeDown : PostnikovInfinityShape.{u} ⥤ WalkingCospan :=
  AsSmall.down

def postnikovInfinityShapeVertex (i : WalkingCospan) : PostnikovInfinityShape.{u} :=
  (AsSmall.up : WalkingCospan ⥤ PostnikovInfinityShape.{u}).obj i

variable (R : Type u) [CommRing R] (B : Mon (Complex R)) [B.X.IsStrictlyLE 0]
  (n : ℤ) (hn : 0 ≤ n)

def postnikovInfinityCospan : PostnikovInfinityShape.{u} ⥤ InfinityPresentation R :=
  (postnikovInfinityShapeDown ⋙ cospan (postnikovPerturbedClass R B n hn)
    (SquareZero.zeroSection (postnikov R B n) (postnikovShiftedLayerBimodule R B n hn 1))) ⋙
      infinityPresentationFunctor R

def postnikovInfinityPresentedCone : Cone (postnikovInfinityCospan R B n hn) :=
  (infinityPresentationFunctor R).mapCone
    ((postnikovAlgebraPullbackCone R B n hn).whisker postnikovInfinityShapeDown)

def postnikovInfinityPresentedCone_isLimit :
    IsLimit (postnikovInfinityPresentedCone R B n hn) := by
  let e₀ : PostnikovInfinityShape.{u} ≌ WalkingCospan := AsSmall.equiv.symm
  let e₁ : Mon (Complex R) ≌ InfinityPresentation R := ULiftHom.equiv
  exact isLimitOfPreserves e₁.functor
    ((postnikovAlgebraPullback_isLimit R B n hn).whiskerEquivalence e₀)

lemma postnikovInfinityNerveCone_isLimit :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCone (postnikovInfinityPresentedCone R B n hn)) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCone_isLimit_iff _).2 ⟨postnikovInfinityPresentedCone_isLimit R B n hn⟩

def postnikovInfinityCone : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone
    (nerveMap (postnikovInfinityCospan R B n hn) ≫ quasiIsoInfinityMap R) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone (quasiIsoInfinityMap R) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCone (postnikovInfinityPresentedCone R B n hn))

lemma postnikovInfinityCone_vertex : (postnikovInfinityCone R B n hn).vertex =
    (quasiIsoInfinityMap R).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex ((infinityPresentationFunctor R).obj (postnikov R B (n + 1)))) := by
  rw [postnikovInfinityCone, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone_vertex, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCone_vertex]
  rfl

lemma postnikovInfinityPresentedCone_left :
    (postnikovInfinityPresentedCone R B n hn).π.app (postnikovInfinityShapeVertex .left) =
      (infinityPresentationFunctor R).map (postnikovPerturbedInclusion R B n hn) := rfl

lemma postnikovInfinityPresentedCone_right :
    (postnikovInfinityPresentedCone R B n hn).π.app (postnikovInfinityShapeVertex .right) =
      (infinityPresentationFunctor R).map
        (postnikovTransition R B (n + 1) n (by omega)) := rfl

lemma postnikovInfinityCone_leg (i : PostnikovInfinityShape.{u}) :
    (postnikovInfinityCone R B n hn).val.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneLegSimplex i) =
      (quasiIsoInfinityMap R).app (Opposite.op ⦋1⦌)
        (ComposableArrows.mk₁ ((postnikovInfinityPresentedCone R B n hn).π.app i)) := by
  change (quasiIsoInfinityMap R).app (Opposite.op ⦋1⦌)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCone (postnikovInfinityPresentedCone R B n hn)).val.app _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneLegSimplex i)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCone_leg]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
