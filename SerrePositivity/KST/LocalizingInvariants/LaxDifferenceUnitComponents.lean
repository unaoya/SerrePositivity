module

public import SerrePositivity.KST.LocalizingInvariants.LaxDifferenceNullComposite

/-!
概要：実 lax pullback 内の単位候補の二成分と、終点の指定矢印族。
方針：C 成分は零値関手への実ホモトピー、D 成分は cofiber 射の元の転置を使う。
規約：両成分の終点は同じ difference≫ρ の実射影。使われ方：四辺を固定した貼り合わせ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
variable {C D E : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D E)
  (v : E.obj ⟶ D.obj)

lemma laxDifferenceUnit_target_snd :
    (laxDifference p q ≫ laxDifferenceRho p q v) ≫ (laxSnd p q).hom =
      laxDifference p q ≫ v := by
  rw [Category.assoc, laxDifferenceRho_snd]

lemma laxDifferenceUnit_target_fst_zero (x : (laxCategory p q).obj _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (((laxDifference p q ≫ laxDifferenceRho p q v) ≫
      (laxFst p q).hom).app (Opposite.op ⦋0⦌) x) := by
  rw [laxDifferenceRho, Category.assoc, Category.assoc, LaxInclusion.fromD_fst]
  change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Lax.zeroC (C := C) (D := D)).app (Opposite.op ⦋0⦌)
    (v.app (Opposite.op ⦋0⦌) ((laxDifference p q).app (Opposite.op ⦋0⦌) x)))
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Lax.zeroC, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroDiagram_const_vertex]
  exact (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.chosenZeroVertex C.obj).isZero

/-- 元の第一射影から、同じ実終点の第一射影への自然な零枝。 -/
def laxDifferenceUnitCHomotopy : SSet.Homotopy (laxFst p q).hom
    ((laxDifference p q ≫ laxDifferenceRho p q v) ≫ (laxFst p q).hom) :=
  ZeroArrowFamily.toZero _ _ (laxDifferenceUnit_target_fst_zero p q v)

/-- 転置された D 成分の代表を保持し、終点を実第二射影へ正規化する。 -/
def laxDifferenceUnitDHomotopy (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction q.hom v) :
    SSet.Homotopy (laxSnd p q).hom
      ((laxDifference p q ≫ laxDifferenceRho p q v) ≫ (laxSnd p q).hom) where
  h := (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy (laxDifferenceUnitD p q a)).h
  h₀ := (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy (laxDifferenceUnitD p q a)).h₀
  h₁ := by
    rw [laxDifferenceUnit_target_snd]
    exact (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy (laxDifferenceUnitD p q a)).h₁
  rel := (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy (laxDifferenceUnitD p q a)).rel

/-- 単位候補の終点における元の指定矢印族。 -/
def laxDifferenceUnitTargetArrowHomotopy : SSet.Homotopy
    (((laxDifference p q ≫ laxDifferenceRho p q v) ≫ (laxFst p q).hom) ≫ p.hom)
    (((laxDifference p q ≫ laxDifferenceRho p q v) ≫ (laxSnd p q).hom) ≫ q.hom) where
  h := (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp (laxArrowHomotopy p q)
    (laxDifference p q ≫ laxDifferenceRho p q v)).h
  h₀ := by
    rw [(_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp (laxArrowHomotopy p q)
      (laxDifference p q ≫ laxDifferenceRho p q v)).h₀]
    rfl
  h₁ := by
    rw [(_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp (laxArrowHomotopy p q)
      (laxDifference p q ≫ laxDifferenceRho p q v)).h₁]
    rfl
  rel := (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp (laxArrowHomotopy p q)
    (laxDifference p q ≫ laxDifferenceRho p q v)).rel

lemma laxDifferenceUnit_target_fst_post_zero (x : (laxCategory p q).obj _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((((laxDifference p q ≫ laxDifferenceRho p q v) ≫
      (laxFst p q).hom) ≫ p.hom).app (Opposite.op ⦋0⦌) x) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero (F := p.hom) _ (laxDifferenceUnit_target_fst_zero p q v x)

end SerrePositivity.KST.LocalizingInvariants
