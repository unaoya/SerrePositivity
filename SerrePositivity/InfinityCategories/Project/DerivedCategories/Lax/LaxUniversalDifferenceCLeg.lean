module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberRotationAdjunction
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.SuspensionExactFunctor
public import SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Exact.ExactArrowMap
public import SerrePositivity.KST.LocalizingInvariants.CofiberRotationAdjunction
public import SerrePositivity.KST.LocalizingInvariants.CofiberRotationExact
public import SerrePositivity.KST.LocalizingInvariants.CofiberZeroTargetDiagrams
public import SerrePositivity.KST.LocalizingInvariants.LaxInclusions
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxQuotientShiftLegs
public import SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifferenceFactor

/-!
概要：普遍の恒等 lax 差への比較の第一射影を、一般商の元の C 脚に同定する。
方針：C 上の逆回転は零終点矢印なので、その cofiber を suspension 全図式で比較する。
規約：元の C 射影と逆 shift を保持。使われ方：二つの Verdier 列の自然な比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference
end SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax
open _root_.SerrePositivity.KST.LocalizingInvariants
open _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference
variable {C D E Q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D E)
  (r : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (laxCategory p q) Q)

lemma arrow_source : arrow p q r ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      ((laxSnd p q).hom ≫ LaxInclusion.fromD p q) ≫ r.hom := by
  rw [arrow, Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Exact.arrowMap_evaluation, ← Category.assoc, LaxCounit.arrow_source]

lemma connectingArrow_target : connectingArrow p q r ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      ((laxSnd p q).hom ≫ LaxInclusion.fromD p q) ≫ r.hom := by
  rw [connectingArrow, Category.assoc, CofiberRotation.inverseRotation_target, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.arrow_source]

lemma fromC_connectingArrow_zeroTarget (c : C.obj _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroTargetArrow
    ((LaxInclusion.fromC p q ≫ connectingArrow p q r).app (Opposite.op ⦋0⦌) c) := by
  change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((LaxInclusion.fromC p q ≫ connectingArrow p q r ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2))).app (Opposite.op ⦋0⦌) c)
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.connectingArrow_target]
  change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (r.hom.app _ ((LaxInclusion.fromD p q).app _
    ((laxSnd p q).hom.app _ ((LaxInclusion.fromC p q).app _ c))))
  have hs : (laxSnd p q).hom.app (Opposite.op ⦋0⦌)
      ((LaxInclusion.fromC p q).app (Opposite.op ⦋0⦌) c) =
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.chosenZeroVertex D.obj).vertex := LaxInclusion.fromC_snd_vertex p q c
  rw [hs]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero (F := r.hom) _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero (F := LaxInclusion.fromD p q) _
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.chosenZeroVertex D.obj).isZero)

def fromCFirstSuspensionIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    ((LaxInclusion.fromC p q ≫ first p q r) ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.map Q.obj)
    (LaxInclusion.fromC p q ≫ r.hom) := by
  have es := CofiberFamily.zeroTargetRelativeIso Q.obj
    (LaxInclusion.fromC p q ≫ connectingArrow p q r)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.fromC_connectingArrow_zeroTarget p q r)
  have he := CofiberRotation.inverseRotationFamilyCofiberIso Q.obj
    (LaxInclusion.fromC p q ≫ arrow p q r)
  simp only [Category.assoc, arrow_target] at he
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberSquareFamily.cofiber Q.obj (LaxInclusion.fromC p q ≫ connectingArrow p q r))
      (LaxInclusion.fromC p q ≫ r.hom) := by
    simpa only [connectingArrow, Category.assoc] using he
  have hs : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberSquareFamily.cofiber Q.obj (LaxInclusion.fromC p q ≫ connectingArrow p q r))
      ((LaxInclusion.fromC p q ≫ first p q r) ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.map Q.obj) := by
    simpa only [first, Category.assoc, lift_fst] using es
  exact hs.symm ≪≫ hc

def fromCFirstIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (LaxInclusion.fromC p q ≫ first p q r)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientCLeg p q r).hom := by
  apply ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.SuspensionExactDiagrams.equivalence Q.obj).isQCatEquivalence.postcompose C.obj
    ).isFullyFaithful.preimageVertexIso
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.fromCFirstSuspensionIso p q r ≪≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientCLeg_suspensionIso p q r).symm

def firstCLegIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (first p q r)
    ((laxFst p q).hom ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientCLeg p q r).hom) := by
  have e := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.fromCFirstIso p q r) (laxFst p q).hom
  have ef : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (first p q r)
      ((laxFst p q).hom ≫ (LaxInclusion.fromC p q ≫ first p q r)) := by
    simpa only [Category.assoc] using firstFactorIso p q r
  exact ef ≪≫ e

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference.arrow_source := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.arrow_source

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference.connectingArrow_target := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.connectingArrow_target

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.firstCLegIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference.firstCLegIso := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.firstCLegIso

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.fromCFirstIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference.fromCFirstIso := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.fromCFirstIso

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.fromCFirstSuspensionIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference.fromCFirstSuspensionIso := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.fromCFirstSuspensionIso

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference.fromC_connectingArrow_zeroTarget := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.fromC_connectingArrow_zeroTarget

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference.firstCLegIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.firstCLegIso._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference.fromCFirstIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.fromCFirstIso._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference.fromCFirstIso._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.fromCFirstIso._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference.fromCFirstSuspensionIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.fromCFirstSuspensionIso._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference.fromCFirstSuspensionIso._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.fromCFirstSuspensionIso._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference.fromCFirstSuspensionIso._proof_3 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.fromCFirstSuspensionIso._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference.fromCFirstSuspensionIso._proof_4 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.fromCFirstSuspensionIso._proof_4
