module

public import SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifferenceFactor
public import SerrePositivity.KST.LocalizingInvariants.CofiberZeroTargetDiagrams
public import SerrePositivity.KST.LocalizingInvariants.LaxQuotientShiftLegs

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
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference
variable {C D E Q : StableCategory.{u}} (p : ExactMap C E) (q : ExactMap D E)
  (r : ExactMap (laxCategory p q) Q)

lemma arrow_source : arrow p q r ≫
    evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      ((laxSnd p q).hom ≫ LaxInclusion.fromD p q) ≫ r.hom := by
  rw [arrow, Category.assoc, arrowMap_evaluation, ← Category.assoc, LaxCounit.arrow_source]

lemma connectingArrow_target : connectingArrow p q r ≫
    evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      ((laxSnd p q).hom ≫ LaxInclusion.fromD p q) ≫ r.hom := by
  rw [connectingArrow, Category.assoc, CofiberRotation.inverseRotation_target, arrow_source]

lemma fromC_connectingArrow_zeroTarget (c : C.obj _⦋0⦌) : IsZeroTargetArrow
    ((LaxInclusion.fromC p q ≫ connectingArrow p q r).app (Opposite.op ⦋0⦌) c) := by
  change IsZeroVertex ((LaxInclusion.fromC p q ≫ connectingArrow p q r ≫
    evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2))).app (Opposite.op ⦋0⦌) c)
  rw [connectingArrow_target]
  change IsZeroVertex (r.hom.app _ ((LaxInclusion.fromD p q).app _
    ((laxSnd p q).hom.app _ ((LaxInclusion.fromC p q).app _ c))))
  have hs : (laxSnd p q).hom.app (Opposite.op ⦋0⦌)
      ((LaxInclusion.fromC p q).app (Opposite.op ⦋0⦌) c) =
        (chosenZeroVertex D.obj).vertex := LaxInclusion.fromC_snd_vertex p q c
  rw [hs]
  exact IsExactFunctor.preservesZero (F := r.hom) _
    (IsExactFunctor.preservesZero (F := LaxInclusion.fromD p q) _
      (chosenZeroVertex D.obj).isZero)

def fromCFirstSuspensionIso : FunctorIso
    ((LaxInclusion.fromC p q ≫ first p q r) ≫ SuspensionExact.map Q.obj)
    (LaxInclusion.fromC p q ≫ r.hom) := by
  have es := CofiberFamily.zeroTargetRelativeIso Q.obj
    (LaxInclusion.fromC p q ≫ connectingArrow p q r)
    (fromC_connectingArrow_zeroTarget p q r)
  have he := CofiberRotation.inverseRotationFamilyCofiberIso Q.obj
    (LaxInclusion.fromC p q ≫ arrow p q r)
  simp only [Category.assoc, arrow_target] at he
  have hc : FunctorIso
      (CofiberFamily.cofiber Q.obj (LaxInclusion.fromC p q ≫ connectingArrow p q r))
      (LaxInclusion.fromC p q ≫ r.hom) := by
    simpa only [connectingArrow, Category.assoc] using he
  have hs : FunctorIso
      (CofiberFamily.cofiber Q.obj (LaxInclusion.fromC p q ≫ connectingArrow p q r))
      ((LaxInclusion.fromC p q ≫ first p q r) ≫ SuspensionExact.map Q.obj) := by
    simpa only [first, Category.assoc, lift_fst] using es
  exact hs.symm ≪≫ hc

def fromCFirstIso : FunctorIso (LaxInclusion.fromC p q ≫ first p q r)
    (laxQuotientCLeg p q r).hom := by
  apply ((SuspensionExact.equivalence Q.obj).isQCatEquivalence.postcompose C.obj
    ).isFullyFaithful.preimageVertexIso
  exact fromCFirstSuspensionIso p q r ≪≫ (laxQuotientCLeg_suspensionIso p q r).symm

def firstCLegIso : FunctorIso (first p q r)
    ((laxFst p q).hom ≫ (laxQuotientCLeg p q r).hom) := by
  have e := FunctorIso.precomp (fromCFirstIso p q r) (laxFst p q).hom
  have ef : FunctorIso (first p q r)
      ((laxFst p q).hom ≫ (LaxInclusion.fromC p q ≫ first p q r)) := by
    simpa only [Category.assoc] using firstFactorIso p q r
  exact ef ≪≫ e

end SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference
