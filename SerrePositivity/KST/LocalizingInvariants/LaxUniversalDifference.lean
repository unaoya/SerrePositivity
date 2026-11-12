module

public import SerrePositivity.KST.LocalizingInvariants.CofiberInverseRotationExact
public import SerrePositivity.KST.LocalizingInvariants.LaxCounitCofiber
public import SerrePositivity.KST.LocalizingInvariants.ExactArrowMap
public import SerrePositivity.KST.LocalizingInvariants.LaxDifferenceExact

/-!
概要：一般商の元の関手を、恒等二関手の lax 差へ移す完全関手。
方針：D 余単位の像を逆 cofiber 回転して恒等 lax 圏へ入れ、その cofiber を元の r に比較。
規約：r と Q は元の入力を保持する。使われ方：実 fiber 列を普遍の恒等差へ比較する。
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
variable {C D E Q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D E)
  (r : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (laxCategory p q) Q)

def arrow : (laxCategory p q).obj ⟶ (ihom (Δ[1] : SSet.{u})).obj Q.obj :=
  LaxCounit.arrow p q ≫ (ihom (Δ[1] : SSet.{u})).map r.hom

instance arrow_isExact : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (arrow p q r) := by
  unfold arrow
  infer_instance

lemma arrow_target : arrow p q r ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = r.hom := by
  rw [arrow, Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Exact.arrowMap_evaluation, ← Category.assoc,
    LaxCounit.arrow_target, Category.id_comp]

def connectingArrow : (laxCategory p q).obj ⟶ (ihom (Δ[1] : SSet.{u})).obj Q.obj :=
  arrow p q r ≫ CofiberRotation.inverseRotation Q.obj

instance connectingArrow_isExact : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (connectingArrow p q r) := by
  unfold connectingArrow
  infer_instance

def lift : (laxCategory p q).obj ⟶ (laxCategory (𝟙 Q) (𝟙 Q)).obj :=
  connectingArrow p q r ≫ _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.arrowLaxInverse Q.obj

instance lift_isExact : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (lift p q r) := by
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.arrowLaxInverse Q.obj) :=
    inferInstanceAs (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.arrowLaxIso Q.obj).inv)
  unfold lift
  infer_instance

def exactLift : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (laxCategory p q) (laxCategory (𝟙 Q) (𝟙 Q)) :=
  ⟨lift p q r, inferInstance⟩

lemma lift_snd : lift p q r ≫ (laxSnd (𝟙 Q) (𝟙 Q)).hom =
    ((laxSnd p q).hom ≫ LaxInclusion.fromD p q) ≫ r.hom := by
  change lift p q r ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackSnd (𝟙 Q.obj) (𝟙 Q.obj) = _
  rw [lift, Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.arrowLaxInverse_snd, connectingArrow, Category.assoc,
    CofiberRotation.inverseRotation_target, arrow, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Exact.arrowMap_evaluation, ← Category.assoc, LaxCounit.arrow_source]

lemma lift_arrow : lift p q r ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackArrow (𝟙 Q.obj) (𝟙 Q.obj) =
    connectingArrow p q r := by
  rw [lift, Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.arrowLaxInverse_arrow, Category.comp_id]

def differenceIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (lift p q r ≫ laxDifference (𝟙 Q) (𝟙 Q)) r.hom := by
  have e := CofiberFamily.precompositionIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackArrow (𝟙 Q.obj) (𝟙 Q.obj))
    (lift p q r)
  rw [lift_arrow] at e
  have h := CofiberRotation.inverseRotationFamilyCofiberIso Q.obj (arrow p q r)
  rw [arrow_target] at h
  exact e ≪≫ h

end SerrePositivity.KST.LocalizingInvariants.LaxUniversalDifference
