module
public import SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Exact.ExactArrowMap

public import SerrePositivity.KST.LocalizingInvariants.ArrowStableExact
public import SerrePositivity.KST.LocalizingInvariants.CofiberFamilyZeroTriangle

/-!
概要：完全関手による矢印圏上の後合成も完全で、矢印の零性は両端の零性で判定できる。
方針：評価と後合成の厳密な交換を両端による完全性判定へ渡す。
規約：元の内部 Hom を保持。使われ方：点ごとの分母を安定な核の cofiber 分母に同定する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

instance arrowMap_isExact {X Y : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    [Quasicategory Y] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable Y] (F : X ⟶ Y) [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor F] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor ((ihom (Δ[1] : SSet.{u})).map F) := by
  have h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor ((ihom (Δ[1] : SSet.{u})).map F ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := Y) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) := by
    rw [_root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Exact.arrowMap_evaluation]
    infer_instance
  have h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor ((ihom (Δ[1] : SSet.{u})).map F ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := Y) (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) := by
    rw [_root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Exact.arrowMap_evaluation]
    infer_instance
  exact arrow_exact_of_endpoints Y _

def exactArrowMap {A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (F : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (_root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Exact.stableArrowCategory A) (_root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Exact.stableArrowCategory B) :=
  ⟨(ihom (Δ[1] : SSet.{u})).map F.hom, inferInstance⟩

end SerrePositivity.KST.LocalizingInvariants
