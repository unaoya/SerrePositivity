module
public import SerrePositivity.InfinityCategories.StablePresentable.Exact.ExactArrowMap

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

instance arrowMap_isExact {X Y : SSet.{u}} [Quasicategory X] [IsStable X]
    [Quasicategory Y] [IsStable Y] (F : X ⟶ Y) [IsExactFunctor F] :
    IsExactFunctor ((ihom (Δ[1] : SSet.{u})).map F) := by
  have h₀ : IsExactFunctor ((ihom (Δ[1] : SSet.{u})).map F ≫
      evaluateFunctorAt (Y := Y) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) := by
    rw [_root_.SerrePositivity.InfinityCategories.StablePresentable.Exact.arrowMap_evaluation]
    infer_instance
  have h₁ : IsExactFunctor ((ihom (Δ[1] : SSet.{u})).map F ≫
      evaluateFunctorAt (Y := Y) (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) := by
    rw [_root_.SerrePositivity.InfinityCategories.StablePresentable.Exact.arrowMap_evaluation]
    infer_instance
  exact arrow_exact_of_endpoints Y _

def exactArrowMap {A B : StableCategory.{u}} (F : ExactMap A B) :
    ExactMap (stableArrowCategory A) (stableArrowCategory B) :=
  ⟨(ihom (Δ[1] : SSet.{u})).map F.hom, inferInstance⟩

end SerrePositivity.KST.LocalizingInvariants
