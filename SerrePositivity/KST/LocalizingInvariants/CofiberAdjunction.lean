module

public import SerrePositivity.KST.LocalizingInvariants.CofiberRotationAdjunction
public import SerrePositivity.KST.LocalizingInvariants.ArrowTargetAdjunction

/-!
概要：元の選択された cofiber 関手の実右随伴を構成する。
方針：cofiber 回転の随伴と終点評価の随伴を合成する。
規約：元の cofiber 関手を保持。使われ方：Tamme の差の関手の右随伴。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
variable (X : SSet.{u}) [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]

/-- 恒等矢印を逆回転して得る、cofiber の実右随伴。 -/
def cofiberRightAdjoint : X ⟶ (ihom (Δ[1] : SSet.{u})).obj X :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.identityArrow X ≫ CofiberRotation.inverseRotation X

/-- 元の全単体上の cofiber 選択は、この逆回転関手の実左随伴である。 -/
def cofiberAdjunction :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberSquareFamily.cofiber X (𝟙 ((ihom (Δ[1] : SSet.{u})).obj X)))
      (cofiberRightAdjoint X) := by
  have a := (CofiberRotation.adjunction X).comp (ArrowTarget.adjunction X)
  change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction
    ((CofiberDiagrams.lift X (𝟙 _) ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.right X) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
    (cofiberRightAdjoint X) at a
  rw [CofiberDiagrams.lift_right_target] at a
  exact a

end SerrePositivity.KST.LocalizingInvariants
