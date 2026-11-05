module
public import SerrePositivity.InfinityCategories.Stable.Exact.CofiberRotationAdjunction

public import SerrePositivity.KST.LocalizingInvariants.CofiberRotationExact
public import SerrePositivity.KST.LocalizingInvariants.TrivialFibrationSectionAdjunction

/-!
概要：元の cofiber 回転関手と、元の右辺を持ち上げて底辺へ戻す関手の実随伴。
方針：底辺切断の左随伴性と右辺切断の右随伴性を合成する。
規約：元の選択された cofiber 族を保持。使われ方：Cone の実右随伴の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.CofiberRotation
variable (X : SSet.{u}) [Quasicategory X] [IsStable X]

/-- 元の cofiber 選択による底辺評価の厳密切断。 -/
def bottomSection : _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberRotation.arrows X ⟶ _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.space X := CofiberDiagrams.lift X (𝟙 _)

lemma bottomSection_bottom : bottomSection X ≫ _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.bottom X = 𝟙 (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberRotation.arrows X) :=
  CofiberDiagrams.lift_bottom X (𝟙 _)

/-- 同じ普遍 cofiber 図式の右辺評価の厳密切断。 -/
def rightSection : _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberRotation.arrows X ⟶ _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.space X :=
  Classical.choose (trivialKanFibration_exists_section (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.right X))

lemma rightSection_right : rightSection X ≫ _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.right X = 𝟙 (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberRotation.arrows X) :=
  Classical.choose_spec (trivialKanFibration_exists_section (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.right X))

def rotation : _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberRotation.arrows X ⟶ _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberRotation.arrows X := bottomSection X ≫ _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.right X

def inverseRotation : _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberRotation.arrows X ⟶ _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberRotation.arrows X := rightSection X ≫ _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.bottom X

def bottomAdjunction : QCatAdjunction (bottomSection X) (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.bottom X) :=
  trivialFibrationSectionLeftAdjunction (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.bottom X) (bottomSection X)
    (bottomSection_bottom X)

def rightAdjunction : QCatAdjunction (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.right X) (rightSection X) :=
  trivialFibrationSectionRightAdjunction (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.right X) (rightSection X)
    (rightSection_right X)

/-- 実際の cofiber 回転と、その逆回転の実随伴。 -/
def adjunction : QCatAdjunction (rotation X) (inverseRotation X) :=
  (bottomAdjunction X).comp (rightAdjunction X)

end SerrePositivity.KST.LocalizingInvariants.CofiberRotation
