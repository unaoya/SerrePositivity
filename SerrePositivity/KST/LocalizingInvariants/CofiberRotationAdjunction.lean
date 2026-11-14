module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberRotationAdjunction

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
variable (X : SSet.{u}) [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]

/-- 元の cofiber 選択による底辺評価の厳密切断。 -/
def bottomSection : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.arrows X ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.space X := CofiberDiagrams.lift X (𝟙 _)

lemma bottomSection_bottom : bottomSection X ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.bottom X = 𝟙 (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.arrows X) :=
  CofiberDiagrams.lift_bottom X (𝟙 _)

/-- 同じ普遍 cofiber 図式の右辺評価の厳密切断。 -/
def rightSection : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.arrows X ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.space X :=
  Classical.choose (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_exists_section (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.right X))

lemma rightSection_right : rightSection X ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.right X = 𝟙 (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.arrows X) :=
  Classical.choose_spec (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_exists_section (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.right X))

def rotation : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.arrows X ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.arrows X := bottomSection X ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.right X

def inverseRotation : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.arrows X ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.arrows X := rightSection X ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.bottom X

def bottomAdjunction : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction (bottomSection X) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.bottom X) :=
  trivialFibrationSectionLeftAdjunction (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.bottom X) (bottomSection X)
    (bottomSection_bottom X)

def rightAdjunction : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.right X) (rightSection X) :=
  trivialFibrationSectionRightAdjunction (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.right X) (rightSection X)
    (rightSection_right X)

/-- 実際の cofiber 回転と、その逆回転の実随伴。 -/
def adjunction : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction (rotation X) (inverseRotation X) :=
  (bottomAdjunction X).comp (rightAdjunction X)

end SerrePositivity.KST.LocalizingInvariants.CofiberRotation

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "1.1.1.7" (partial := stronger-hyp) "仮定：安定準圏 X（Lean が強い：HA は点付き性のみで射ごとの余ファイバーが存在する場合を含む）。結論：余ファイバー正方形から底辺への射は自明 Kan fibration で切断を持つ。安定な場合の結論と一致し、余ファイバーが一部しかない場合は扱わない。"] _root_.SerrePositivity.KST.LocalizingInvariants.CofiberRotation.bottomSection
