module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.KanSpecifiedPathLift

/-!
概要：Kan 値 cospan の二枝を、指定した共通部分の経路全体を保って厳密に一致させる。
方針：右枝の fibration に経路を指定始点から持ち上げ、その反対端点を新しい右枝とする。
規約：パラメータ空間は任意。使われ方：余錐空間の経路データを失わない貼り合わせ。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {L M R T : SSet.{u}} [KanComplex M] [KanComplex R]
  (f : L ⟶ M) (g : R ⟶ M) [Fibration g]
  (b : T ⟶ L) (c : T ⟶ R) (h : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath M)
  (h₀ : h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint M 0 = c ≫ g)
  (h₁ : h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint M 1 = b ≫ f)

/-- 指定した共通部分の経路族を、そのまま右枝へ持ち上げた経路。 -/
def cospanRectificationPath : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath R := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanSpecifiedPathLift g 0 c h h₀

/-- 持ち上げた右枝の経路の始点は、元の右枝の族。 -/
lemma cospanRectificationPath_zero :
    cospanRectificationPath g c h h₀ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint R 0 = c :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanSpecifiedPathLift_endpoint g 0 c h h₀

/-- 持ち上げた右枝の経路は、指定した共通部分の経路そのものを被覆。 -/
lemma cospanRectificationPath_projection :
    cospanRectificationPath g c h h₀ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap g = h :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanSpecifiedPathLift_projection g 0 c h h₀

/-- 指定経路に沿って修正した右枝の族。 -/
def cospanPathCorrectedRight : T ⟶ R :=
  cospanRectificationPath g c h h₀ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint R 1

include h₁ in
/-- 修正後の右枝は、左枝と共通部分の全単体で厳密に一致。 -/
lemma cospanPathCorrectedRight_boundary :
    cospanPathCorrectedRight g c h h₀ ≫ g = b ≫ f := by
  rw [cospanPathCorrectedRight]
  exact (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanSpecifiedPathLift_other_endpoint g 0 c h h₀).trans h₁

/-- 指定経路で修正した二枝を、実際の厳密な引き戻しへ貼る。 -/
def cospanPathRectifiedLift : T ⟶ pullback f g :=
  pullback.lift b (cospanPathCorrectedRight g c h h₀)
    (cospanPathCorrectedRight_boundary f g b c h h₀ h₁).symm

/-- 経路を保つ貼り合わせは、左枝の族を厳密に保つ。 -/
lemma cospanPathRectifiedLift_left :
    cospanPathRectifiedLift f g b c h h₀ h₁ ≫ pullback.fst f g = b :=
  pullback.lift_fst _ _ _

/-- 経路を保つ貼り合わせの右枝は、指定経路による修正そのもの。 -/
lemma cospanPathRectifiedLift_right :
    cospanPathRectifiedLift f g b c h h₀ h₁ ≫ pullback.snd f g =
      cospanPathCorrectedRight g c h h₀ := pullback.lift_snd _ _ _

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
