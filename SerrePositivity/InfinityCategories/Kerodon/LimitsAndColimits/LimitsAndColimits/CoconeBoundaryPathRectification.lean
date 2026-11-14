module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.KanExtensions.KanCospanPathRectification
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeMappingShapePushout

/-!
概要：指定した境界の経路の全パラメータ族を保って、coherent な余錐の族を貼り合わせる。
方針：右枝の制限の Kan fibration に経路を持ち上げ、厳密な余錐空間の引き戻しを使う。
規約：経路全体と左枝を保持し、パラメータの Kan 性は不要。使われ方：共通 end の経路の照合。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
noncomputable section
variable {A B C D X T : SSet.{u}} [Quasicategory X]
  {f : A ⟶ B} {g : A ⟶ C} {i : B ⟶ D} {j : C ⟶ D}
  (hp : IsPushout f g i j) [Mono g] (p : D ⟶ X) (y : X _⦋0⦌)
  (b : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (i ≫ p) y) (c : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (j ≫ p) y)
  (h : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (f ≫ (i ≫ p)) y))
  (h₀ : h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint _ 0 = c ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber (j ≫ p) g (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) y)
  (h₁ : h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint _ 1 = b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap (i ≫ p) f y)

/-- 元の右余錐族から、指定した境界経路を厳密に被覆する右余錐空間内の経路族。 -/
def coconeBoundaryPathCorrection : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (j ≫ p) y) := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingShapePushout_right_fibration hp p y
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.cospanRectificationPath
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber (j ≫ p) g (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) y) c h h₀

/-- 右余錐空間内の経路の始点は元の右枝の族そのもの。 -/
lemma coconeBoundaryPathCorrection_zero :
    coconeBoundaryPathCorrection hp p y c h h₀ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint _ 0 = c := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingShapePushout_right_fibration hp p y
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.cospanRectificationPath_zero _ _ _ _

/-- 右余錐空間内の経路は、入力した境界の経路族そのものを被覆する。 -/
lemma coconeBoundaryPathCorrection_projection :
    coconeBoundaryPathCorrection hp p y c h h₀ ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber (j ≫ p) g (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) y) = h := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingShapePushout_right_fibration hp p y
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.cospanRectificationPath_projection _ _ _ _

include h₁ in
/-- 右枝の経路の反対端点は、左余錐族と境界で全単体において一致する。 -/
lemma coconeBoundaryPathCorrection_boundary :
    (coconeBoundaryPathCorrection hp p y c h h₀ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint _ 1) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber (j ≫ p) g (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) y =
      b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap (i ≫ p) f y := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingShapePushout_right_fibration hp p y
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.cospanPathCorrectedRight_boundary _ _ _ _ _ _ h₁

/-- 指定した境界の経路の全パラメータ族を保って貼った、元の図式の固定終点余錐の族。 -/
def coconeBoundaryPathRectifiedFamily : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace p y :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingShapePushout_isPullback hp p y).lift b
    (coconeBoundaryPathCorrection hp p y c h h₀ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint _ 1)
    (coconeBoundaryPathCorrection_boundary hp p y b c h h₀ h₁).symm

/-- 経路を指定した貼り合わせは左余錐の族を厳密に保つ。 -/
lemma coconeBoundaryPathRectifiedFamily_left :
    coconeBoundaryPathRectifiedFamily hp p y b c h h₀ h₁ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap p i y = b :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingShapePushout_isPullback hp p y).lift_fst _ _ _

/-- 貼った余錐族の右枝は、入力した経路を持ち上げた経路の反対端点そのもの。 -/
lemma coconeBoundaryPathRectifiedFamily_right :
    coconeBoundaryPathRectifiedFamily hp p y b c h h₀ h₁ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap p j y =
      coconeBoundaryPathCorrection hp p y c h h₀ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint _ 1 :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingShapePushout_isPullback hp p y).lift_snd _ _ _

/-- パラメータの変更は、指定境界の経路の持ち上げと厳密に可換。 -/
lemma coconeBoundaryPathCorrection_precomp {S : SSet.{u}} (a : S ⟶ T) :
    coconeBoundaryPathCorrection hp p y (a ≫ c) (a ≫ h)
        (by rw [Category.assoc, h₀, Category.assoc]) =
      a ≫ coconeBoundaryPathCorrection hp p y c h h₀ := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingShapePushout_right_fibration hp p y
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanSpecifiedPathLift_precomp _ _ _ _ _ a

/-- 全パラメータを保つ貼り合わせ自体も、パラメータの変更と厳密に可換。 -/
lemma coconeBoundaryPathRectifiedFamily_precomp {S : SSet.{u}} (a : S ⟶ T) :
    coconeBoundaryPathRectifiedFamily hp p y (a ≫ b) (a ≫ c) (a ≫ h)
        (by rw [Category.assoc, h₀, Category.assoc])
        (by rw [Category.assoc, h₁, Category.assoc]) =
      a ≫ coconeBoundaryPathRectifiedFamily hp p y b c h h₀ h₁ := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingShapePushout_isPullback hp p y).hom_ext
  · simp only [coconeBoundaryPathRectifiedFamily_left, Category.assoc]
  · simp only [coconeBoundaryPathRectifiedFamily_right, Category.assoc]
    rw [coconeBoundaryPathCorrection_precomp hp p y c h h₀ a, Category.assoc]

/-- 同じ指定境界経路と元の右枝を持つ修正は、その経路と右枝を保つホモトピーで結べる。 -/
lemma coconeBoundaryPathCorrection_unique_homotopy
    (l : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (j ≫ p) y))
    (hl : l ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber (j ≫ p) g (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) y) = h)
    (hl₀ : l ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint _ 0 = c) :
    ∃ H : SSet.Homotopy (coconeBoundaryPathCorrection hp p y c h h₀) l,
      H.h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap
          (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber (j ≫ p) g (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) y) =
        fst T (Δ[1] : SSet.{u}) ≫ h ∧
      H.h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint _ 0 = fst T (Δ[1] : SSet.{u}) ≫ c := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingShapePushout_right_fibration hp p y
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanSpecifiedPathLift_unique_homotopy _ _ _ _ _ l hl hl₀

end
end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
