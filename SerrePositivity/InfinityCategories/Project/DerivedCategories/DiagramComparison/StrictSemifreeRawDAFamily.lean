module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictBarNativeProjectiveFamily
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictSemifreePointUnderlyingFunctor
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.SpecifiedProjectiveCocone

/-!
概要：同じ全native余錐族を既存D(A)へ送り、二重ULiftのjoinを指定形状へ運ぶ。
方針：既存の射影的一点模型の同値とsmallDiagramShapeIsoをそのまま使う。
規約：二つの添字を定義的に同一視しない。
使われ方：3b-3 R6 U29〜U30、全余錐族の下方図式の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet MonoidalCategory
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A]

/-- U29：同じ全射影的native余錐族を、既存の一点模型の同値でD(A)へ送る。 -/
def strictSemifreeRawDAJoinFamily :
    nerve (StrictSemifreeDiagram A SimplexCategoryᵒᵖ) ⊗
      join ((SSet.uliftFunctor.{u + 1, u}).obj
        ((SSet.uliftFunctor.{u, 0}).obj (nerve SimplexCategoryᵒᵖ)))
        (Δ[0] : SSet.{u + 1}) ⟶ derivedInfinityCategory A :=
  strictBarNativeProjectiveJoinFamily A SimplexCategoryᵒᵖ
    (strictSemifreePointUnderlyingFunctor A)
    (strictSemifreePointUnderlyingFunctor_projective A) ≫ (projectivePointEquivalence A).hom

/-- U30：同じsmallDiagramShapeIsoの逆から作る、指定joinの同型。 -/
def strictSemifreeJoinShapeIso (_A : Type u) :
    join ((SSet.uliftFunctor.{u + 1, 0}).obj (nerve SimplexCategoryᵒᵖ))
        (Δ[0] : SSet.{u + 1}) ≅
      join ((SSet.uliftFunctor.{u + 1, u}).obj
        ((SSet.uliftFunctor.{u, 0}).obj (nerve SimplexCategoryᵒᵖ)))
        (Δ[0] : SSet.{u + 1}) :=
  joinIso (smallDiagramShapeIso.{u} (nerve SimplexCategoryᵒᵖ)).symm (Iso.refl _)

/-- U30の単位の法則：前面は同じsmallDiagramShapeIsoの逆に沿う。 -/
lemma strictSemifreeJoinShapeIso_inl :
    joinInl ((SSet.uliftFunctor.{u + 1, 0}).obj (nerve SimplexCategoryᵒᵖ)) Δ[0] ≫
        (strictSemifreeJoinShapeIso A).hom =
      (smallDiagramShapeIso.{u} (nerve SimplexCategoryᵒᵖ)).inv ≫
        joinInl ((SSet.uliftFunctor.{u + 1, u}).obj
          ((SSet.uliftFunctor.{u, 0}).obj (nerve SimplexCategoryᵒᵖ))) Δ[0] := by
  exact joinInl_joinMap _ _

/-- U30の単位の法則：同じ右端のapexは恒等写像で保つ。 -/
lemma strictSemifreeJoinShapeIso_inr :
    joinInr ((SSet.uliftFunctor.{u + 1, 0}).obj (nerve SimplexCategoryᵒᵖ)) Δ[0] ≫
        (strictSemifreeJoinShapeIso A).hom =
      joinInr ((SSet.uliftFunctor.{u + 1, u}).obj
        ((SSet.uliftFunctor.{u, 0}).obj (nerve SimplexCategoryᵒᵖ))) Δ[0] := by
  change _ ≫ joinMap _ (𝟙 _) = _
  rw [joinInr_joinMap, Category.id_comp]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
