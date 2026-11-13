module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictSemifreeFunctorCoconeTransport
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictBarNativeProjectiveCocone
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.EquivalenceColimitCones
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitReindex
public import SerrePositivity.InfinityCategories.HTT.InitialAndFinalObjects.InitialBoundaryTransport

/-!
概要：同じ計算済み全余錐族は、各パラメーターで元の余極限性を保つ。
方針：元の射影的余錐を既存同値と形状同型で運び、同じ全族同型の制限で保存する。
規約：余極限対象を別の選択で置き換えない。
使われ方：3b-3 R6 U33、全族を普遍余錐の全部分圏へ入れる入力。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet MonoidalCategory MonoidalClosed CartesianMonoidalCategory
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A]

/-- U33の分割：元の同じ射影的余錐を既存同値と形状同型で運ぶ。 -/
def strictSemifreeRawDACoconeAt (F : StrictSemifreeDiagram A SimplexCategoryᵒᵖ) :=
  (mapJoinCocone (projectivePointEquivalence A).hom
    (strictBarNativeProjectiveCoconeAt A SimplexCategoryᵒᵖ
      (strictSemifreePointUnderlyingFunctor A)
      (strictSemifreePointUnderlyingFunctor_projective A) F)).restrict
    (smallDiagramShapeIso.{u} (nerve SimplexCategoryᵒᵖ)).inv

/-- U33の前提計算：同じ余錐の制限は全族の同じパラメーター評価である。 -/
lemma strictSemifreeRawDACoconeAt_val (F : StrictSemifreeDiagram A SimplexCategoryᵒᵖ) :
    (strictSemifreeRawDACoconeAt A F).val =
      lift (SSet.const (ComposableArrows.mk₀ F))
        (𝟙 (join ((SSet.uliftFunctor.{u + 1, 0}).obj (nerve SimplexCategoryᵒᵖ))
          (Δ[0] : SSet.{u + 1}))) ≫ strictSemifreeReindexedRawDAJoinFamily A := by
  change (strictSemifreeJoinShapeIso A).hom ≫
      (strictBarNativeProjectiveCoconeMapAt A SimplexCategoryᵒᵖ
        (strictSemifreePointUnderlyingFunctor A)
        (strictSemifreePointUnderlyingFunctor_projective A) F ≫
          (projectivePointEquivalence A).hom) = _
  unfold strictBarNativeProjectiveCoconeMapAt strictSemifreeReindexedRawDAJoinFamily
    strictSemifreeRawDAJoinFamily
  simp only [Category.assoc]
  rw [comp_lift_assoc, SSet.comp_const, Category.comp_id, lift_whiskerLeft_assoc,
    Category.id_comp]

/-- 同じraw余錐は元の射影的余錐の余極限性を保つ。 -/
lemma strictSemifreeRawDACoconeAt_isColimit (F : StrictSemifreeDiagram A SimplexCategoryᵒᵖ) :
    IsColimitCone (strictSemifreeRawDACoconeAt A F) := by
  apply (isColimitCone_iff_restrict_of_isIso _
    (smallDiagramShapeIso.{u} (nerve SimplexCategoryᵒᵖ)).inv).mp
  exact (equivalence_isColimitCone_iff (projectivePointEquivalence A).isQCatEquivalence _).mp
    (strictBarNativeProjectiveCoconeAt_isColimit A SimplexCategoryᵒᵖ
      (strictSemifreePointUnderlyingFunctor A)
      (strictSemifreePointUnderlyingFunctor_projective A) F)

/-- U33の包装の分割：計算済み全余錐族の固定パラメーターの射。 -/
def strictSemifreeComputedDACoconeMapAt (F : StrictSemifreeDiagram A SimplexCategoryᵒᵖ) :
    join ((SSet.uliftFunctor.{u + 1, 0}).obj (nerve SimplexCategoryᵒᵖ))
      (Δ[0] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A :=
  lift (SSet.const (ComposableArrows.mk₀ F))
    (𝟙 (join ((SSet.uliftFunctor.{u + 1, 0}).obj (nerve SimplexCategoryᵒᵖ))
      (Δ[0] : SSet.{u + 1}))) ≫ strictSemifreeComputedDAJoinFamily A

/-- U33：同じ全余錐族の固定パラメーターでの余錐。 -/
def strictSemifreeComputedDACoconeAt (F : StrictSemifreeDiagram A SimplexCategoryᵒᵖ) :
    JoinCocone (joinInl ((SSet.uliftFunctor.{u + 1, 0}).obj (nerve SimplexCategoryᵒᵖ))
      (Δ[0] : SSet.{u + 1}) ≫ strictSemifreeComputedDACoconeMapAt A F) :=
  ⟨strictSemifreeComputedDACoconeMapAt A F, rfl⟩

/-- U33の分割：全族の同じ同型を固定パラメーターで評価する。 -/
def strictSemifreeComputedDACoconeAtIso (F : StrictSemifreeDiagram A SimplexCategoryᵒᵖ) :
    FunctorIso (strictSemifreeRawDACoconeAt A F).val
      (strictSemifreeComputedDACoconeAt A F).val := by
  rw [strictSemifreeRawDACoconeAt_val]
  have h := (strictSemifreeComputedDAJoinFamily_transportIso A).precomp
    (lift (SSet.const (ComposableArrows.mk₀ F))
      (𝟙 (join ((SSet.uliftFunctor.{u + 1, 0}).obj (nerve SimplexCategoryᵒᵖ))
        (Δ[0] : SSet.{u + 1}))))
  exact h

/-- U33：計算済みの同じ全余錐族は各パラメーターで余極限を与える。 -/
lemma strictSemifreeComputedDACoconeAt_isColimit
    (F : StrictSemifreeDiagram A SimplexCategoryᵒᵖ) :
    IsColimitCone (strictSemifreeComputedDACoconeAt A F) := by
  apply isColimitCone_of_initialBoundaryLifting_coconeRestriction
  exact SerrePositivity.InfinityCategories.HTT.InitialAndFinalObjects.InitialBoundaryLifting.of_vertexIso
    (coconeRestriction ((SSet.uliftFunctor.{u + 1, 0}).obj (nerve SimplexCategoryᵒᵖ))
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A))
    (strictSemifreeRawDACoconeAt_isColimit A F).initialBoundaryLifting
    (strictSemifreeComputedDACoconeAtIso A F)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
