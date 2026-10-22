module

public import SerrePositivity.InfinityCategories.F2.Ind.WeightedTotalBoundedEvaluation
public import SerrePositivity.InfinityCategories.F2.Ind.WeightedTopPrismCocone

/-!
概要：一つの下区間上の元の weighted 図式を、元の全空間余極限上で一段へ輸送する。
方針：最大添字への全円柱を元の底へ戻し、同じ余錐の自然性で値の固定を証明する。
規約：両端と全空間余極限への射を厳密に保持。使われ方：全比較の coslice 図式の収縮。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {C : SSet.{u}} {I : Type u} [PartialOrder I] (F : I ⥤ RightFibrationObject C)
  (i : I) {K : SSet.{u}}
  (q : K ⟶ weightedNerve (sublevelInclusion i ⋙ rightFibrationTotalDiagram F))

/-- 同じ下区間上の図式を上界での係数へ輸送する元の全円柱。 -/
def weightedBoundedPrism : (Δ[1] : SSet.{u}) ⊗ K ⟶ weightedNerve (rightFibrationTotalDiagram F) :=
  (Δ[1] ◁ q) ≫ weightedTopPrism (sublevelInclusion i ⋙ rightFibrationTotalDiagram F) ≫
    weightedNerveBaseMap (sublevelInclusion i) (rightFibrationTotalDiagram F)

/-- 円柱の始端は同じ下区間上の元の図式。 -/
lemma weightedBoundedPrism_zero :
    prismEndpoint 0 K ≫ weightedBoundedPrism F i q =
      q ≫ weightedNerveBaseMap (sublevelInclusion i) (rightFibrationTotalDiagram F) := by
  unfold weightedBoundedPrism
  rw [← Category.assoc, prismEndpoint_naturality, Category.assoc]
  rw [← Category.assoc (prismEndpoint 0 _), weightedTopPrism_zero, Category.id_comp]

/-- 円柱の終端は同じ上界への評価と元の係数包含。 -/
lemma weightedBoundedPrism_one :
    prismEndpoint 1 K ≫ weightedBoundedPrism F i q =
      (q ≫ weightedTotalBoundedEvaluation F i) ≫
        weightedNerveConstantLift (rightFibrationTotalDiagram F) i := by
  unfold weightedBoundedPrism
  rw [← Category.assoc, prismEndpoint_naturality, Category.assoc]
  rw [← Category.assoc (prismEndpoint 1 _), weightedTopPrism_one,
    Category.assoc, weightedNerveConstantLift_baseMap]
  rfl

/-- 円柱全体の元の全空間余極限での値は、元の図式の値に厳密に固定される。 -/
lemma weightedBoundedPrism_assembly :
    weightedBoundedPrism F i q ≫ strictRightFibrationTotalAssembly F =
      snd (Δ[1] : SSet.{u}) K ≫
        (q ≫ weightedNerveBaseMap (sublevelInclusion i) (rightFibrationTotalDiagram F)) ≫
          strictRightFibrationTotalAssembly F := by
  let η : (sublevelInclusion i ⋙ rightFibrationTotalDiagram F) ⟶
      (CategoryTheory.Functor.const (Set.Iic i)).obj (colimit (rightFibrationTotalDiagram F)) :=
    CategoryTheory.Functor.whiskerLeft (sublevelInclusion i)
      (colimit.cocone (rightFibrationTotalDiagram F)).ι
  have hv : weightedNerveMap η ≫
      weightedNerveConstantEvaluation (Set.Iic i) (colimit (rightFibrationTotalDiagram F)) =
        weightedNerveBaseMap (sublevelInclusion i) (rightFibrationTotalDiagram F) ≫
          strictRightFibrationTotalAssembly F := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    rfl
  have h := weightedTopPrism_cocone (sublevelInclusion i ⋙ rightFibrationTotalDiagram F) η
  rw [hv] at h
  simpa only [weightedBoundedPrism, Category.assoc, whiskerLeft_snd_assoc] using
    congrArg (fun f => (Δ[1] ◁ q) ≫ f) h

/-- 小さい元の weighted 図式全体は、比較先での値を固定した円柱によって同じ一段へ輸送できる。 -/
lemma exists_weightedTotal_stageTransport {κ : Cardinal.{u}} [Fact κ.IsRegular]
    [IsCardinalFiltered I κ] {L : SSet.{u}} (hL : IsKappaSmall κ L)
    (a : L ⟶ weightedNerve (rightFibrationTotalDiagram F)) :
    ∃ (j : I) (g : L ⟶ (F.obj j).val.left)
      (H : (Δ[1] : SSet.{u}) ⊗ L ⟶ weightedNerve (rightFibrationTotalDiagram F)),
      prismEndpoint 0 L ≫ H = a ∧
      prismEndpoint 1 L ≫ H = g ≫ weightedNerveConstantLift (rightFibrationTotalDiagram F) j ∧
      H ≫ strictRightFibrationTotalAssembly F =
        snd (Δ[1] : SSet.{u}) L ≫ a ≫ strictRightFibrationTotalAssembly F ∧
      g ≫ colimit.ι (rightFibrationTotalDiagram F) j = a ≫ strictRightFibrationTotalAssembly F := by
  obtain ⟨j, q, hq, hg⟩ := exists_weightedTotal_boundedEvaluation F hL a
  refine ⟨j, q ≫ weightedTotalBoundedEvaluation F j, weightedBoundedPrism F j q,
    ?_, weightedBoundedPrism_one F j q, ?_, hg⟩
  · rw [weightedBoundedPrism_zero, hq]
  · rw [weightedBoundedPrism_assembly, hq]

end SerrePositivity.InfinityCategories.F2.Ind
