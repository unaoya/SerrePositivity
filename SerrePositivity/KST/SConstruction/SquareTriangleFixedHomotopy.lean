module
public import SerrePositivity.KST.SConstruction.SquareTriangleHomotopy
public import SerrePositivity.KST.SConstruction.FullCylinderBoundaryTensor
public import SerrePositivity.KST.SConstruction.FamilyCylinderFixedBoundary

/-! # 両三角形の全境界固定から正方形の全境界固定を回収する
概要：元の両三角形比較が全三辺を固定すれば、貼った全比較は正方形の四辺を固定する。
方針：四辺を元の三角形面へ因子分解し、境界の余積と pushout で全境界を判定する。
規約：入力全境界と比較時刻の両端の和を全高次比較時刻で同時に固定する。
使われ方：始辺消去の四面体比較を、全境界固定の出力円柱比較へ変換する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory SSet Spectra
open SerrePositivity.SimplicialModel.LargeParameterHomotopy
open scoped Simplicial
variable {E : SSet.{u}} {f g : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ E}
  (H : SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.upper ≫ f) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.upper ≫ g))
  (K : SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.lower ≫ f) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.lower ≫ g))
  (hc : (stdSimplex.δ 1 ▷ (Δ[1] : SSet.{u})) ≫ H.h =
    (stdSimplex.δ 1 ▷ (Δ[1] : SSet.{u})) ≫ K.h)
  (hH : ∀ i : Fin 3, (stdSimplex.δ i ▷ (Δ[1] : SSet.{u})) ≫ H.h =
    fst (Δ[1] : SSet.{u}) Δ[1] ≫ stdSimplex.δ i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.upper ≫ f)
  (hK : ∀ i : Fin 3, (stdSimplex.δ i ▷ (Δ[1] : SSet.{u})) ≫ K.h =
    fst (Δ[1] : SSet.{u}) Δ[1] ≫ stdSimplex.δ i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.lower ≫ f)

include hH hK

/-- 元の入力の両端辺は、全高次比較時刻で厳密に固定される。 -/
lemma squareTriangleHomotopyMap_input_vertex (i : Fin 2) :
    ((stdSimplex.δ i ▷ (Δ[1] : SSet.{u})) ▷ (Δ[1] : SSet.{u})) ≫
        squareTriangleHomotopyMap H K hc =
      fst ((Δ[0] : SSet.{u}) ⊗ Δ[1]) Δ[1] ≫
        (stdSimplex.δ i ▷ (Δ[1] : SSet.{u})) ≫ f := by
  rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
  · simp only [SquareTriangles.first_endpoint_zero, comp_whiskerRight, Category.assoc]
    rw [squareTriangleHomotopyMap_lower, hK]
    simp only [whiskerRight_fst_assoc]
  · simp only [SquareTriangles.first_endpoint_one, comp_whiskerRight, Category.assoc]
    rw [squareTriangleHomotopyMap_upper, hH]
    simp only [whiskerRight_fst_assoc]

/-- 元の比較時刻の両端辺も、全高次比較時刻で厳密に固定される。 -/
lemma squareTriangleHomotopyMap_time_vertex (i : Fin 2) :
    (((Δ[1] : SSet.{u}) ◁ stdSimplex.δ i) ▷ (Δ[1] : SSet.{u})) ≫
        squareTriangleHomotopyMap H K hc =
      fst ((Δ[1] : SSet.{u}) ⊗ Δ[0]) Δ[1] ≫
        ((Δ[1] : SSet.{u}) ◁ stdSimplex.δ i) ≫ f := by
  rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
  · simp only [SquareTriangles.second_endpoint_zero, comp_whiskerRight, Category.assoc]
    rw [squareTriangleHomotopyMap_upper, hH]
    simp only [whiskerRight_fst_assoc]
  · simp only [SquareTriangles.second_endpoint_one, comp_whiskerRight, Category.assoc]
    rw [squareTriangleHomotopyMap_lower, hK]
    simp only [whiskerRight_fst_assoc]

/-- 元の全入力境界を全高次比較時刻で厳密に固定する。 -/
lemma squareTriangleHomotopyMap_input :
    (((SSet.boundary 1).ι ▷ (Δ[1] : SSet.{u})) ▷ (Δ[1] : SSet.{u})) ≫
        squareTriangleHomotopyMap H K hc =
      fst ((∂Δ[1] : SSet.{u}) ⊗ Δ[1]) Δ[1] ≫
        ((SSet.boundary 1).ι ▷ (Δ[1] : SSet.{u})) ≫ f := by
  let hc' := mapIsColimitOfPreservesOfIsColimit
    (tensorRight (Δ[1] : SSet.{u}) ⋙ tensorRight (Δ[1] : SSet.{u}))
    _ _ HomotopyFunctionComplex.BoundaryOne.isColimit
  apply hc'.hom_ext
  rintro ⟨i⟩
  cases i <;>
    change ((SSet.boundary.ι _ ▷ (Δ[1] : SSet.{u})) ▷ (Δ[1] : SSet.{u})) ≫ _ =
      ((SSet.boundary.ι _ ▷ (Δ[1] : SSet.{u})) ▷ (Δ[1] : SSet.{u})) ≫
        fst ((∂Δ[1] : SSet.{u}) ⊗ Δ[1]) Δ[1] ≫
          ((SSet.boundary 1).ι ▷ (Δ[1] : SSet.{u})) ≫ f
  all_goals
    rw [← Category.assoc, ← comp_whiskerRight, ← comp_whiskerRight, SSet.boundary.ι_ι,
      squareTriangleHomotopyMap_input_vertex H K hc hH hK, whiskerRight_fst_assoc,
      ← Category.assoc (_ ▷ (Δ[1] : SSet.{u})), ← comp_whiskerRight, SSet.boundary.ι_ι]

/-- 元の全比較時刻境界も全高次比較時刻で厳密に固定する。 -/
lemma squareTriangleHomotopyMap_time :
    (((Δ[1] : SSet.{u}) ◁ (SSet.boundary 1).ι) ▷ (Δ[1] : SSet.{u})) ≫
        squareTriangleHomotopyMap H K hc =
      fst ((Δ[1] : SSet.{u}) ⊗ ∂Δ[1]) Δ[1] ≫
        ((Δ[1] : SSet.{u}) ◁ (SSet.boundary 1).ι) ≫ f := by
  let hc' := mapIsColimitOfPreservesOfIsColimit (tensorRight (Δ[1] : SSet.{u}))
    _ _ (boundaryColimit (Δ[1] : SSet.{u}))
  apply hc'.hom_ext
  rintro ⟨i⟩
  cases i <;>
    change (((Δ[1] : SSet.{u}) ◁ SSet.boundary.ι _) ▷ (Δ[1] : SSet.{u})) ≫ _ =
      (((Δ[1] : SSet.{u}) ◁ SSet.boundary.ι _) ▷ (Δ[1] : SSet.{u})) ≫
        fst ((Δ[1] : SSet.{u}) ⊗ ∂Δ[1]) Δ[1] ≫
          ((Δ[1] : SSet.{u}) ◁ (SSet.boundary 1).ι) ≫ f
  all_goals
    rw [← Category.assoc, ← comp_whiskerRight, ← whiskerLeft_comp, SSet.boundary.ι_ι,
      squareTriangleHomotopyMap_time_vertex H K hc hH hK, whiskerRight_fst_assoc,
      ← Category.assoc ((Δ[1] : SSet.{u}) ◁ _), ← whiskerLeft_comp, SSet.boundary.ι_ι]

/-- 入力全境界と元の比較時刻の両端の和を、全高次比較時刻で同時に固定する。 -/
lemma squareTriangleHomotopy_relative :
    (fullCylinderBoundaryInclusion (SSet.boundary 1).ι ▷ (Δ[1] : SSet.{u})) ≫
        (squareTriangleHomotopy H K hc).h =
      fst (fullCylinderBoundary (SSet.boundary 1).ι) Δ[1] ≫
        fullCylinderBoundaryInclusion (SSet.boundary 1).ι ≫ f := by
  apply (fullCylinderBoundaryTensor_fixed_iff (SSet.boundary 1).ι _ _).mpr
  exact ⟨squareTriangleHomotopyMap_time H K hc hH hK,
    squareTriangleHomotopyMap_input H K hc hH hK⟩

end SerrePositivity.KST.SConstruction
