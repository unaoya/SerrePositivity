module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.ConeTransformationPointAt
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.SourceConstantTransformationVertex
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.SourceConstantTransformationHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.HomotopyConeBoundary
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.FatConeCylinderIso

/-!
概要：指定変換から実現した錐の標準変換を、同じ元の指定変換へ戻す。
方針：実現の両端固定比較を元の円柱で制限して curry する。
規約：元の錐・図式・指定頂点・比較時間全体を保持する。
使われ方：全切断の恒等射を表す変換との整合性。

対応節は Kerodon 4.3（Tag 015M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
variable {K X : SSet.{u}} {f : K ⟶ X} {z : X _⦋0⦌}

/-- 実現した錐の標準変換と、元の指定変換の実際のホモトピー。 -/
def coneRealizationTransformationHomotopy
    (t : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const z)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f)) _⦋0⦌)
    (R : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.HomotopyConeRealization
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeOfVertex t).toTruncated)) :
    SSet.Homotopy (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.coneTransformationPointAt R.cone z R.vertex_eq))
      (SSet.yonedaEquiv.symm t) := by
  let a := SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.coneTransformationPointAt R.cone z R.vertex_eq)
  let b := SSet.yonedaEquiv.symm t
  let q := fst (K ⊗ (Δ[1] : SSet.{u})) (Δ[0] : SSet.{u}) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.fatConeCylinderMap K
  let h := (q ▷ (Δ[1] : SSet.{u})) ≫ R.comparison.h
  have h₀ : SSet.ι₀ ≫ h = _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.sourceConstantTransformationPrism a := by
    dsimp only [h]
    rw [← Category.assoc, SSet.ι₀_comp, Category.assoc, R.comparison.h₀,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.coneTransformationPointAt_prism]
    rfl
  have h₁ : SSet.ι₁ ≫ h = _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.sourceConstantTransformationPrism b := by
    dsimp only [h, q]
    rw [← Category.assoc, SSet.ι₁_comp, Category.assoc, R.comparison.h₁,
      _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.sourceConstantTransformationPrism_vertex, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.fatConeCylinderMap,
      Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.homotopyFatCone_cylinder, ← Category.assoc]
    have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.fatConeCylinderEmbedding K ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.fatConeCylinderProjection K = 𝟙 _ :=
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.fatConeCylinderIso K).inv_hom_id
    rw [Category.assoc, ← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.fatConeCylinderEmbedding K), hi, Category.id_comp]
  let H : SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.sourceConstantTransformationPrism a)
      (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.sourceConstantTransformationPrism b) := ⟨h, h₀, h₁, by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property⟩
  apply _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.sourceConstantTransformationHomotopyOfPrisms a b H
  · change ((SSet.ι₀ (X := K) ▷ (Δ[0] : SSet.{u})) ▷ (Δ[1] : SSet.{u})) ≫ h = _
    dsimp only [h, q]
    rw [← Category.assoc, ← comp_whiskerRight]
    have he : (SSet.ι₀ (X := K) ▷ (Δ[0] : SSet.{u})) ≫
        (fst (K ⊗ (Δ[1] : SSet.{u})) Δ[0] ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.fatConeCylinderMap K) =
        (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) : K ⊗ Δ[0] ⟶ Δ[0]) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl Δ[0] K := by
      change (fst K Δ[0] ≫ SSet.ι₀) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.fatConeCylinderMap K = _
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.fatConeCylinderMap_zero, ← Category.assoc, SSet.comp_const]
    rw [he, comp_whiskerRight, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.homotopyConeRealization_left, SSet.comp_const]
  · change ((SSet.ι₁ (X := K) ▷ (Δ[0] : SSet.{u})) ▷ (Δ[1] : SSet.{u})) ≫ h = _
    dsimp only [h, q]
    rw [← Category.assoc, ← comp_whiskerRight]
    have he : (SSet.ι₁ (X := K) ▷ (Δ[0] : SSet.{u})) ≫
        (fst (K ⊗ (Δ[1] : SSet.{u})) Δ[0] ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.fatConeCylinderMap K) =
        fst K Δ[0] ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr Δ[0] K := by
      change (fst K Δ[0] ≫ SSet.ι₁) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.fatConeCylinderMap K = _
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.fatConeCylinderMap_one]
    rw [he, comp_whiskerRight, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.homotopyConeRealization_right,
      ← Category.assoc, whiskerRight_fst, Category.assoc]

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
