module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.KanExtensions.RightKanConeUniverseShape
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightCounitUniverse

/-!
概要：元の指定右 Kan 輸送の全円柱を、同じ実形状の宇宙比較で移す。
方針：既存の simplexTensorMap の始域・定値族の法則と、実標準錐の比較を使う。
使われ方：Kerodon §7.3（Tag 02Y1）、HTT 6.2.2.6 の任意の係数での降下。
規約：元の始端・図式・固定頂点を保持し、点ごとに輸送を選び直さない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
open SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
open SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 実右 Kan 形状の逆宇宙比較も、元の始域射影を保つ。 -/
lemma rightKanShapeUniverseIso_inv_projection {K C : SSet.{u}}
    (δ : K ⟶ C) (c : C _⦋0⦌) :
    (rightKanShapeUniverseIso.{u, v} δ c).inv ≫
      (SSet.uliftFunctor.{v, u}).map (rightKanProjection δ c) =
      rightKanProjection ((SSet.uliftFunctor.{v, u}).map δ) (ULift.up c) := by
  rw [← rightKanShapeUniverseIso_projection, Iso.inv_hom_id_assoc]

/-- 元の指定輸送を、同じ全円柱と実形状の比較で大きい宇宙へ写す。 -/
def kanRightTransportUlift {K C D : SSet.{u}} {δ : K ⟶ C}
    {F₀ : K ⟶ D} {F : C ⟶ D} {α : SSet.Homotopy (δ ≫ F) F₀} {c : C _⦋0⦌}
    (t : RightKanConeTransport δ F₀ F α c) :
    RightKanConeTransport ((SSet.uliftFunctor.{v, u}).map δ)
      ((SSet.uliftFunctor.{v, u}).map F₀) ((SSet.uliftFunctor.{v, u}).map F)
      (kanRightCounitUlift.{u, v} α) (ULift.up c) where
  family := ((rightKanConeUniverseIso.{u, v} δ c).inv ▷ (Δ[1] : SSet.{max u v})) ≫
    simplexTensorMap.{v} t.family
  start := by
    rw [← Category.assoc, SSet.ι₀_comp, Category.assoc, simplexTensorMap_zero, t.start,
      rightKanConeUniverseIso_inv_canonical]
  diagram := by
    change (joinInr (Δ[0] : SSet.{max u v}) _ ▷ (Δ[1] : SSet.{max u v})) ≫
      ((rightKanConeUniverseIso.{u, v} δ c).inv ▷ (Δ[1] : SSet.{max u v})) ≫
        simplexTensorMap.{v} t.family =
      (rightKanProjection ((SSet.uliftFunctor.{v, u}).map δ) (ULift.up c) ▷
        (Δ[1] : SSet.{max u v})) ≫ simplexTensorMap.{v} α.h
    rw [← Category.assoc, ← comp_whiskerRight, rightKanConeUniverseIso_inv_inr,
      comp_whiskerRight, Category.assoc, simplexTensorMap_source, t.diagram,
      ← simplexTensorMap_source, ← Category.assoc, ← comp_whiskerRight,
      rightKanShapeUniverseIso_inv_projection]
  fixedVertex := by
    change (joinInl (Δ[0] : SSet.{max u v}) _ ▷ (Δ[1] : SSet.{max u v})) ≫
      ((rightKanConeUniverseIso.{u, v} δ c).inv ▷ (Δ[1] : SSet.{max u v})) ≫
        simplexTensorMap.{v} t.family = _
    rw [← Category.assoc, ← comp_whiskerRight, rightKanConeUniverseIso_inv_inl,
      comp_whiskerRight, Category.assoc, simplexTensorMap_source, t.fixedVertex,
      simplexTensorMap_constant, whiskerRight_fst_assoc]
    have he := congrArg (fun f => f ≫
      (SSet.uliftFunctor.{v, u}).map (rightKanCanonicalCone δ F c).val)
      (rightKanConeUniverseIso_inv_inl.{u, v} δ c)
    have h : (uliftStdSimplexIso.{u, v} 0).inv ≫
        (SSet.uliftFunctor.{v, u}).map (joinInl (Δ[0] : SSet.{u}) (rightKanShape δ c) ≫
          (rightKanCanonicalCone δ F c).val) =
      joinInl (Δ[0] : SSet.{max u v}) _ ≫
        (rightKanCanonicalCone ((SSet.uliftFunctor.{v, u}).map δ)
          ((SSet.uliftFunctor.{v, u}).map F) (ULift.up c)).val := by
      rw [Functor.map_comp]
      simpa only [Category.assoc, rightKanConeUniverseIso_inv_canonical] using he.symm
    simpa only [Category.assoc] using congrArg
      (fun f => fst (Δ[0] : SSet.{max u v}) (Δ[1] : SSet.{max u v}) ≫ f) h

/-- 同じ輸送の終端は、元の終端の全射の同じ宇宙移送になる。 -/
lemma kanRightTransportUlift_cone_val {K C D : SSet.{u}} {δ : K ⟶ C}
    {F₀ : K ⟶ D} {F : C ⟶ D} {α : SSet.Homotopy (δ ≫ F) F₀} {c : C _⦋0⦌}
    (t : RightKanConeTransport δ F₀ F α c) :
    (kanRightTransportUlift.{u, v} t).cone.val =
      (rightKanConeUniverseIso.{u, v} δ c).inv ≫
        (SSet.uliftFunctor.{v, u}).map t.cone.val := by
  change SSet.ι₁ ≫ ((rightKanConeUniverseIso.{u, v} δ c).inv ▷
    (Δ[1] : SSet.{max u v})) ≫ simplexTensorMap.{v} t.family = _
  rw [← Category.assoc, SSet.ι₁_comp, Category.assoc, simplexTensorMap_one]
  rfl

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
