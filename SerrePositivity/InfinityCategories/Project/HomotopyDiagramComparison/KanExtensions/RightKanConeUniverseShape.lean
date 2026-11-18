module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.KanExtensions.UniverseRightKanCanonical

/-!
概要：指定右 Kan 輸送の全錐の形状を、既存の実宇宙同型で正規化する。
方針：元の join の宇宙同型と元の右 Kan 形状の宇宙同型を合成する。
使われ方：Kerodon §7.3（Tag 02Y1）、HTT 6.2.2.6 の指定余単位の係数変更。
規約：元の両包含と実標準錐を保持する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
open SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 左包含についても、既存の逆宇宙同型は同じ元の包含を与える。 -/
lemma uliftConeShapeIso_inv_inl (K : SSet.{u}) (n : ℕ) :
    joinInl (Δ[n] : SSet.{max u v}) ((SSet.uliftFunctor.{v, u}).obj K) ≫
      (uliftConeShapeIso.{u, v} K n).inv =
    (uliftStdSimplexIso.{u, v} n).inv ≫
      (SSet.uliftFunctor.{v, u}).map (joinInl (Δ[n] : SSet.{u}) K) := by
  have h : (SSet.uliftFunctor.{v, u}).map (joinInl (Δ[n] : SSet.{u}) K) ≫
      (uliftConeShapeIso.{u, v} K n).hom =
      (uliftStdSimplexIso.{u, v} n).hom ≫
        joinInl (Δ[n] : SSet.{max u v}) ((SSet.uliftFunctor.{v, u}).obj K) := by
    simp only [uliftConeShapeIso, Iso.trans_hom, joinIso, Iso.refl_hom,
      ← Category.assoc, uliftJoinIso_inl, joinInl_joinMap]
  apply (cancel_mono (uliftConeShapeIso.{u, v} K n).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, h,
    Iso.inv_hom_id_assoc]

/-- 元の全右 Kan 錐の形状の宇宙移送を、実右 Kan 形状へ接続する同じ同型。 -/
def rightKanConeUniverseIso {K C : SSet.{u}} (δ : K ⟶ C) (c : C _⦋0⦌) :
    (SSet.uliftFunctor.{v, u}).obj (join (Δ[0] : SSet.{u}) (rightKanShape δ c)) ≅
      join (Δ[0] : SSet.{max u v})
        (rightKanShape ((SSet.uliftFunctor.{v, u}).map δ) (ULift.up c)) :=
  uliftConeShapeIso.{u, v} (rightKanShape δ c) 0 ≪≫
    joinIso (Iso.refl _) (rightKanShapeUniverseIso.{u, v} δ c)

/-- 実全錐の逆宇宙比較は、元の図式包含を同じ形状の逆比較で保つ。 -/
lemma rightKanConeUniverseIso_inv_inr {K C : SSet.{u}} (δ : K ⟶ C) (c : C _⦋0⦌) :
    joinInr (Δ[0] : SSet.{max u v}) _ ≫ (rightKanConeUniverseIso.{u, v} δ c).inv =
      (rightKanShapeUniverseIso.{u, v} δ c).inv ≫
        (SSet.uliftFunctor.{v, u}).map (joinInr (Δ[0] : SSet.{u}) (rightKanShape δ c)) := by
  simp only [rightKanConeUniverseIso, Iso.trans_inv, joinIso, Iso.refl_inv,
    ← Category.assoc, joinInr_joinMap]
  rw [Category.assoc, uliftConeShapeIso_inv_inr]

/-- 実全錐の逆宇宙比較は、元の頂点包含も同じ標準単体の比較で保つ。 -/
lemma rightKanConeUniverseIso_inv_inl {K C : SSet.{u}} (δ : K ⟶ C) (c : C _⦋0⦌) :
    joinInl (Δ[0] : SSet.{max u v}) _ ≫ (rightKanConeUniverseIso.{u, v} δ c).inv =
      (uliftStdSimplexIso.{u, v} 0).inv ≫
        (SSet.uliftFunctor.{v, u}).map (joinInl (Δ[0] : SSet.{u}) (rightKanShape δ c)) := by
  simp only [rightKanConeUniverseIso, Iso.trans_inv, joinIso, Iso.refl_inv,
    ← Category.assoc, joinInl_joinMap, Category.id_comp]
  exact uliftConeShapeIso_inv_inl (rightKanShape δ c) 0

/-- 同じ宇宙比較の下で、元の標準錐の全射は大きい宇宙の実標準錐そのもの。 -/
lemma rightKanConeUniverseIso_inv_canonical {K C D : SSet.{u}}
    (δ : K ⟶ C) (F : C ⟶ D) (c : C _⦋0⦌) :
    (rightKanConeUniverseIso.{u, v} δ c).inv ≫
      (SSet.uliftFunctor.{v, u}).map (rightKanCanonicalCone δ F c).val =
      (rightKanCanonicalCone ((SSet.uliftFunctor.{v, u}).map δ)
        ((SSet.uliftFunctor.{v, u}).map F) (ULift.up c)).val := by
  have h := rightKanCanonicalCone_universe_val.{u, v} δ F c
  change joinMap (𝟙 (Δ[0] : SSet.{max u v})) (rightKanShapeUniverseIso.{u, v} δ c).hom ≫
      (rightKanCanonicalCone ((SSet.uliftFunctor.{v, u}).map δ)
        ((SSet.uliftFunctor.{v, u}).map F) (ULift.up c)).val =
    (uliftConeShapeIso.{u, v} (rightKanShape δ c) 0).inv ≫
      (SSet.uliftFunctor.{v, u}).map (rightKanCanonicalCone δ F c).val at h
  simp only [rightKanConeUniverseIso, Iso.trans_inv, joinIso, Iso.refl_inv, Category.assoc]
  rw [← h, ← Category.assoc, ← joinMap_comp, Category.id_comp, Iso.inv_hom_id,
    joinMap_id, Category.id_comp]

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
