module

public import SerrePositivity.AlgebraicGeometry.DenseClosedFactor
public import SerrePositivity.AlgebraicGeometry.DenseImageOpenLifts
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
概要：グラフ閉包の射影をチャートの像へ因子化し、チャート上の固有射を供給する。
方針：共通の稠密な開での因子化を延ばし、チャートの開包含に沿って底変換する。
規約：像と pullback は実際の射から構成する。
使われ方：C06 の局所の固有射の貼り合わせ。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u

/-- 固有な射影を、共通の稠密な開で指定された実際のチャート像へ因子化する。 -/
theorem exists_proper_map_to_immersion_image
    {W Z X P : Scheme.{u}} (j : W ⟶ Z) [IsSchemeTheoreticallyDominant j]
    (p : Z ⟶ P) [IsProper p] (e : X ⟶ P) [IsImmersion e] [QuasiCompact e]
    (l : W ⟶ X) (h : j ≫ p = l ≫ e) :
    ∃ a : Z ⟶ e.image, IsProper a ∧ a ≫ e.imageι = p ∧
      j ≫ a = l ≫ e.toImage := by
  apply exists_proper_closed_factor_of_schemeTheoreticallyDominant j p e.imageι
    (l ≫ e.toImage)
  simpa only [Category.assoc, Scheme.Hom.toImage_imageι] using h

/-- 実際のチャート像の開部分への底変換は、チャート上の固有射を持つ開部分を供給する。 -/
theorem exists_proper_chart_open
    {W Z X P : Scheme.{u}} (j : W ⟶ Z)
    [IsOpenImmersion j] [IsSchemeTheoreticallyDominant j] [QuasiCompact j]
    (p : Z ⟶ P) [IsProper p] (e : X ⟶ P) [IsImmersion e] [QuasiCompact e]
    (l : W ⟶ X) (h : j ≫ p = l ≫ e) :
    ∃ (V : Scheme.{u}) (b : V ⟶ Z) (r : V ⟶ X) (w : W ⟶ V),
      IsOpenImmersion b ∧ IsProper r ∧ IsOpenImmersion w ∧
      IsSchemeTheoreticallyDominant w ∧
      b ≫ p = r ≫ e ∧ w ≫ b = j ∧ w ≫ r = l := by
  obtain ⟨a, ha, hap, hja⟩ := exists_proper_map_to_immersion_image j p e l h
  letI : IsProper a := ha
  let V := pullback a e.toImage
  let b : V ⟶ Z := pullback.fst a e.toImage
  let r : V ⟶ X := pullback.snd a e.toImage
  let w : W ⟶ V := pullback.lift j l hja
  have hwb : w ≫ b = j := pullback.lift_fst _ _ _
  haveI : IsOpenImmersion b := inferInstance
  haveI : IsOpenImmersion (w ≫ b) := by rw [hwb]; infer_instance
  haveI : IsOpenImmersion w := IsOpenImmersion.of_comp w b
  have H : Set.range j ⊆ Set.range b := by
    rintro _ ⟨x, rfl⟩
    exact ⟨w x, by simpa only [Scheme.Hom.comp_apply] using congrArg (fun k ↦ k x) hwb⟩
  have hw : w = IsOpenImmersion.lift b j H := by
    apply (cancel_mono b).mp
    rw [hwb, IsOpenImmersion.lift_fac]
  haveI : IsSchemeTheoreticallyDominant w := by
    rw [hw]
    exact isSchemeTheoreticallyDominant_open_lift j b H
  refine ⟨V, b, r, w, inferInstance, inferInstance, inferInstance, inferInstance, ?_, hwb, ?_⟩
  · rw [← hap, ← Category.assoc]
    change (pullback.fst a e.toImage ≫ a) ≫ e.imageι =
      pullback.snd a e.toImage ≫ e
    rw [pullback.condition, Category.assoc, Scheme.Hom.toImage_imageι]
  · exact pullback.lift_snd _ _ _

end SerrePositivity.AlgebraicGeometry
