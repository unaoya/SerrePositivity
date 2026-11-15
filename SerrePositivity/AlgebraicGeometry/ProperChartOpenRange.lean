module

public import SerrePositivity.AlgebraicGeometry.ProperChartOpen
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import SerrePositivity.AlgebraicGeometry.CommonDenseOpenGluing

/-!
概要：チャート像への底変換で供給した開部分の範囲を、元の射影で特定する。
方針：閉包含の単射性と pullback の範囲を使う。
規約：実際の像と pullback の比較を保持する。
使われ方：C06 の貼り合わせた射の各 affine 開の逆像の一致。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u

/-- 像への射をチャートに沿って引き戻した範囲は、元のチャートの像の逆像。 -/
theorem range_pullback_toImage {Z X P : Scheme.{u}}
    (e : X ⟶ P) (a : Z ⟶ e.image) :
    Set.range (pullback.fst a e.toImage) = (a ≫ e.imageι) ⁻¹' Set.range e := by
  rw [Scheme.Pullback.range_fst]
  ext z
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    have hh := congrArg e.imageι hx
    simpa only [← Scheme.Hom.comp_apply, Scheme.Hom.toImage_imageι] using hh
  · rintro ⟨x, hx⟩
    refine ⟨x, e.imageι.isClosedEmbedding.injective ?_⟩
    simpa only [← Scheme.Hom.comp_apply, Scheme.Hom.toImage_imageι] using hx

/-- 実際のチャート上の固有射を、元の射影で決まる開部分の範囲とともに供給する。 -/
theorem exists_proper_chart_open_range
    {W Z X P : Scheme.{u}} (j : W ⟶ Z)
    [IsOpenImmersion j] [IsSchemeTheoreticallyDominant j] [QuasiCompact j]
    (p : Z ⟶ P) [IsProper p] (e : X ⟶ P) [IsImmersion e] [QuasiCompact e]
    (l : W ⟶ X) (h : j ≫ p = l ≫ e) :
    ∃ (V : Scheme.{u}) (b : V ⟶ Z) (r : V ⟶ X) (w : W ⟶ V),
      IsOpenImmersion b ∧ IsProper r ∧ IsOpenImmersion w ∧
      IsSchemeTheoreticallyDominant w ∧
      b ≫ p = r ≫ e ∧ w ≫ b = j ∧ w ≫ r = l ∧
      Set.range b = p ⁻¹' Set.range e := by
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
  haveI : IsSchemeTheoreticallyDominant w :=
    isSchemeTheoreticallyDominant_of_open_factor j b w hwb
  refine ⟨V, b, r, w, inferInstance, inferInstance, inferInstance,
    inferInstance, ?_, hwb, pullback.lift_snd _ _ _, ?_⟩
  · rw [← hap, ← Category.assoc]
    change (pullback.fst a e.toImage ≫ a) ≫ e.imageι =
      pullback.snd a e.toImage ≫ e
    rw [pullback.condition, Category.assoc, Scheme.Hom.toImage_imageι]
  · dsimp [b]
    rw [range_pullback_toImage, hap]

end SerrePositivity.AlgebraicGeometry
