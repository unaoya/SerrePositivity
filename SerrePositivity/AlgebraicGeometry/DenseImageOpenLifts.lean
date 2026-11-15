module

public import SerrePositivity.AlgebraicGeometry.SchemeImageDominance

/-!
概要：稠密な射の実際の像の包含の全射性と、像を含む開への持ち上げの稠密性を示す。
方針：閉じた像の稠密性と、開の lift の Cartesian 正方形を使う。
規約：scheme-theoretic な稠密性は、開包含に沿う平坦な底変換で移す。
使われ方：C06 の共通の開の像と有限 affine 被覆への持ち上げ。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u

/-- 稠密な射の実際の像の閉包含は全射。 -/
theorem surjective_schemeImageInclusion_of_isDominant
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsDominant f] : Surjective f.imageι := by
  haveI : IsDominant (f.toImage ≫ f.imageι) := by
    simpa only [Scheme.Hom.toImage_imageι] using (inferInstance : IsDominant f)
  haveI : IsDominant f.imageι := IsDominant.of_comp f.toImage f.imageι
  exact surjective_of_isDominant_of_isClosed_range f.imageι f.imageι.isClosedEmbedding.isClosed_range

/-- 稠密な開の実際のスキーム論的像の包含は全射。 -/
theorem surjective_denseOpenImageInclusion {X : Scheme.{u}} (W : X.Opens)
    (hW : Dense (W : Set X)) : Surjective W.ι.imageι := by
  haveI : IsDominant W.ι := ⟨by
    change Dense (Set.range W.ι)
    rw [Scheme.Opens.range_ι]
    exact hW⟩
  exact surjective_schemeImageInclusion_of_isDominant W.ι

/-- 像を含む開への持ち上げでも scheme-theoretic な稠密性が保たれる。 -/
theorem isSchemeTheoreticallyDominant_open_lift
    {X U Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [IsSchemeTheoreticallyDominant f]
    (g : U ⟶ Y) [IsOpenImmersion g] (H : Set.range f ⊆ Set.range g) :
    IsSchemeTheoreticallyDominant (IsOpenImmersion.lift g f H) :=
  IsSchemeTheoreticallyDominant.of_isPullback (IsOpenImmersion.isPullback_lift_id f g H).flip

/-- 開包含をその像を含む別の開へ持ち上げた射も開包含。 -/
theorem isOpenImmersion_open_lift
    {X U Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (g : U ⟶ Y) [IsOpenImmersion g] (H : Set.range f ⊆ Set.range g) :
    IsOpenImmersion (IsOpenImmersion.lift g f H) :=
  MorphismProperty.of_isPullback (IsOpenImmersion.isPullback_lift_id f g H).flip inferInstance

end SerrePositivity.AlgebraicGeometry
