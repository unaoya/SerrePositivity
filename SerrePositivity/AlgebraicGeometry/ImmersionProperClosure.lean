module

public import SerrePositivity.AlgebraicGeometry.SchemeImageDominance
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
概要：immersion の実際のスキーム論的像を、固有な周辺の閉包として供給する。
方針：像への開包含とその scheme-theoretic な稠密性、周辺への閉包含を組み合わせる。
規約：Stacks 01RG。Noether 性は閉包の構成そのものには要求しない。
使われ方：C06 の有限 affine 被覆の固有な閉包とグラフの閉包。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u

/-- 固有な周辺への準コンパクトな immersion は、実際の固有な閉包を持つ。 -/
theorem exists_immersion_proper_closure
    {U P S : Scheme.{u}} (i : U ⟶ P) [IsImmersion i] [QuasiCompact i]
    (q : P ⟶ S) [IsProper q] :
    ∃ (Z : Scheme.{u}) (a : U ⟶ Z) (j : Z ⟶ P),
      IsOpenImmersion a ∧ IsSchemeTheoreticallyDominant a ∧ IsClosedImmersion j ∧
        IsProper (j ≫ q) ∧ a ≫ j = i := by
  haveI : IsSchemeTheoreticallyDominant i.toImage := isSchemeTheoreticallyDominant_toImage i
  exact ⟨i.image, i.toImage, i.imageι, inferInstance, inferInstance, inferInstance,
    inferInstance, i.toImage_imageι⟩

/-- Noether な周辺への射の実際のスキーム論的像は Noether。 -/
theorem isNoetherian_schemeImage {X Y : Scheme.{u}} (f : X ⟶ Y) [IsNoetherian Y] :
    IsNoetherian f.image := by
  haveI : CompactSpace f.image := QuasiCompact.compactSpace_of_compactSpace f.imageι
  letI : IsLocallyNoetherian f.image := LocallyOfFiniteType.isLocallyNoetherian f.imageι
  exact ⟨⟩

end SerrePositivity.AlgebraicGeometry
