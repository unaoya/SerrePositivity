module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
概要：固有なスキーム論的閉像の稠密像から全射性を得る。
方針：固有射の閉像と、既存のスキーム論的像への因子化を使う。
規約：基底の Noether 性と被約性は不要。
使われ方：Rydh Proposition 3.7、閉包の全射性と C02 の閉包絡への移送。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
universe u

/-- 固有射の像が稠密なら、その射は全射。 -/
theorem surjective_of_isProper_of_denseRange
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (hf : DenseRange f) : Surjective f := by
  constructor
  intro y
  have hy := hf y
  rw [f.isClosedMap.isClosed_range.closure_eq] at hy
  exact hy

/-- 合成の像が稠密なら、固有な構造射を持つ実際のスキーム論的像は基底へ全射。 -/
theorem surjective_imageι_comp_of_denseRange
    {X Y S : Scheme.{u}} (j : X ⟶ Y) [QuasiCompact j]
    (p : Y ⟶ S) [IsProper p] (hjp : DenseRange (j ≫ p)) :
    Surjective (j.imageι ≫ p) := by
  apply surjective_of_isProper_of_denseRange
  intro s
  apply closure_mono (t := Set.range (j.imageι ≫ p)) ?_ (hjp s)
  rintro _ ⟨x, rfl⟩
  refine ⟨j.toImage x, ?_⟩
  change p (j.imageι (j.toImage x)) = p (j x)
  congr 1

end SerrePositivity.AlgebraicGeometry
