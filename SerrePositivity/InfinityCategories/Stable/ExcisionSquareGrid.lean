module
public import SerrePositivity.InfinityCategories.Stable.ExcisionGridExtension
public import SerrePositivity.InfinityCategories.Stable.ExcisionGridSquareShape

/-!
概要：任意の四角形を厳密に保つ比較格子と二段階の局所余極限を構成する。
方針：有限順序添字の厳密左 Kan 拡張と、指定終対象への延長を交互に使う。
規約：各面の押し出し性はまだ結論しない。使われ方：HA 1.4.2.15 の比較格子。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 元の四角形・局所余極限・指定頂点を厳密に保持する比較。 -/
structure ExcisionSquareGrid {X : SSet.{u}} (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X)
    (z : X _⦋0⦌) where
  seed : nerve ExcisionGridSeedIndex.{u} ⟶ X
  square_eq : nerveMap excisionGridSquareInclusion ≫ seed = excisionGridSquareShapeIso.hom ≫ R
  zero_seed (v : (nerve ExcisionGridSeedIndex.{u}) _⦋0⦌) :
    ¬ IsExcisionGridSquare (nerveEquiv v) → seed.app (Opposite.op ⦋0⦌) v = z
  extension : ExcisionGridExtension seed z

/-- 元の四角形・局所余極限・指定頂点を厳密に保持する比較。 -/
lemma excisionSquareGrid_nonempty {X : SSet.{u}} [Quasicategory X] [HasFiniteColimits X]
    (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) (z : X _⦋0⦌) (hz : IsTerminalVertex z) :
    Nonempty (ExcisionSquareGrid R z) := by
  obtain ⟨G, hG, hGz⟩ := exists_posetSubtype_downward_terminal_extension
    IsExcisionGridSquare (fun h hb ↦ excisionGridSquare_downward h hb)
    (excisionGridSquareShapeIso.hom ≫ R) z hz
  obtain ⟨d⟩ := excisionGridExtension_nonempty G z hz
  exact ⟨⟨G, hG, hGz, d⟩⟩

/-- 元の四角形・局所余極限・指定頂点を厳密に保持する比較。 -/
def excisionGridSquareEmbedding : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶
    nerve ExcisionGridIndex.{u} :=
  excisionGridSquareShapeIso.inv ≫ nerveMap excisionGridSquareInclusion ≫
    nerveMap excisionGridSeedInclusion ≫ nerveMap excisionGridCoreInclusion ≫
      nerveMap excisionGridMiddleInclusion

/-- 元の四角形・局所余極限・指定頂点を厳密に保持する比較。 -/
lemma ExcisionSquareGrid.square_restriction {X : SSet.{u}}
    {R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X} {z : X _⦋0⦌} (d : ExcisionSquareGrid R z) :
    excisionGridSquareEmbedding ≫ d.extension.full = R := by
  simp only [excisionGridSquareEmbedding, Category.assoc,
    d.extension.seed_restriction, d.square_eq, Iso.inv_hom_id_assoc]

end SerrePositivity.InfinityCategories
