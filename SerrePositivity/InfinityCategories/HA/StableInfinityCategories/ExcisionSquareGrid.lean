module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridExtension
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridSquareShape

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
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 元の四角形・局所余極限・指定頂点を厳密に保持する比較。 -/
structure ExcisionSquareGrid {X : SSet.{u}} (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X)
    (z : X _⦋0⦌) where
  seed : nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridSeedIndex.{u} ⟶ X
  square_eq : nerveMap _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSquareInclusion ≫ seed = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSquareShapeIso.hom ≫ R
  zero_seed (v : (nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridSeedIndex.{u}) _⦋0⦌) :
    ¬ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionGridSquare (nerveEquiv v) → seed.app (Opposite.op ⦋0⦌) v = z
  extension : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridExtension seed z

/-- 元の四角形・局所余極限・指定頂点を厳密に保持する比較。 -/
lemma excisionSquareGrid_nonempty {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteColimits X]
    (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) (z : X _⦋0⦌) (hz : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex z) :
    Nonempty (ExcisionSquareGrid R z) := by
  obtain ⟨G, hG, hGz⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exists_posetSubtype_downward_terminal_extension
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionGridSquare (fun h hb ↦ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSquare_downward h hb)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSquareShapeIso.hom ≫ R) z hz
  obtain ⟨d⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridExtension_nonempty G z hz
  exact ⟨⟨G, hG, hGz, d⟩⟩

/-- 元の四角形・局所余極限・指定頂点を厳密に保持する比較。 -/
def excisionGridSquareEmbedding : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶
    nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridIndex.{u} :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSquareShapeIso.inv ≫ nerveMap _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSquareInclusion ≫
    nerveMap _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSeedInclusion ≫ nerveMap _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCoreInclusion ≫
      nerveMap _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridMiddleInclusion

/-- 元の四角形・局所余極限・指定頂点を厳密に保持する比較。 -/
lemma ExcisionSquareGrid.square_restriction {X : SSet.{u}}
    {R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X} {z : X _⦋0⦌} (d : ExcisionSquareGrid R z) :
    excisionGridSquareEmbedding ≫ d.extension.full = R := by
  simp only [excisionGridSquareEmbedding, Category.assoc,
    d.extension.seed_restriction, d.square_eq, Iso.inv_hom_id_assoc]

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
