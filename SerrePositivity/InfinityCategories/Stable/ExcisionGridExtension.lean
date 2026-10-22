module
public import SerrePositivity.InfinityCategories.Stable.ExcisionGridIndex
public import SerrePositivity.InfinityCategories.Stable.PosetSubtypeExtensions

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
structure ExcisionGridExtension {X : SSet.{u}}
    (G : nerve ExcisionGridSeedIndex.{u} ⟶ X) (z : X _⦋0⦌) where
  core : nerve ExcisionGridCoreIndex.{u} ⟶ X
  middle : nerve ExcisionGridMiddleIndex.{u} ⟶ X
  full : nerve ExcisionGridIndex.{u} ⟶ X
  seed_eq : nerveMap excisionGridSeedInclusion ≫ core = G
  core_eq : nerveMap excisionGridCoreInclusion ≫ middle = core
  middle_eq : nerveMap excisionGridMiddleInclusion ≫ full = middle
  core_colimit (c : (nerve ExcisionGridCoreIndex.{u}) _⦋0⦌) :
    IsColimitCone (leftKanCanonicalCocone (nerveMap excisionGridSeedInclusion) core c)
  full_colimit (c : (nerve ExcisionGridIndex.{u}) _⦋0⦌) :
    IsColimitCone (leftKanCanonicalCocone (nerveMap excisionGridMiddleInclusion) full c)
  zero_middle (v : (nerve ExcisionGridMiddleIndex.{u}) _⦋0⦌) :
    ¬ IsExcisionGridCore (nerveEquiv v).val → middle.app (Opposite.op ⦋0⦌) v = z

/-- 元の四角形・局所余極限・指定頂点を厳密に保持する比較。 -/
lemma excisionGridExtension_nonempty {X : SSet.{u}} [Quasicategory X]
    [HasFiniteColimits X] (G : nerve ExcisionGridSeedIndex.{u} ⟶ X)
    (z : X _⦋0⦌) (hz : IsTerminalVertex z) : Nonempty (ExcisionGridExtension G z) := by
  obtain ⟨C, hC, hCc⟩ := exists_finitePosetSubtypeLeftKan_strict_extension
    IsExcisionGridSeed G
  obtain ⟨M, hM, hMz⟩ := exists_posetSubtype_downward_terminal_extension
    (fun p : ExcisionGridMiddleIndex.{u} ↦ IsExcisionGridCore p.val)
    (fun h hb ↦ excisionGridCore_downward h hb) C z hz
  obtain ⟨F, hF, hFc⟩ := exists_finitePosetSubtypeLeftKan_strict_extension
    IsExcisionGridMiddle M
  exact ⟨⟨C, M, F, hC, hM, hF, hCc, hFc, hMz⟩⟩

/-- 元の四角形・局所余極限・指定頂点を厳密に保持する比較。 -/
lemma ExcisionGridExtension.seed_restriction {X : SSet.{u}}
    {G : nerve ExcisionGridSeedIndex.{u} ⟶ X} {z : X _⦋0⦌}
    (d : ExcisionGridExtension G z) :
    nerveMap excisionGridSeedInclusion ≫ nerveMap excisionGridCoreInclusion ≫
      nerveMap excisionGridMiddleInclusion ≫ d.full = G := by
  rw [d.middle_eq, d.core_eq, d.seed_eq]

/-- 元の四角形・局所余極限・指定頂点を厳密に保持する比較。 -/
lemma ExcisionGridExtension.zero_full {X : SSet.{u}}
    {G : nerve ExcisionGridSeedIndex.{u} ⟶ X} {z : X _⦋0⦌}
    (d : ExcisionGridExtension G z) (v : (nerve ExcisionGridMiddleIndex.{u}) _⦋0⦌)
    (hv : ¬ IsExcisionGridCore (nerveEquiv v).val) :
    d.full.app (Opposite.op ⦋0⦌)
      ((nerveMap excisionGridMiddleInclusion).app (Opposite.op ⦋0⦌) v) = z :=
  (ConcreteCategory.congr_hom (NatTrans.congr_app d.middle_eq (Opposite.op ⦋0⦌)) v).trans
    (d.zero_middle v hv)

end SerrePositivity.InfinityCategories
