module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridIndex
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PosetSubtypeExtensions

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
structure ExcisionGridExtension {X : SSet.{u}}
    (G : nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridSeedIndex.{u} ⟶ X) (z : X _⦋0⦌) where
  core : nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridCoreIndex.{u} ⟶ X
  middle : nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridMiddleIndex.{u} ⟶ X
  full : nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridIndex.{u} ⟶ X
  seed_eq : nerveMap _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSeedInclusion ≫ core = G
  core_eq : nerveMap _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCoreInclusion ≫ middle = core
  middle_eq : nerveMap _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridMiddleInclusion ≫ full = middle
  core_colimit (c : (nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridCoreIndex.{u}) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCanonicalCocone (nerveMap _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSeedInclusion) core c)
  full_colimit (c : (nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridIndex.{u}) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCanonicalCocone (nerveMap _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridMiddleInclusion) full c)
  zero_middle (v : (nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridMiddleIndex.{u}) _⦋0⦌) :
    ¬ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionGridCore (nerveEquiv v).val → middle.app (Opposite.op ⦋0⦌) v = z

/-- 元の四角形・局所余極限・指定頂点を厳密に保持する比較。 -/
lemma excisionGridExtension_nonempty {X : SSet.{u}} [Quasicategory X]
    [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteColimits X] (G : nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridSeedIndex.{u} ⟶ X)
    (z : X _⦋0⦌) (hz : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex z) : Nonempty (ExcisionGridExtension G z) := by
  obtain ⟨C, hC, hCc⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exists_finitePosetSubtypeLeftKan_strict_extension
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionGridSeed G
  obtain ⟨M, hM, hMz⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exists_posetSubtype_downward_terminal_extension
    (fun p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridMiddleIndex.{u} ↦ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionGridCore p.val)
    (fun h hb ↦ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCore_downward h hb) C z hz
  obtain ⟨F, hF, hFc⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exists_finitePosetSubtypeLeftKan_strict_extension
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionGridMiddle M
  exact ⟨⟨C, M, F, hC, hM, hF, hCc, hFc, hMz⟩⟩

/-- 元の四角形・局所余極限・指定頂点を厳密に保持する比較。 -/
lemma ExcisionGridExtension.seed_restriction {X : SSet.{u}}
    {G : nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridSeedIndex.{u} ⟶ X} {z : X _⦋0⦌}
    (d : ExcisionGridExtension G z) :
    nerveMap _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSeedInclusion ≫ nerveMap _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCoreInclusion ≫
      nerveMap _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridMiddleInclusion ≫ d.full = G := by
  rw [d.middle_eq, d.core_eq, d.seed_eq]

/-- 元の四角形・局所余極限・指定頂点を厳密に保持する比較。 -/
lemma ExcisionGridExtension.zero_full {X : SSet.{u}}
    {G : nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridSeedIndex.{u} ⟶ X} {z : X _⦋0⦌}
    (d : ExcisionGridExtension G z) (v : (nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridMiddleIndex.{u}) _⦋0⦌)
    (hv : ¬ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionGridCore (nerveEquiv v).val) :
    d.full.app (Opposite.op ⦋0⦌)
      ((nerveMap _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridMiddleInclusion).app (Opposite.op ⦋0⦌) v) = z :=
  (ConcreteCategory.congr_hom (NatTrans.congr_app d.middle_eq (Opposite.op ⦋0⦌)) v).trans
    (d.zero_middle v hv)

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
