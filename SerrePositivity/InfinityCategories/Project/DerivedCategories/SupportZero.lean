module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.SupportClosure
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeLimits

/-! # 台つき部分 ∞ 圏の零対象

概要：D_Z と Perf_Z は D(S) と同じ零複体の頂点を零対象として持つ。
方針：充満 dg 部分圏で零対象を反映し、像との単体的同型で移す。
規約：任意の閉集合 Z。使われ方：台つき部分圏の零対象閉性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded
open scoped _root_.Simplicial ZeroObject

private lemma terminal_iso {X Y : SSet.{u}} (e : X ≅ Y) {x : X _⦋0⦌}
    (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex x) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (e.hom.app _ x) := by
  intro n b hb
  have hi : e.inv.app _ (e.hom.app _ x) = x := by
    change (e.hom ≫ e.inv).app _ x = x
    rw [Iso.hom_inv_id]
    rfl
  have hb' : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫ (b ≫ e.inv) = SSet.yonedaEquiv.symm x := by
    rw [← Category.assoc, hb, SSet.yonedaEquiv_symm_comp, hi]
  obtain ⟨f, hf⟩ := hx n _ hb'
  exact ⟨f ≫ e.hom, by rw [← Category.assoc, hf, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]⟩

private lemma initial_iso {X Y : SSet.{u}} (e : X ≅ Y) {x : X _⦋0⦌}
    (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex x) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex (e.hom.app _ x) := by
  intro n b hb
  have hi : e.inv.app _ (e.hom.app _ x) = x := by
    change (e.hom ≫ e.inv).app _ x = x
    rw [Iso.hom_inv_id]
    rfl
  have hb' : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ (b ≫ e.inv) = SSet.yonedaEquiv.symm x := by
    rw [← Category.assoc, hb, SSet.yonedaEquiv_symm_comp, hi]
  obtain ⟨f, hf⟩ := hx n _ hb'
  exact ⟨f ≫ e.hom, by rw [← Category.assoc, hf, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]⟩

variable (S : Type u) [CommRing S]

/-- 概要：零複体を含む対象条件の全部分単体集合は零対象を持つ。
方針：semifree の零対象性を充満包含で反映し、像との同型で移す。
規約：P は任意の対象条件。使われ方：D_Z と Perf_Z の零対象。 -/
theorem semifreeFullSubcomplex_hasZeroVertex (P : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S → Prop)
    (h0 : P ⟨0, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexSemifree_zero S⟩) :
    ∃ x : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeFullSubcomplex S P : SSet.{u + 1}) _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex x ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex x := by
  let z : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeFullNerve S P) _⦋0⦌ :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (⟨⟨0, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexSemifree_zero S⟩, h0⟩ : DGFullSubcategory (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S) P)
  have hv : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeFullNerveInclusion S P).app _ z =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (⟨0, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexSemifree_zero S⟩ : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S) := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.injective
    rfl
  have ht : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex z := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.isTerminalVertex_of_fullInclusion S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S) P
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeFullNerveInclusion S P).app _ z)
    rw [hv]
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.isTerminalVertex_semifree_zero S
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex z := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.isInitialVertex_of_fullInclusion S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S) P
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeFullNerveInclusion S P).app _ z)
    rw [hv]
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.isInitialVertex_semifree_zero S
  exact ⟨(_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeFullNerveIso S P).hom.app _ z,
    initial_iso _ hi, terminal_iso _ ht⟩

/-- 概要：D_Z の正本は零対象を持つ。
方針：零複体の幾何学的台は空であることを使う。
規約：任意の閉集合。使われ方：D_Z の零対象閉性。 -/
theorem derivedSupportCategory_hasZeroVertex (Z : TopologicalSpace.Closeds (PrimeSpectrum S)) :
    ∃ x : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSupportCategory S Z) _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex x ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex x :=
  semifreeFullSubcomplex_hasZeroVertex S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSupportProperty S Z)
    (hasHomologySupportOn_of_isZero (isZero_zero _))

/-- 概要：Perf_Z の正本は零対象を持つ。
方針：零複体の完全性と空の台を使う。
規約：任意の閉集合。使われ方：Perf_Z の零対象閉性。 -/
theorem perfectSupportCategory_hasZeroVertex (Z : TopologicalSpace.Closeds (PrimeSpectrum S)) :
    ∃ x : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectSupportCategory S Z) _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex x ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex x :=
  semifreeFullSubcomplex_hasZeroVertex S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectSupportProperty S Z)
    ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPerfectModel_zero S, hasHomologySupportOn_of_isZero (isZero_zero _)⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
