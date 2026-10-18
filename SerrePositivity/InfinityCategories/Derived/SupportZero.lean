module
public import SerrePositivity.InfinityCategories.Derived.SupportClosure
public import SerrePositivity.InfinityCategories.DGNerve.SemifreeLimits

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
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve
open scoped Simplicial ZeroObject

private lemma terminal_iso {X Y : SSet.{u}} (e : X ≅ Y) {x : X _⦋0⦌}
    (hx : IsTerminalVertex x) : IsTerminalVertex (e.hom.app _ x) := by
  intro n b hb
  have hi : e.inv.app _ (e.hom.app _ x) = x := by
    change (e.hom ≫ e.inv).app _ x = x
    rw [Iso.hom_inv_id]
    rfl
  have hb' : boundaryVertex n (Fin.last (n + 1)) ≫ (b ≫ e.inv) = SSet.yonedaEquiv.symm x := by
    rw [← Category.assoc, hb, SSet.yonedaEquiv_symm_comp, hi]
  obtain ⟨f, hf⟩ := hx n _ hb'
  exact ⟨f ≫ e.hom, by rw [← Category.assoc, hf, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]⟩

private lemma initial_iso {X Y : SSet.{u}} (e : X ≅ Y) {x : X _⦋0⦌}
    (hx : IsInitialVertex x) : IsInitialVertex (e.hom.app _ x) := by
  intro n b hb
  have hi : e.inv.app _ (e.hom.app _ x) = x := by
    change (e.hom ≫ e.inv).app _ x = x
    rw [Iso.hom_inv_id]
    rfl
  have hb' : boundaryVertex n 0 ≫ (b ≫ e.inv) = SSet.yonedaEquiv.symm x := by
    rw [← Category.assoc, hb, SSet.yonedaEquiv_symm_comp, hi]
  obtain ⟨f, hf⟩ := hx n _ hb'
  exact ⟨f ≫ e.hom, by rw [← Category.assoc, hf, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]⟩

variable (S : Type u) [CommRing S]

/-- 概要：零複体を含む対象条件の全部分単体集合は零対象を持つ。
方針：semifree の零対象性を充満包含で反映し、像との同型で移す。
規約：P は任意の対象条件。使われ方：D_Z と Perf_Z の零対象。 -/
theorem semifreeFullSubcomplex_hasZeroVertex (P : Semifree S → Prop)
    (h0 : P ⟨0, complexSemifree_zero S⟩) :
    ∃ x : (semifreeFullSubcomplex S P : SSet.{u + 1}) _⦋0⦌,
      IsInitialVertex x ∧ IsTerminalVertex x := by
  let z : (semifreeFullNerve S P) _⦋0⦌ :=
    Simplex.vertex (⟨⟨0, complexSemifree_zero S⟩, h0⟩ : DGFullSubcategory (Semifree S) P)
  have hv : (semifreeFullNerveInclusion S P).app _ z =
      Simplex.vertex (⟨0, complexSemifree_zero S⟩ : Semifree S) := by
    apply Simplex.vertexEquiv.injective
    rfl
  have ht : IsTerminalVertex z := by
    apply isTerminalVertex_of_fullInclusion S (Semifree S) P
    change IsTerminalVertex ((semifreeFullNerveInclusion S P).app _ z)
    rw [hv]
    exact isTerminalVertex_semifree_zero S
  have hi : IsInitialVertex z := by
    apply isInitialVertex_of_fullInclusion S (Semifree S) P
    change IsInitialVertex ((semifreeFullNerveInclusion S P).app _ z)
    rw [hv]
    exact isInitialVertex_semifree_zero S
  exact ⟨(semifreeFullNerveIso S P).hom.app _ z,
    initial_iso _ hi, terminal_iso _ ht⟩

/-- 概要：D_Z の正本は零対象を持つ。
方針：零複体の幾何学的台は空であることを使う。
規約：任意の閉集合。使われ方：D_Z の零対象閉性。 -/
theorem derivedSupportCategory_hasZeroVertex (Z : TopologicalSpace.Closeds (PrimeSpectrum S)) :
    ∃ x : (derivedSupportCategory S Z) _⦋0⦌, IsInitialVertex x ∧ IsTerminalVertex x :=
  semifreeFullSubcomplex_hasZeroVertex S (derivedSupportProperty S Z)
    (hasHomologySupportOn_of_isZero (isZero_zero _))

/-- 概要：Perf_Z の正本は零対象を持つ。
方針：零複体の完全性と空の台を使う。
規約：任意の閉集合。使われ方：Perf_Z の零対象閉性。 -/
theorem perfectSupportCategory_hasZeroVertex (Z : TopologicalSpace.Closeds (PrimeSpectrum S)) :
    ∃ x : (perfectSupportCategory S Z) _⦋0⦌, IsInitialVertex x ∧ IsTerminalVertex x :=
  semifreeFullSubcomplex_hasZeroVertex S (perfectSupportProperty S Z)
    ⟨complexPerfectModel_zero S, hasHomologySupportOn_of_isZero (isZero_zero _)⟩

end SerrePositivity.InfinityCategories
