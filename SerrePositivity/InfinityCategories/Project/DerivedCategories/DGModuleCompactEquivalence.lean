module
public import SerrePositivity.DifferentialGraded.Perfect.Compact.FiniteGeneration
/-!
概要：異なる小さい dg 圏の主導来加群圏の加法的同値は compact・perfect を保存反映する。
方針：実余積比較と随伴 Hom 全単射で有限和表示を輸送する。
規約：対象宇宙の smallness を仮定しない。使われ方：β5 の Perf の Morita 不変性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits Preadditive DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) (E : Type w)
variable [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
/-- 主導来加群圏の加法的同値は、u-small 余積に関する compact 性を保存する。 -/
lemma dgModuleCompact_equivalence (e : DerivedModuleCategory R D ≌ DerivedModuleCategory R E)
    [e.functor.Additive] {X : DerivedModuleCategory R D} (hX : moduleCompact R D X) :
    moduleCompact R E (e.functor.obj X) := by
  classical
  intro J F f
  let c := PreservesCoproduct.iso e.inverse F
  let b := e.toAdjunction.homEquiv X (∐ F) f
  obtain ⟨t, g, hg⟩ := hX J (fun j => e.inverse.obj (F j)) (b ≫ c.hom)
  refine ⟨t, fun j => (e.toAdjunction.homEquiv X (F j)).symm (g j), ?_⟩
  apply (e.toAdjunction.homAddEquiv X (∐ F)).injective
  calc
    _ = ∑ j ∈ t, g j ≫ e.inverse.map (Sigma.ι F j) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro j _
      exact (e.toAdjunction.homEquiv_naturality_right _ _).trans
        (by rw [Equiv.apply_symm_apply])
    _ = (∑ j ∈ t, g j ≫ Sigma.ι (fun j => e.inverse.obj (F j)) j) ≫ c.inv := by
      rw [sum_comp]
      apply Finset.sum_congr rfl
      intro j _
      simp only [Category.assoc, c, PreservesCoproduct.inv_hom, ι_comp_sigmaComparison]
    _ = _ := by
      rw [hg, Category.assoc, Iso.hom_inv_id, Category.comp_id]
      rfl
/-- 主導来加群圏の加法的同値は、compact 性を保存・反映する。 -/
lemma dgModuleCompact_equivalence_iff (e : DerivedModuleCategory R D ≌ DerivedModuleCategory R E)
    [e.functor.Additive] (X : DerivedModuleCategory R D) :
    moduleCompact R E (e.functor.obj X) ↔ moduleCompact R D X := by
  constructor
  · intro h
    have : e.symm.functor.Additive := by change e.inverse.Additive; infer_instance
    exact (moduleCompact R D).prop_of_iso (e.unitIso.app X).symm
      (dgModuleCompact_equivalence R E D e.symm h)
  · exact dgModuleCompact_equivalence R D E e
/-- 主導来加群圏の加法的同値は、perfect 性を保存・反映する。 -/
lemma dgModulePerfect_equivalence_iff (e : DerivedModuleCategory R D ≌ DerivedModuleCategory R E)
    [e.functor.Additive] (X : DerivedModuleCategory R D) :
    modulePerfect R E (e.functor.obj X) ↔ modulePerfect R D X := by
  rw [← moduleCompact_iff_perfect, ← moduleCompact_iff_perfect]
  exact dgModuleCompact_equivalence_iff R D E e X
end SerrePositivity.InfinityCategories.Project.DerivedCategories
