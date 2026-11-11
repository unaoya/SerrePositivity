module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ModulePostAction

/-! 全次数の加群後合成と、Yoneda 評価の逆との整合。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory CochainComplex HomComplex DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (U V : RightModule R C) (p : ℤ) (x : C) (z : (moduleHom R C U V).X p)

/-- 評価された作用を逆 Yoneda で戻すと、同じ元の全 Hom 後合成になる。 -/
lemma dgGluingYonedaPostAction_inv :
    ((moduleHomπ R C U V x).f p z).comp
      (Cochain.ofHom (dgYonedaIso R x V).inv) (add_zero p) =
    (Cochain.ofHom (dgYonedaIso R x U).inv).comp
      ((modulePostcompositionMap R C (representable R x) U V).f p z) (zero_add p) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingYonedaPostAction R C U V p x z
  have hh := congrArg (fun k =>
    ((Cochain.ofHom (dgYonedaIso R x U).inv).comp k (zero_add p)).comp
      (Cochain.ofHom (dgYonedaIso R x V).inv) (add_zero p)) h
  simp only [Cochain.comp_assoc_of_first_is_zero_cochain,
    Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp,
    Iso.hom_inv_id, Cochain.comp_id] at hh
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp,
    Iso.inv_hom_id, Cochain.id_comp] at hh
  exact hh.symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
