module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Functoriality.YonedaCoefficientActions

/-! 全次数の共変作用を、同じ Yoneda 逆同型を通して運ぶ。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]

lemma dgGluingYonedaCoefficient_post_inv
    (x : C) (U V : RightModule R C) {q p n : ℤ}
    (t : (U.obj (op x)).X q) (g : (moduleHom R C U V).X p) (hn : q + p = n) :
    forward R (x := representable R x) (y := U) (z := V)
      ((dgYonedaIso R x U).inv.f q t) g hn =
    (dgYonedaIso R x V).inv.f n
      ((q * p).negOnePow • ((moduleHomπ R C U V x).f p g).v q n hn t) := by
  apply (ModuleCat.mono_iff_injective ((dgYonedaIso R x V).hom.f n)).mp inferInstance
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingYonedaCoefficient_post]
  have ht : (dgYonedaIso R x U).hom.f q ((dgYonedaIso R x U).inv.f q t) = t := by
    change (((dgYonedaIso R x U).inv ≫ (dgYonedaIso R x U).hom).f q) t = t
    rw [Iso.inv_hom_id, HomologicalComplex.id_f, ModuleCat.id_apply]
  rw [ht]
  have hi := congrArg (fun k => k.f n) (dgYonedaIso R x V).inv_hom_id
  have he := congrArg (fun k => k
    ((q * p).negOnePow • ((moduleHomπ R C U V x).f p g).v q n hn t)) hi
  simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f,
    ModuleCat.comp_apply, ModuleCat.id_apply] using he.symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
