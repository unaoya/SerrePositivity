module
public import SerrePositivity.DifferentialGraded.Module.Graded
public import SerrePositivity.DifferentialGraded.Module.Hom.ConeComparison

/-! 係数の全 Yoneda 同型による前後合成の評価と、同じ元の加群作用。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
open DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]

lemma dgGluingYonedaCoefficient_post
    (x : C) (U V : RightModule R C) {q p n : ℤ}
    (t : (moduleHom R C (representable R x) U).X q)
    (g : (moduleHom R C U V).X p) (hn : q + p = n) :
    (dgYonedaIso R x V).hom.f n
      (forward R (x := representable R x) (y := U) (z := V) t g hn) =
    (q * p).negOnePow • ((moduleHomπ R C U V x).f p g).v q n hn
      ((dgYonedaIso R x U).hom.f q t) := by
  dsimp only [dgYonedaIso]
  rw [yonedaEvaluateFamily_apply, yonedaEvaluateFamily_apply,
    moduleHomForward_π, Cochain.units_smul_v,
    Cochain.comp_v _ _ hn 0 q n (zero_add q) hn]
  rfl

lemma dgGluingYonedaCoefficient_inv_apply
    (x y : C) (N : RightModule R C) {p q n : ℤ}
    (t : (N.obj (op y)).X p) (f : GradedHom R x y q) (hn : q + p = n) :
    ((moduleHomπ R C (representable R y) N x).f p
      ((dgYonedaIso R y N).inv.f p t)).v q n hn f =
    (p * q).negOnePow • moduleAction R N (x := op y) (y := op x) f t (by omega) := by
  have hp := congrArg (fun k => k.f p t)
    (moduleHomEquiv_symm_π R C (N.obj (op y)) (representable R y) N
      (yonedaExtension R y N (𝟙 _)) x)
  change (moduleHomπ R C (representable R y) N x).f p
    ((dgYonedaIso R y N).inv.f p t) =
      (yonedaExtensionApp R y N (𝟙 _) (op x)).f p t at hp
  rw [hp]
  simpa only [HomologicalComplex.id_f, ModuleCat.id_apply] using
    yonedaExtensionApp_apply R y N (𝟙 _) (op x) p q n hn t f

lemma dgGluingYonedaCoefficient_pre
    (x y : C) (N : RightModule R C) {q p n : ℤ}
    (f : GradedHom R x y q) (t : (N.obj (op y)).X p) (hn : q + p = n) :
    (dgYonedaIso R x N).hom.f n
      (forward R (x := representable R x) (y := representable R y) (z := N)
        ((yonedaHom R C x y).f q f) ((dgYonedaIso R y N).inv.f p t) hn) =
    moduleAction R N (x := op y) (y := op x) f t (by omega) := by
  rw [dgGluingYonedaCoefficient_post]
  have hf : (dgYonedaIso R x (representable R y)).hom.f q
      ((yonedaHom R C x y).f q f) = f := by
    change ((yonedaHom R C x y ≫
      (dgYonedaIso R x (representable R y)).hom).f q) f = f
    rw [yonedaHom, Iso.inv_hom_id, HomologicalComplex.id_f, ModuleCat.id_apply]
  rw [hf, dgGluingYonedaCoefficient_inv_apply, mul_comm p q,
    smul_smul, Int.units_mul_self, one_smul]

lemma dgGluingYonedaCoefficient_pre_inv
    (x y : C) (N : RightModule R C) {q p n : ℤ}
    (f : GradedHom R x y q) (t : (N.obj (op y)).X p) (hn : q + p = n) :
    forward R (x := representable R x) (y := representable R y) (z := N)
      ((yonedaHom R C x y).f q f) ((dgYonedaIso R y N).inv.f p t) hn =
    (dgYonedaIso R x N).inv.f n
      (moduleAction R N (x := op y) (y := op x) f t (by omega)) := by
  apply (ModuleCat.mono_iff_injective ((dgYonedaIso R x N).hom.f n)).mp inferInstance
  rw [dgGluingYonedaCoefficient_pre]
  have hi := congrArg (fun k => k.f n)
    (dgYonedaIso R x N).inv_hom_id
  have he := congrArg (fun k => k
    (moduleAction R N (x := op y) (y := op x) f t (by omega : p + q = n))) hi
  simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f,
    ModuleCat.comp_apply, ModuleCat.id_apply] using he.symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
