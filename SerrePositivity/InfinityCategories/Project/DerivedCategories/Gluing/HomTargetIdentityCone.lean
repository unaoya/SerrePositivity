module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomTargetIdentityFunctor
public import SerrePositivity.KST.SConstruction.DGHomGluingConeFunctor
/-! 元二脚の実 cone 関手は、恒等二脚への三成分 dg 比較を通じて厳密に因子化する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory HomologicalComplex CochainComplex HomComplex DifferentialGraded
open KST.SConstruction
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (E : Type z) [DGCategory R E] [Small.{u} E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
local notation "M" => dgHomGluingBimodule R C D E p q
local notation "I" => dgHomGluingBimodule R E E E (DGFunctor.id E) (DGFunctor.id E)
local notation "T" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetIdentityObject R C D E p q
local notation "H" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetIdentityHomMap R C D E p q

lemma dgGluingHomTargetToIdentity_cone :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetToIdentity R C D E p q).comp
      (dgHomGluingConeFunctor R E E E (DGFunctor.id E) (DGFunctor.id E)) =
      dgHomGluingConeFunctor R C D E p q := by
  apply EnrichedFunctor.ext (Complex R)
  case h_obj => intro X; rfl
  intro X Y
  simp only [eqToHom_refl, Category.comp_id]
  change H X Y ≫ dgHomGluingConeHomMap R E E E
    (DGFunctor.id E) (DGFunctor.id E) (T X) (T Y) = dgHomGluingConeHomMap R C D E p q X Y
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change (dgHomGluingConeHomMap R E E E (DGFunctor.id E) (DGFunctor.id E)
    (T X) (T Y)).f n ((H X Y).f n a) = _
  have hl := congrArg (fun f => f.f n a)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetIdentityHomMap_left R C D E p q X Y)
  have hr := congrArg (fun f => f.f n a)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetIdentityHomMap_right R C D E p q X Y)
  have hp := congrArg (fun f => f a) (Cochain.congr_v
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetIdentityHomMap_comparison R C D E p q X Y) n (n - 1) (by omega))
  simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply] at hl hr
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComparison, Cochain.zero_cochain_comp_v,
    Cochain.ofHom_v, ModuleCat.comp_apply] at hp
  erw [dgHomGluingConeHomMap_apply, dgHomGluingConeHomMap_apply]
  simp only [dgHomGluingConeLeftMap, dgHomGluingConeRightMap, dgHomGluingConePrimitive,
    DGFunctor.id, EnrichedFunctor.id_map, Category.id_comp,
    HomologicalComplex.comp_f, ModuleCat.comp_apply,
    Cochain.comp_zero_cochain_v, Cochain.ofHom_v]
  erw [hl, hr, hp]
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
