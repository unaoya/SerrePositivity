module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Functoriality.ModulePostAction
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomComplexes.Models.HomConeLeftModule
public import SerrePositivity.DifferentialGraded.Module.Hom.ConeComparison

/-! 既存の全 Hom 円錐比較を Yoneda 評価の標準円錐写像と同定する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory CochainComplex HomComplex
open DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (x : C) {P Q : ModuleCategory R C} (f : P ⟶ Q)
local notation "T" => ForgetEnrichment.of (Complex R) (representable R x)
local notation "U" => ForgetEnrichment.to (Complex R) P
local notation "V" => ForgetEnrichment.to (Complex R) Q
local notation "K" => ForgetEnrichment.to (Complex R) (moduleCone R C f)

/-- 左包含の Yoneda 評価は、元の加群円錐の同じ次数 −1 の包含。 -/
lemma dgGluingYonedaHomCone_inl :
    (moduleHomConeLeftCochain R C T f).comp
      (Cochain.ofHom (dgYonedaIso R x K).hom) (add_zero (-1)) =
    (Cochain.ofHom (dgYonedaIso R x U).hom).comp
      (mappingCone.inl ((moduleEvaluation R C x).map f)) (zero_add (-1)) := by
  have he := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingYonedaPostAction R C U K (-1) x (moduleConeInlElement R C f)
  rw [moduleConeInlElement_π] at he
  exact he

/-- 全 Hom の円錐比較を Yoneda で評価すると、両端の評価の標準円錐写像になる。 -/
lemma dgGluingYonedaHomConeComparison :
    moduleHomConeComparison R C T f ≫ (dgYonedaIso R x K).hom =
    mappingCone.map (eHomWhiskerLeft (Complex R) T f)
      ((moduleEvaluation R C x).map f) (dgYonedaIso R x U).hom (dgYonedaIso R x V).hom
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingYoneda_postcompose R C x f) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply mappingCone.ext_from (eHomWhiskerLeft (Complex R) T f) (n + 1) n rfl
  · have he := Cochain.congr_v (dgGluingYonedaHomCone_inl R C x f)
      (n + 1) n (by omega)
    simpa only [HomologicalComplex.comp_f, moduleHomConeComparison, mappingCone.map,
      mappingCone.inl_v_desc_f_assoc, mappingCone.inl_v_desc_f,
      Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v, Cochain.ofHom_v] using he
  · have he := congrArg (fun a => a.f n)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingYoneda_postcompose R C x (moduleConeInr R C f))
    simp only [HomologicalComplex.comp_f, moduleHomConeComparison, mappingCone.map,
      mappingCone.inr_f_desc_f_assoc, mappingCone.inr_f_desc_f]
    simp only [HomologicalComplex.comp_f, moduleConeInr_eval] at he
    exact he

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
