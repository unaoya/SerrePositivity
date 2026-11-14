module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Resolutions.DGModuleOutputResolutionValue
/-!
概要：全実出力 ∞ 関手の各頂点から、元の同じ dg 像への次数別全射な準同型を得る。
方針：厳密切断から回収した実分解の augmentation と、入力の厳密な回収等式を使う。
規約：元の出力の射影性は不要。使われ方：D(R) 値 Hom の値の同定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] [Small.{u} E] (F : DGFunctor R C (RightModule R E))
/-- 同じ元の dg 像への実 augmentation は、全評価で準同型。 -/
lemma dgModuleOutputResolutionAugmentation_quasiIso (x : C) :
    moduleQuasiIso R E (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolutionAugmentation R C E F x) := by
  exact MorphismProperty.RespectsIso.postcomp (moduleQuasiIso R E) (eqToHom _)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolutionObject R C E F x).augmentation
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolutionObject R C E F x).quasiIso
/-- 同じ実 augmentation は、全評価の全整数次数で全射。 -/
lemma dgModuleOutputResolutionAugmentation_degree_surjective (x : C) :
    moduleDegreewiseSurjective R E (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolutionAugmentation R C E F x) := by
  intro d n
  apply (moduleSurjectiveAt_iff_epi R E d n _).2
  have : Epi (((moduleEvaluation R E d).map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolutionObject R C E F x).augmentation).f n) :=
    (moduleSurjectiveAt_iff_epi R E d n _).1
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolutionObject R C E F x).surjective d n)
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolutionAugmentation, CategoryTheory.Functor.map_comp,
    HomologicalComplex.comp_f]
  infer_instance
end SerrePositivity.InfinityCategories.Project.DerivedCategories
