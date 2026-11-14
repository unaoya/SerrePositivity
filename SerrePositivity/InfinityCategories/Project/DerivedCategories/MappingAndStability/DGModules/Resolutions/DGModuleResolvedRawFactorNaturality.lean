module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Resolutions.DGModuleResolvedPrecompComposition
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Resolutions.DGModuleResolvedRawFactor
/-!
概要：元の指定 raw factor 比較は、任意の dg 入力前合成と整合する。
方針：元の resolved 比較の合成則を恒等出力に適用し、同じ恒等合成の端点を輸送する。
規約：元の比較と実関手を保持する。使われ方：導来 kernel 合成子の経路照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (A B : Type (max (u + 1) v))
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R A] [_root_.SerrePositivity.DifferentialGraded.DGCategory R B] (E : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
omit [_root_.SerrePositivity.DifferentialGraded.DGCategory R A] in
/-- 元の raw factor 比較は、同じ指定前合成比較を恒等出力へ適用した値である。 -/
lemma dgModuleResolvedInfinity_rawFactorIso_heq (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R B (_root_.SerrePositivity.DifferentialGraded.RightModule R E)) :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_rawFactorIso R B E F)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_precompIso R B (RightModule R E) E F
        (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R E))) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_rawFactorIso, Eq.mp]
  rfl
/-- 出力 dg 関手の同じ表示の等式は、元の指定前合成比較を型付きで保持する。 -/
lemma dgModuleResolvedInfinity_precompIso_heq_of_output_eq (H : _root_.SerrePositivity.DifferentialGraded.DGFunctor R A B)
    {F G : _root_.SerrePositivity.DifferentialGraded.DGFunctor R B (_root_.SerrePositivity.DifferentialGraded.RightModule R E)} (h : F = G) :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_precompIso R A B E H F)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_precompIso R A B E H G) := by
  subst G
  rfl
/-- 元の raw factor 比較は、同じ入力 dg 関手の前合成に関して型付きで自然。 -/
lemma dgModuleResolvedInfinity_rawFactorIso_precomp_heq (H : _root_.SerrePositivity.DifferentialGraded.DGFunctor R A B)
    (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R B (_root_.SerrePositivity.DifferentialGraded.RightModule R E)) :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_rawFactorIso R A E (H.comp F))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_precompIso R A B E H F ≪≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_rawFactorIso R B E F).precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map H)) := by
  let I : _root_.SerrePositivity.DifferentialGraded.DGFunctor R (_root_.SerrePositivity.DifferentialGraded.RightModule R E) (_root_.SerrePositivity.DifferentialGraded.RightModule R E) :=
    _root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R E)
  have hF : F.comp I = F := by
    apply EnrichedFunctor.ext (_root_.SerrePositivity.DifferentialGraded.Complex R) (fun _ => rfl)
    intro X Y
    simp only [EnrichedFunctor.comp_map,
      eqToHom_refl, Category.comp_id]
  let p := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_precompIso R A B E H F
  let q := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_rawFactorIso R B E F).precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map H)
  let p' := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_precompIso R A B E H (F.comp I)
  let q' := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_precompIso R B (RightModule R E) E F I).precomp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map H)
  have hp : HEq p p' :=
    (dgModuleResolvedInfinity_precompIso_heq_of_output_eq R A B E H hF).symm
  have hq : HEq q q' :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.functorIso_precomp_heq_of_heq
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_precompIso R B (RightModule R E) E F I)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_rawFactorIso R B E F)
      (congrArg (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R B E) hF) rfl
      (dgModuleResolvedInfinity_rawFactorIso_heq R B E F) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map H)
  have hs := congrArg (fun G => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R A E (H.comp G)) hF.symm
  have ht := congrArg (fun G => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map H ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R B E G) hF.symm
  have hpath := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_trans_heq p q p' q' hs ht rfl hp hq
  exact (dgModuleResolvedInfinity_rawFactorIso_heq R A E (H.comp F)).trans
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_precompIso_comp_heq R A B (RightModule R E) E H F I).trans
      hpath.symm)
/-- 明示した元の nerve 合成の端点輸送の下で、raw factor の入力自然性は等式となる。 -/
lemma dgModuleResolvedInfinity_rawFactorIso_precomp (H : _root_.SerrePositivity.DifferentialGraded.DGFunctor R A B)
    (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R B (_root_.SerrePositivity.DifferentialGraded.RightModule R E)) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_rawFactorIso R A E (H.comp F)) rfl
      (congrArg (fun m => m ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (RightModule R E) E
        (DGFunctor.id (RightModule R E))) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp H F)) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_precompIso R A B E H F ≪≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_rawFactorIso R B E F).precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map H) := by
  apply eq_of_heq
  exact (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_heq _ _ _).trans
    (dgModuleResolvedInfinity_rawFactorIso_precomp_heq R A B E H F)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
