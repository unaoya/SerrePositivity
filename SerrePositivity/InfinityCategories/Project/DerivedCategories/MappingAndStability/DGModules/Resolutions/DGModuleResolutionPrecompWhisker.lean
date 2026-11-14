module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Actions.DGModuleOutputPrecompComposition
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Resolutions.DGModuleResolvedPrecomposition
/-!
概要：元の unlifted・resolved 比較を、同じ入力 Up と出力 Down による前後合成へ回収する。
方針：既存定義の端点輸送だけを除き、元の指定比較をそのまま保持する。
規約：比較や切断を選び直さない。使われ方：元の resolved 比較の前合成則。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (A C : Type (max (u + 1) v w))
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R A] [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] (E : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
/-- 元の unlifted 比較は、同じ指定比較への元の入力 Up の前合成である。 -/
lemma dgModuleOutputResolution_unliftedPrecompIso_heq
    (H : _root_.SerrePositivity.DifferentialGraded.DGFunctor R A C) (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C (_root_.SerrePositivity.DifferentialGraded.RightModule R E)) :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolution_unliftedPrecompIso.{u, v, w} R A C E H F)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolution_precompIso R A C E H F).precomp
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v w, max (u + 1) w} R A))) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolution_unliftedPrecompIso,
    Eq.mp, Eq.mpr]
  rfl
/-- 元の resolved 比較は、同じ unlifted 比較への半自由出力 Down の後合成である。 -/
lemma dgModuleResolvedInfinity_precompIso_heq (A C : Type (max (u + 1) v))
    [_root_.SerrePositivity.DifferentialGraded.DGCategory R A] [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
    (E : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
    (H : _root_.SerrePositivity.DifferentialGraded.DGFunctor R A C) (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C (_root_.SerrePositivity.DifferentialGraded.RightModule R E)) :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_precompIso R A C E H F)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolution_unliftedPrecompIso.{u, v, v} R A C E H F).postcomp
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R E)))) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_precompIso, Eq.mp]
  rfl
end SerrePositivity.InfinityCategories.Project.DerivedCategories
