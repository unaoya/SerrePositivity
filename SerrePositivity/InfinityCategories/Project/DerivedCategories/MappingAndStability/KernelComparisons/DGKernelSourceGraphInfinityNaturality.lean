module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.KernelComparisons.DGKernelDerivedCompositionRightNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.KernelComparisons.DGKernelSourceGraphComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.SimplicialFunctors.FunctorIsoTwoStepSquare
/-!
概要：元の graph 入力変更と元の kernel の実導来作用の任意射自然性を回収する。
方針：指定 graph 比較・κ・元の双加群同型の自然性を保持する。
規約：原 kernel に平坦性を追加しない。使われ方：元の始域制限と cell 入力比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet DifferentialGraded MonoidalClosed
variable (R : Type u) [CommRing R] (C D E : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C] [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C D)
variable {Q0 Q1 : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D} (g : Q0 ⟶ Q1)
local notation "q0" => _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D Q0
local notation "q1" => _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D Q1
local notation "H0" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D E q0
local notation "H1" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D E q1
local notation "P" => _root_.SerrePositivity.DifferentialGraded.functorGraph R C D F
local notation "J" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleExtensionInfinity R C D F
local notation "G" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R C D P
lemma dgKernelDerivedInfinity_sourceGraphIso_hom_naturality :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_sourceGraphIso R C D E F q0).hom ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R C E).map
        (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeMap R E D C g (𝟙 (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R D C P))) =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp H0 H1 J ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R D E).map g) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_sourceGraphIso R C D E F q1).hom := by
  let e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso J G := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_graphIso R C D F).symm
  let a : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom H0 H1 := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R D E).map g
  have he : (e.postcomp H0).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp H0 H1 G a =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp H0 H1 J a ≫ (e.postcomp H1).hom := by
    simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_postcomp_hom_typed] using!
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHom_whisker_exchange_typed e.hom a
  have hk := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compIso_right_naturality R C D E
    (BimoduleCategory.of R D C P) g (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorGraph_rightRelativeKFlat R C D F)
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_trans_hom_square (e.postcomp H0) (e.postcomp H1)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R C D E P q0
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorGraph_rightRelativeKFlat R C D F))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R C D E P q1
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorGraph_rightRelativeKFlat R C D F))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp H0 H1 J a) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp H0 H1 G a)
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R C E).map
      (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeMap R E D C g (𝟙 (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R D C P)))) he hk
end SerrePositivity.InfinityCategories.Project.DerivedCategories
