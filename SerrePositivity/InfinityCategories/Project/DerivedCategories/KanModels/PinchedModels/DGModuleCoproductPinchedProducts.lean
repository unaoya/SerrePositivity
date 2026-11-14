module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Actions.DGModuleCoproductHomDegrees
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.PinchedModels.PinchedLinearProductCriterion
/-!
概要：加群余積の同じ包含による制限は、全 pinched 線形単体の直積表示を与える。
方針：全 Hom の次数別直積同型を線形単体の一般判定へ渡す。
規約：元の加群・包含・全次数を保持し、射影性や compact 性は仮定しない。
使われ方：D-8 c5 の native 余積の写像空間検査。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
variable {J : Type u}

lemma dgModuleCoproductHomProjections_bijective (M : J → _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D)
    (N : _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D) (k : ℤ) :
    Function.Bijective (fun z : (_root_.SerrePositivity.DifferentialGraded.moduleCoproductHomFan R D M N).pt.X k =>
      fun j => (eHomWhiskerRight (_root_.SerrePositivity.DifferentialGraded.Complex R) (Sigma.ι M j) N).f k z) := by
  have heq : (fun z : (_root_.SerrePositivity.DifferentialGraded.moduleCoproductHomFan R D M N).pt.X k =>
      fun j => (eHomWhiskerRight (_root_.SerrePositivity.DifferentialGraded.Complex R) (Sigma.ι M j) N).f k z) =
      fun z => (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCoproductHomDegreeIso R D M N k).hom z := by
    funext z j
    exact (ConcreteCategory.congr_hom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCoproductHomDegreeIso_π R D M N k j) z).symm
  rw [heq]
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCoproductHomDegreeIso R D M N k).toLinearEquiv.bijective

lemma dgModuleCoproductPinchedLinear_bijective (M : J → _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D)
    (N : _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D) (n : ℕ) :
    Function.Bijective (fun s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex R
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) (∐ M)) (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) N) n =>
      fun j => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearSimplexMap
        (eHomWhiskerRight (_root_.SerrePositivity.DifferentialGraded.Complex R) (Sigma.ι M j) N) s) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearSimplex_family_bijective _ (dgModuleCoproductHomProjections_bijective R D M N) n

lemma dgModuleCoproductStandard_bijective (M : J → _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D)
    (N : _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D) (n : ℕ) :
    Function.Bijective (fun s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardSimplex R
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) (∐ M)) (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) N) n =>
      fun j => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStandardSimplexMap
        (eHomWhiskerRight (_root_.SerrePositivity.DifferentialGraded.Complex R) (Sigma.ι M j) N) s) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStandardSimplex_family_bijective _ (dgModuleCoproductHomProjections_bijective R D M N) n

end SerrePositivity.InfinityCategories.Project.DerivedCategories
