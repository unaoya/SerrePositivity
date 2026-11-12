module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelIdentityInfinity
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGBimoduleIsoNerveAlgebra
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorHomotopyRawTransport
/-!
概要：元の通常 kernel 単位と同じ単位子の nerve 像を照合する。
方針：元の指定値と端点等式を保つ。
規約：原 Hom の平坦性を追加しない。使われ方：kernel の単位・結合 coherence。
-/
@[expose] public section
open CategoryTheory
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open DifferentialGraded SSet
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
/-- 元の通常単位は、同じ双加群単位子の nerve 像の指定値を保つ。 -/
lemma dgKernelIdentityNerveIso_value_heq :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelIdentityNerveIso R D)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleIsoNerve R D (RightModule R D)
        (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.leftBimoduleUnitIso R D (_root_.SerrePositivity.DifferentialGraded.RightModule R D)
          (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R D)))) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelIdentityNerveIso]
  rfl
/-- 元の通常単位の射は、同じ単位子の全関手射の像を保つ。 -/
lemma dgKernelIdentityNerveIso_hom_heq :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelIdentityNerveIso R D).hom
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleFunctorHomFunctor R D (RightModule R D)).map
        (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.leftBimoduleUnitIso R D (_root_.SerrePositivity.DifferentialGraded.RightModule R D)
          (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R D))).hom) := by
  have hh := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_hom_heq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelIdentityNerveIso R D)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleIsoNerve R D (RightModule R D)
      (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.leftBimoduleUnitIso R D (_root_.SerrePositivity.DifferentialGraded.RightModule R D)
        (DGFunctor.id (RightModule R D)))) rfl _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_id.symm
    (dgKernelIdentityNerveIso_value_heq R D)
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleFunctorHomFunctor_mapIso] at hh
  exact hh
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
