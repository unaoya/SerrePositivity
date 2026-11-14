module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.KernelComparisons.DGKernelSourceGraphBimoduleNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.KernelComparisons.DGKernelDerivedHomFunctor
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
lemma dgKernelDerivedInfinity_sourceGraphBimoduleIso_hom_naturality
    {P0 P1 : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D} (g : P0 ⟶ P1) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_bimoduleIso R C E
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelSourceGraphBimoduleIso R C D E F
        (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D P0))).hom ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R C E).map
        ((_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.middleLeftRestrictionFunctor R E D C F).map g) =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R C E).map
        (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeMap R E D C g
          (𝟙 (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R D C (_root_.SerrePositivity.DifferentialGraded.functorGraph R C D F)))) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_bimoduleIso R C E
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelSourceGraphBimoduleIso R C D E F
          (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D P1))).hom := by
  have h := congrArg (fun z => (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R C E).map z)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelSourceGraphBimoduleIso_hom_naturality R C D E F g)
  simp only [CategoryTheory.Functor.map_comp] at h
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor_mapIso,
    ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor_mapIso]
  exact h.symm
end SerrePositivity.InfinityCategories.Project.DerivedCategories
