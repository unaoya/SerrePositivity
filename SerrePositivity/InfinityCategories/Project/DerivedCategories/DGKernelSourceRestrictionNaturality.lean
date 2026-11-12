module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelSourceGraphInfinityNaturality
public import
  SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelSourceGraphDerivedBimoduleNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelSourceRestrictionInfinity
/-!
概要：元の始域制限比較そのものの、任意の双加群射に対する自然性を証明する。
方針：元の source graph 比較と元の graph 合成双加群同型の二つの四角形を接続する。
規約：原 kernel の平坦性を要求しない。使われ方：cell 入力比較の全関手整合性。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet DifferentialGraded MonoidalClosed
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] (C D E : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C] [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C D)
lemma dgKernelDerivedInfinity_sourceRestrictionIso_hom_naturality
    {P0 P1 : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D} (g : P0 ⟶ P1) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_sourceRestrictionIso R C D E F
        (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D P0)).hom ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R C E).map
        ((_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.middleLeftRestrictionFunctor R E D C F).map g) =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D E (BimoduleCategory.underlying R E D P0))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D E (BimoduleCategory.underlying R E D P1))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleExtensionInfinity R C D F)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R D E).map g) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_sourceRestrictionIso R C D E F
        (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D P1)).hom := by
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_trans_hom_square
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_sourceGraphIso R C D E F
      (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D P0))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_sourceGraphIso R C D E F
      (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D P1))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_bimoduleIso R C E
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelSourceGraphBimoduleIso R C D E F (BimoduleCategory.underlying R E D P0)))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_bimoduleIso R C E
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelSourceGraphBimoduleIso R C D E F (BimoduleCategory.underlying R E D P1)))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D E (BimoduleCategory.underlying R E D P0))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D E (BimoduleCategory.underlying R E D P1))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleExtensionInfinity R C D F)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R D E).map g))
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R C E).map
      (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeMap R E D C g
        (𝟙 (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R D C (_root_.SerrePositivity.DifferentialGraded.functorGraph R C D F)))))
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R C E).map
      ((_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.middleLeftRestrictionFunctor R E D C F).map g))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_sourceGraphIso_hom_naturality R C D E F g)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_sourceGraphBimoduleIso_hom_naturality R C D E F g)
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
