module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.KernelComparisons.DGKernelDerivedCompositionHomNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.SimplicialFunctors.FunctorHomPrecompIdentityMorphism
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.KernelComparisons.DGKernelSourceGraphComparison
/-!
概要：元の出力模型比較を、その指定射と可換四角形で照合する。
方針：同じ全関手射の前合成と tensor 評価、元の合成比較の自然性を使う。
規約：指定比較・計算上限を変更しない。使われ方：一般 cell 模型の整合性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet DifferentialGraded MonoidalClosed
variable (R : Type u) [CommRing R] (D C E : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E)
lemma dgKernelDerivedInfinity_comp_graph_hom_naturality
    {Q Q' : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R C D} (b : Q ⟶ Q')
    (hQ : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R C D (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R C D Q))
    (hQ' : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R C D (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R C D Q')) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R D C E
        (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R C D Q) (_root_.SerrePositivity.DifferentialGraded.functorGraph R C E F) hQ).hom ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R D E).map
        (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeMap R E C D
          (𝟙 (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R E C (_root_.SerrePositivity.DifferentialGraded.functorGraph R C E F))) b) =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D C (BimoduleCategory.underlying R C D Q))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D C (BimoduleCategory.underlying R C D Q'))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R C E (functorGraph R C E F))
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R D C).map b) ≫
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R D C E
      (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R C D Q') (_root_.SerrePositivity.DifferentialGraded.functorGraph R C E F) hQ').hom := by
  have hh := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compIso_hom_naturality R D C E b
    (𝟙 (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R E C (_root_.SerrePositivity.DifferentialGraded.functorGraph R C E F))) hQ hQ'
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorGraph_rightRelativeKFlat R C E F)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorGraph_rightRelativeKFlat R C E F)
  rw [CategoryTheory.Functor.map_id] at hh
  have hid : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R C E
        (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E C (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R E C (_root_.SerrePositivity.DifferentialGraded.functorGraph R C E F))))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R C E
        (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E C (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R E C (_root_.SerrePositivity.DifferentialGraded.functorGraph R C E F))))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D C (BimoduleCategory.underlying R C D Q'))
      (𝟙 ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R C E).obj
        (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R E C (_root_.SerrePositivity.DifferentialGraded.functorGraph R C E F)))) = 𝟙 _ :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp_identity _ _
  rw [hid, Category.comp_id] at hh
  exact hh
end SerrePositivity.InfinityCategories.Project.DerivedCategories
