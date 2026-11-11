module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelTargetModelAugmentation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelQuasiIsoComparison
/-!
概要：指定出力模型の実 kernel 作用と graph 延長の合成を、元の一般作用へ比較する。
方針：同じ全 Hom 自然な augmentation の準同型性と、実導来合成を使う。
規約：原 kernel の平坦性・射影性は不要。指定模型だけに右相対 K-flat 性を要求する。
使われ方：一般 kernel の出力模型移送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
variable (R : Type u) [CommRing R] (D C E : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E)
  (P : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D) (Q : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R C D)
  (q : Q ⟶ (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.middleRightRestrictionFunctor R E C D F).obj P)
/-- 指定右相対 K-flat 模型と準同値の graph による実作用は、元の同じ kernel の作用と同型。 -/
def dgKernelDerivedInfinity_targetModelIso (hF : _root_.SerrePositivity.DifferentialGraded.QuasiEquivalence F)
    (hQ : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R C D (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R C D Q))
    (hq : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.quasiIso R C D q) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D C (BimoduleCategory.underlying R C D Q) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleExtensionInfinity R C E F)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D E (BimoduleCategory.underlying R E D P)) := by
  have a := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_graphIso R C E F).symm
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D C (BimoduleCategory.underlying R C D Q))
  have b := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R D C E
    (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R C D Q) (_root_.SerrePositivity.DifferentialGraded.functorGraph R C E F) hQ
  have c := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_mapIso_of_quasiIso R D E
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTargetModelAugmentation R D C E F P Q q)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTargetModelAugmentation_quasiIso R D C E F P Q q hF hQ hq)
  exact a ≪≫ b ≪≫ c
end SerrePositivity.InfinityCategories.Project.DerivedCategories
