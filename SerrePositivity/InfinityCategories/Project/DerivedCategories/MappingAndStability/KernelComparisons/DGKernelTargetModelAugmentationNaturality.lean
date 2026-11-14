module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.KernelComparisons.DGKernelTargetModelInfinity
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.KernelComparisons.DGKernelPostcompBimodule
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
omit [Small.{u} D] in
lemma dgKernelTargetModelAugmentation_naturality
    {P P' : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D} {Q Q' : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R C D}
    (q : Q ⟶ (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.middleRightRestrictionFunctor R E C D F).obj P)
    (q' : Q' ⟶ (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.middleRightRestrictionFunctor R E C D F).obj P')
    (a : P ⟶ P') (b : Q ⟶ Q')
    (h : b ≫ q' = q ≫ (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.middleRightRestrictionFunctor R E C D F).map a) :
    _root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeMap R E C D
        (𝟙 (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R E C (_root_.SerrePositivity.DifferentialGraded.functorGraph R C E F))) b ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTargetModelAugmentation R D C E F P' Q' q' =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTargetModelAugmentation R D C E F P Q q ≫ a := by
  apply _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.hom_ext
  intro d
  simp only [CategoryTheory.Functor.map_comp]
  have hm : (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.evaluation R E D d).map
      (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeMap R E C D
        (𝟙 (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R E C (_root_.SerrePositivity.DifferentialGraded.functorGraph R C E F))) b) =
      (_root_.SerrePositivity.DifferentialGraded.dgModuleExtension R C E F).onClosed.map
        ((_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.evaluation R C D d).map b) := by
    apply _root_.SerrePositivity.DifferentialGraded.moduleMorphism_ext R E
    intro e
    change (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.valueEvaluation R E D e d).map
      (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeMap R E C D
        (𝟙 (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R E C (_root_.SerrePositivity.DifferentialGraded.functorGraph R C E F))) b) = _
    rw [_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeMap_value_eval, _root_.SerrePositivity.DifferentialGraded.dgModuleExtension_map_eval]
    unfold _root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeValueMap _root_.SerrePositivity.DifferentialGraded.BalancedTensor.rightTensorMap
      _root_.SerrePositivity.DifferentialGraded.BalancedTensor.rightTensorFunctor
    rw [CategoryTheory.Functor.map_id]
    rfl
  rw [hm, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTargetModelAugmentation_component,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTargetModelAugmentation_component]
  have hd := congrArg (fun k => (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.evaluation R C D d).map k) h
  simp only [CategoryTheory.Functor.map_comp] at hd
  change b.val d ≫ q'.val d = q.val d ≫ (_root_.SerrePositivity.DifferentialGraded.moduleRestriction R C E F.op).map (a.val d) at hd
  exact (_root_.SerrePositivity.DifferentialGraded.dgModuleExtensionRestrictionAdjunction R C E F).homEquiv_naturality_right_square
    (b.val d) (q'.val d) (q.val d) (a.val d) hd
end SerrePositivity.InfinityCategories.Project.DerivedCategories
