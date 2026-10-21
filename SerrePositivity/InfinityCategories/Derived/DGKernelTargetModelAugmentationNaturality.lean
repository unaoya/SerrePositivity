module
public import SerrePositivity.InfinityCategories.Derived.DGKernelTargetModelInfinity
public import SerrePositivity.InfinityCategories.Derived.DGKernelPostcompBimodule
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve MonoidalClosed
variable (R : Type u) [CommRing R] (D C E : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R C] [Small.{u} C]
  [DGCategory R E] [Small.{u} E] (F : DGFunctor R C E)
omit [Small.{u} D] in
lemma dgKernelTargetModelAugmentation_naturality
    {P P' : BimoduleCategory R E D} {Q Q' : BimoduleCategory R C D}
    (q : Q ⟶ (BimoduleCategory.middleRightRestrictionFunctor R E C D F).obj P)
    (q' : Q' ⟶ (BimoduleCategory.middleRightRestrictionFunctor R E C D F).obj P')
    (a : P ⟶ P') (b : Q ⟶ Q')
    (h : b ≫ q' = q ≫ (BimoduleCategory.middleRightRestrictionFunctor R E C D F).map a) :
    BimoduleTensor.composeMap R E C D
        (𝟙 (BimoduleCategory.of R E C (functorGraph R C E F))) b ≫
      dgKernelTargetModelAugmentation R D C E F P' Q' q' =
    dgKernelTargetModelAugmentation R D C E F P Q q ≫ a := by
  apply BimoduleCategory.hom_ext
  intro d
  simp only [CategoryTheory.Functor.map_comp]
  have hm : (BimoduleCategory.evaluation R E D d).map
      (BimoduleTensor.composeMap R E C D
        (𝟙 (BimoduleCategory.of R E C (functorGraph R C E F))) b) =
      (dgModuleExtension R C E F).onClosed.map
        ((BimoduleCategory.evaluation R C D d).map b) := by
    apply moduleMorphism_ext R E
    intro e
    change (BimoduleCategory.valueEvaluation R E D e d).map
      (BimoduleTensor.composeMap R E C D
        (𝟙 (BimoduleCategory.of R E C (functorGraph R C E F))) b) = _
    rw [BimoduleTensor.composeMap_value_eval, dgModuleExtension_map_eval]
    unfold BimoduleTensor.composeValueMap BalancedTensor.rightTensorMap
      BalancedTensor.rightTensorFunctor
    rw [CategoryTheory.Functor.map_id]
    rfl
  rw [hm, dgKernelTargetModelAugmentation_component,
    dgKernelTargetModelAugmentation_component]
  have hd := congrArg (fun k => (BimoduleCategory.evaluation R C D d).map k) h
  simp only [CategoryTheory.Functor.map_comp] at hd
  change b.val d ≫ q'.val d = q.val d ≫ (moduleRestriction R C E F.op).map (a.val d) at hd
  exact (dgModuleExtensionRestrictionAdjunction R C E F).homEquiv_naturality_right_square
    (b.val d) (q'.val d) (q.val d) (a.val d) hd
end SerrePositivity.InfinityCategories
