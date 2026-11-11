module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGBimoduleIsoNerveAlgebra
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGBimoduleStrictNatTransAlgebra
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStrictNerveWhiskerHom
public import SerrePositivity.DifferentialGraded.Morita.CoherenceCompositionKernel
public import SerrePositivity.DifferentialGraded.Tensor.Bimodule.Actions
/-!
概要：通常 kernel 後合成と双加群合成を、dg 関手・厳密変換・実全関手射で照合する。
方針：主 Hom の評価式、同じ閉零成分、元の全ホモトピーの後合成式を使う。
規約：原 Hom の平坦性と入力圏の Small 性は要求しない。使われ方：kernel の coherence。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet DifferentialGraded
/-- 端点 dg 関手と閉零成分の同じ値は、厳密 dg 変換の値を型付きで保つ。 -/
lemma dgStrictNatTrans_heq_of_functor_eq {S : Type*} [CommRing S] {X Y : Type*}
    [_root_.SerrePositivity.DifferentialGraded.DGCategory S X] [_root_.SerrePositivity.DifferentialGraded.DGCategory S Y] {F G F' G' : _root_.SerrePositivity.DifferentialGraded.DGFunctor S X Y}
    (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G) (θ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F' G') (hF : F = F') (hG : G = G')
    (happ : ∀ x, HEq (η.app x) (θ.app x)) : HEq η θ := by
  subst F' G'
  apply heq_of_eq
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTrans_ext
  intro x
  exact eq_of_heq (happ x)
variable (R : Type u) [CommRing R] (E F : Type v) (C : Type (max (u + 1) v))
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E] [_root_.SerrePositivity.DifferentialGraded.DGCategory R F] [Small.{u} F] [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
/-- 任意の加群値 dg 関手の通常 kernel 後合成は、同じ双加群合成と厳密に一致。 -/
lemma dgKernelTensor_postcomp_bimodule_eq (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R E C) (Q : _root_.SerrePositivity.DifferentialGraded.Bimodule R F E) :
    P.toFunctor.comp (_root_.SerrePositivity.DifferentialGraded.Morita.kernelTensor R E F Q) =
      (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.compose R F E C Q P).toFunctor := by
  apply EnrichedFunctor.ext (_root_.SerrePositivity.DifferentialGraded.Complex R)
    (F := P.toFunctor.comp (_root_.SerrePositivity.DifferentialGraded.Morita.kernelTensor R E F Q))
    (G := (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.compose R F E C Q P).toFunctor) (fun _ => rfl)
  intro x y
  change (P.toFunctor.map x y ≫ (_root_.SerrePositivity.DifferentialGraded.Morita.kernelTensor R E F Q).map _ _) ≫ 𝟙 _ = _
  rw [Category.comp_id]
  apply _root_.SerrePositivity.DifferentialGraded.moduleHom_ext
  intro f
  rw [Category.assoc, _root_.SerrePositivity.DifferentialGraded.Morita.kernelTensor_map_π R E F Q]
  exact (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.compose_leftMap_π R F E C Q P x y f).symm
/-- 同じ composeMap の閉零成分は、通常 kernel 関手による元の閉射の像。 -/
lemma dgKernelTensor_postcomp_closed_map {P P' : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E C}
    (η : P ⟶ P') (Q : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R F E) (x : C) :
    (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.evaluation R F C x).map
      (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeMap R F E C (𝟙 Q) η) =
    (_root_.SerrePositivity.DifferentialGraded.Morita.kernelTensor R E F (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R F E Q)).onClosed.map
      ((_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.evaluation R E C x).map η) := by
  apply _root_.SerrePositivity.DifferentialGraded.moduleMorphism_ext
  intro f
  have he := _root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeMap_value_eval R F E C (𝟙 Q) η f x
  dsimp only [_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.valueEvaluation, CategoryTheory.Functor.comp_map] at he
  rw [he, _root_.SerrePositivity.DifferentialGraded.Morita.kernelTensor_map_eval]
  unfold _root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeValueMap _root_.SerrePositivity.DifferentialGraded.BalancedTensor.rightTensorMap
    _root_.SerrePositivity.DifferentialGraded.BalancedTensor.rightTensorFunctor
  rw [CategoryTheory.Functor.map_id]
  rfl
/-- 同じ composeMap の厳密変換は、通常 kernel 関手による後合成そのもの。 -/
lemma dgKernelTensor_postcomp_strict_heq {P P' : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E C}
    (η : P ⟶ P') (Q : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R F E) :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleMapStrictNatTrans R F C (BimoduleTensor.composeMap R F E C (𝟙 Q) η))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleMapStrictNatTrans R E C η)
        (_root_.SerrePositivity.DifferentialGraded.Morita.kernelTensor R E F (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R F E Q))) := by
  apply dgStrictNatTrans_heq_of_functor_eq _ _
    (dgKernelTensor_postcomp_bimodule_eq R E F C (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E C P)
      (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R F E Q)).symm
    (dgKernelTensor_postcomp_bimodule_eq R E F C (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E C P')
      (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R F E Q)).symm
  intro x
  apply heq_of_eq
  apply Subtype.ext
  change (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv R (_root_.SerrePositivity.DifferentialGraded.RightModule R F) _ _
      ((_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.evaluation R F C x).map
        (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeMap R F E C (𝟙 Q) η))).val = _
  rw [dgKernelTensor_postcomp_closed_map R E F C η Q x]
  exact congrArg Subtype.val (_root_.SerrePositivity.DifferentialGraded.DGFunctor.closedHomEquiv_map
    (_root_.SerrePositivity.DifferentialGraded.Morita.kernelTensor R E F (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R F E Q))
    ((_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.evaluation R E C x).map η))
/-- 端点を揃えた同じ厳密変換は、その全関手射の実 nerve 像も型付きで保つ。 -/
lemma dgStrictNatTransNerveHom_heq_of_functor_eq {S : Type*} [CommRing S] {X Y : Type v}
    [_root_.SerrePositivity.DifferentialGraded.DGCategory S X] [_root_.SerrePositivity.DifferentialGraded.DGCategory S Y] {F G F' G' : _root_.SerrePositivity.DifferentialGraded.DGFunctor S X Y}
    (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G) (θ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F' G') (hF : F = F') (hG : G = G')
    (hη : HEq η θ) : HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom S X Y η)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom S X Y θ) := by
  subst F' G'
  cases eq_of_heq hη
  rfl
/-- 同じ composeMap の実 nerve 像は、通常 kernel 作用による全関手射の後合成。 -/
lemma dgKernelTensor_postcomp_nerve_hom_heq {P P' : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E C}
    (η : P ⟶ P') (Q : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R F E) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleFunctorHomFunctor R F C).map
      (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeMap R F E C (𝟙 Q) η))
      ((SSet.mapHomotopyCategory ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C)).map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R E F (BimoduleCategory.underlying R F E Q))))).map
          ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleFunctorHomFunctor R E C).map η)) := by
  have h1 := dgStrictNatTransNerveHom_heq_of_functor_eq
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleMapStrictNatTrans R F C (BimoduleTensor.composeMap R F E C (𝟙 Q) η))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleMapStrictNatTrans R E C η)
      (_root_.SerrePositivity.DifferentialGraded.Morita.kernelTensor R E F (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R F E Q)))
    (dgKernelTensor_postcomp_bimodule_eq R E F C (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E C P)
      (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R F E Q)).symm
    (dgKernelTensor_postcomp_bimodule_eq R E F C (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E C P')
      (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R F E Q)).symm
    (dgKernelTensor_postcomp_strict_heq R E F C η Q)
  exact h1.trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom_postcomp_heq R C (RightModule R E) (RightModule R F)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleMapStrictNatTrans R E C η)
    (_root_.SerrePositivity.DifferentialGraded.Morita.kernelTensor R E F (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R F E Q)))
end SerrePositivity.InfinityCategories.Project.DerivedCategories
