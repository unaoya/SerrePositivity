module
public import SerrePositivity.InfinityCategories.Derived.DGBimoduleIsoNerveAlgebra
public import SerrePositivity.InfinityCategories.Derived.DGBimoduleStrictNatTransAlgebra
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence
public import SerrePositivity.InfinityCategories.Derived.DGStrictNerveWhiskerHom
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve
/-- 端点 dg 関手と閉零成分の同じ値は、厳密 dg 変換の値を型付きで保つ。 -/
lemma dgStrictNatTrans_heq_of_functor_eq {S : Type*} [CommRing S] {X Y : Type*}
    [DGCategory S X] [DGCategory S Y] {F G F' G' : DGFunctor S X Y}
    (η : StrictNatTrans F G) (θ : StrictNatTrans F' G') (hF : F = F') (hG : G = G')
    (happ : ∀ x, HEq (η.app x) (θ.app x)) : HEq η θ := by
  subst F' G'
  apply heq_of_eq
  apply dgStrictNatTrans_ext
  intro x
  exact eq_of_heq (happ x)
variable (R : Type u) [CommRing R] (E F : Type v) (C : Type (max (u + 1) v))
  [DGCategory R E] [Small.{u} E] [DGCategory R F] [Small.{u} F] [DGCategory R C]
/-- 任意の加群値 dg 関手の通常 kernel 後合成は、同じ双加群合成と厳密に一致。 -/
lemma dgKernelTensor_postcomp_bimodule_eq (P : Bimodule R E C) (Q : Bimodule R F E) :
    P.toFunctor.comp (Morita.kernelTensor R E F Q) =
      (BimoduleTensor.compose R F E C Q P).toFunctor := by
  apply EnrichedFunctor.ext (Complex R)
    (F := P.toFunctor.comp (Morita.kernelTensor R E F Q))
    (G := (BimoduleTensor.compose R F E C Q P).toFunctor) (fun _ => rfl)
  intro x y
  change (P.toFunctor.map x y ≫ (Morita.kernelTensor R E F Q).map _ _) ≫ 𝟙 _ = _
  rw [Category.comp_id]
  apply moduleHom_ext
  intro f
  rw [Category.assoc, Morita.kernelTensor_map_π R E F Q]
  exact (BimoduleTensor.compose_leftMap_π R F E C Q P x y f).symm
/-- 同じ composeMap の閉零成分は、通常 kernel 関手による元の閉射の像。 -/
lemma dgKernelTensor_postcomp_closed_map {P P' : BimoduleCategory R E C}
    (η : P ⟶ P') (Q : BimoduleCategory R F E) (x : C) :
    (BimoduleCategory.evaluation R F C x).map
      (BimoduleTensor.composeMap R F E C (𝟙 Q) η) =
    (Morita.kernelTensor R E F (BimoduleCategory.underlying R F E Q)).onClosed.map
      ((BimoduleCategory.evaluation R E C x).map η) := by
  apply moduleMorphism_ext
  intro f
  have he := BimoduleTensor.composeMap_value_eval R F E C (𝟙 Q) η f x
  dsimp only [BimoduleCategory.valueEvaluation, CategoryTheory.Functor.comp_map] at he
  rw [he, Morita.kernelTensor_map_eval]
  unfold BimoduleTensor.composeValueMap BalancedTensor.rightTensorMap
    BalancedTensor.rightTensorFunctor
  rw [CategoryTheory.Functor.map_id]
  rfl
/-- 同じ composeMap の厳密変換は、通常 kernel 関手による後合成そのもの。 -/
lemma dgKernelTensor_postcomp_strict_heq {P P' : BimoduleCategory R E C}
    (η : P ⟶ P') (Q : BimoduleCategory R F E) :
    HEq (dgBimoduleMapStrictNatTrans R F C (BimoduleTensor.composeMap R F E C (𝟙 Q) η))
      (dgStrictNatTransPostcomp (dgBimoduleMapStrictNatTrans R E C η)
        (Morita.kernelTensor R E F (BimoduleCategory.underlying R F E Q))) := by
  apply dgStrictNatTrans_heq_of_functor_eq _ _
    (dgKernelTensor_postcomp_bimodule_eq R E F C (BimoduleCategory.underlying R E C P)
      (BimoduleCategory.underlying R F E Q)).symm
    (dgKernelTensor_postcomp_bimodule_eq R E F C (BimoduleCategory.underlying R E C P')
      (BimoduleCategory.underlying R F E Q)).symm
  intro x
  apply heq_of_eq
  apply Subtype.ext
  change (closedHomEquiv R (RightModule R F) _ _
      ((BimoduleCategory.evaluation R F C x).map
        (BimoduleTensor.composeMap R F E C (𝟙 Q) η))).val = _
  rw [dgKernelTensor_postcomp_closed_map R E F C η Q x]
  exact congrArg Subtype.val (DGFunctor.closedHomEquiv_map
    (Morita.kernelTensor R E F (BimoduleCategory.underlying R F E Q))
    ((BimoduleCategory.evaluation R E C x).map η))
/-- 端点を揃えた同じ厳密変換は、その全関手射の実 nerve 像も型付きで保つ。 -/
lemma dgStrictNatTransNerveHom_heq_of_functor_eq {S : Type*} [CommRing S] {X Y : Type v}
    [DGCategory S X] [DGCategory S Y] {F G F' G' : DGFunctor S X Y}
    (η : StrictNatTrans F G) (θ : StrictNatTrans F' G') (hF : F = F') (hG : G = G')
    (hη : HEq η θ) : HEq (dgStrictNatTransNerveHom S X Y η)
      (dgStrictNatTransNerveHom S X Y θ) := by
  subst F' G'
  cases eq_of_heq hη
  rfl
/-- 同じ composeMap の実 nerve 像は、通常 kernel 作用による全関手射の後合成。 -/
lemma dgKernelTensor_postcomp_nerve_hom_heq {P P' : BimoduleCategory R E C}
    (η : P ⟶ P') (Q : BimoduleCategory R F E) :
    HEq ((dgBimoduleFunctorHomFunctor R F C).map
      (BimoduleTensor.composeMap R F E C (𝟙 Q) η))
      ((SSet.mapHomotopyCategory ((ihom (dgNerve R C)).map
        (dgNerve.map (Morita.kernelTensor R E F (BimoduleCategory.underlying R F E Q))))).map
          ((dgBimoduleFunctorHomFunctor R E C).map η)) := by
  have h1 := dgStrictNatTransNerveHom_heq_of_functor_eq
    (dgBimoduleMapStrictNatTrans R F C (BimoduleTensor.composeMap R F E C (𝟙 Q) η))
    (dgStrictNatTransPostcomp (dgBimoduleMapStrictNatTrans R E C η)
      (Morita.kernelTensor R E F (BimoduleCategory.underlying R F E Q)))
    (dgKernelTensor_postcomp_bimodule_eq R E F C (BimoduleCategory.underlying R E C P)
      (BimoduleCategory.underlying R F E Q)).symm
    (dgKernelTensor_postcomp_bimodule_eq R E F C (BimoduleCategory.underlying R E C P')
      (BimoduleCategory.underlying R F E Q)).symm
    (dgKernelTensor_postcomp_strict_heq R E F C η Q)
  exact h1.trans (dgStrictNatTransNerveHom_postcomp_heq R C (RightModule R E) (RightModule R F)
    (dgBimoduleMapStrictNatTrans R E C η)
    (Morita.kernelTensor R E F (BimoduleCategory.underlying R F E Q)))
end SerrePositivity.InfinityCategories
