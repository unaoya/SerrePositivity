module
public import
  SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleResolutionChangeIdentityNerveProjection
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorHomLiftedSquare
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleResolutionPrecompInfinity
/-!
概要：元の入力分解の対象宇宙を保ち、同じ厳密変換の全関手正方形を構成する。
方針：既存の上げ下げと nerve の全前後合成を、同じ射の型付き等式で照合する。
規約：指定同値の逆を変更しない。使われ方：元の指定入力比較の自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet DifferentialGraded MonoidalClosed
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (E : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
  (F G : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C (_root_.SerrePositivity.DifferentialGraded.RightModule R E))
  (a : ∀ x, ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (F.obj x) ⟶
    ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (G.obj x))
  (hs : ∀ x, _root_.SerrePositivity.DifferentialGraded.moduleDegreewiseSurjective R E (a x))
  (hq : ∀ x, _root_.SerrePositivity.DifferentialGraded.moduleQuasiIso R E (a x))
  (ha : ∀ x y, (F.comp (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R E))).map x y ≫
    eHomWhiskerLeft (_root_.SerrePositivity.DifferentialGraded.Complex R) (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (F.obj x)) (a y) =
    (G.comp (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R E))).map x y ≫
      eHomWhiskerRight (_root_.SerrePositivity.DifferentialGraded.Complex R) (a x)
        (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (G.obj y)))
def dgModuleResolutionLiftedInputFunctor :
    DGFunctor R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{max (u + 1) v, max (u + 1) v} C) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{max (u + 1)
      v, max (u + 1) v} (_root_.SerrePositivity.DifferentialGraded.RightModule R E)) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R C).comp (F.comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u,
    max (u + 1) v, max (u + 1) v} R (_root_.SerrePositivity.DifferentialGraded.RightModule R E)))
def dgModuleResolutionChangeIdentityLiftedNatTrans : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans
  (dgModuleResolutionLiftedInputFunctor R C E F) (dgModuleResolutionLiftedInputFunctor R C E G) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPrecomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R C)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeIdentityOriginalNatTrans R C E F G a ha)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R (RightModule R E)))
lemma dgModuleResolutionChangeIdentity_lifted_original_nerve_heq :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{max (u + 1) v, max (u + 1) v} C)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{max (u + 1) v, max (u + 1) v} (RightModule R E))
        (dgModuleResolutionChangeIdentityLiftedNatTrans R C E F G a ha))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v,
        max (u + 1) v} R (RightModule R E)))) ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map G) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R (RightModule R E))))
            (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R C))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map G) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u,
          max (u + 1) v, max (u + 1) v} R (RightModule R E))) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R C
            (RightModule R E) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeIdentityOriginalNatTrans R C E F G a
              ha)))) := by
  have hp := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom_postcomp_heq
    (R := R) (C := C) (D := (RightModule R E)) (E := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{max (u + 1) v, max (u +
      1) v} (RightModule R E))) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeIdentityOriginalNatTrans R C E F G a
        ha) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R (RightModule R E))
  have ht := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom_precomp_heq
    (R := R) (B := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{max (u + 1) v, max (u + 1) v} C)) (C := C) (D :=
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{max (u + 1) v, max (u + 1) v} (RightModule R E)))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R C)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeIdentityOriginalNatTrans R C E F G a ha)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R (RightModule R E)))
  have he := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHom_precomp_heq
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R C (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{max (u + 1) v, max (u + 1) v} (RightModule R
      E)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeIdentityOriginalNatTrans R C E F G
        a ha) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R (RightModule R E))))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map G) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max
      (u + 1) v, max (u + 1) v} R (RightModule R E))) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R C
        (RightModule R E) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionChangeIdentityOriginalNatTrans R C E F G a ha)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R (RightModule R
      E))) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp G (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R
        (RightModule R E))) hp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1)
          v} R C))
  exact ht.trans he
end SerrePositivity.InfinityCategories.Project.DerivedCategories
