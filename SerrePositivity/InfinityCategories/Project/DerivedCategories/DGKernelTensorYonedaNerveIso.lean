module
public import SerrePositivity.DifferentialGraded.Morita.CriterionPerfTriangulated
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleExtensionYonedaStrict
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleStrictNatTransIso
/-!
概要：任意の加群値 dg 関手を Yoneda 後の同じ kernel tensor と実関手同型で比較する。
方針：既存の tensor・Yoneda の厳密同定と対角右単位の全 Hom 自然性を使う。
規約：Small 仮定は二つの係数 dg 圏だけに置く。
使われ方：前三角始域から全加群圏への任意の dg 関手の完全性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D C : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R C D)

lemma dgKernelTensorYoneda_naturality (d d' : D) :
    ((_root_.SerrePositivity.DifferentialGraded.dgYoneda R D).comp (_root_.SerrePositivity.DifferentialGraded.Morita.kernelTensor R D C P)).map d d' ≫
      _root_.SerrePositivity.DifferentialGraded.moduleHomPostcompose R C _ _ _ (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.rightUnitIso R C D P d').hom =
    P.toFunctor.map d d' ≫
      _root_.SerrePositivity.DifferentialGraded.moduleHomPrecompose R C _ _ _ (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.rightUnitIso R C D P d).hom := by
  have hh : ∀ (F G : _root_.SerrePositivity.DifferentialGraded.DGFunctor R D (_root_.SerrePositivity.DifferentialGraded.RightModule R C)), F = G →
      HEq (F.map d d') (G.map d d') := by
    intro F G h
    cases h
    rfl
  have hm0 := hh ((_root_.SerrePositivity.DifferentialGraded.dgYoneda R D).comp (_root_.SerrePositivity.DifferentialGraded.Morita.kernelTensor R D C P))
    (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.compose R C D D P (_root_.SerrePositivity.DifferentialGraded.Bimodule.diagonal R D)).toFunctor
    (_root_.SerrePositivity.DifferentialGraded.Morita.criterionPerfYonedaTensor_eq R D C P)
  have hm := eq_of_heq hm0
  rw [hm]
  exact _root_.SerrePositivity.DifferentialGraded.BimoduleTensor.rightUnitIso_naturality R C D P d d'

def dgKernelTensorYonedaStrict :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans ((dgYoneda R D).comp (Morita.kernelTensor R D C P)) P.toFunctor :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleStrictNatTransOfHomNaturality R C
    (fun d => (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.rightUnitIso R C D P d).hom)
    (dgKernelTensorYoneda_naturality R D C P)

def dgKernelTensorYonedaCompositeIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, v, max (u + 1) v} R D).comp (dgYoneda R D)) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R D C P))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, v, max (u + 1) v} R D).comp P.toFunctor)) := by
  let L := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, v, max (u + 1) v} R D
  have he : (L.comp (_root_.SerrePositivity.DifferentialGraded.dgYoneda R D)).comp (_root_.SerrePositivity.DifferentialGraded.Morita.kernelTensor R D C P) =
      L.comp ((_root_.SerrePositivity.DifferentialGraded.dgYoneda R D).comp (_root_.SerrePositivity.DifferentialGraded.Morita.kernelTensor R D C P)) := by
    apply EnrichedFunctor.ext (_root_.SerrePositivity.DifferentialGraded.Complex R) (fun _ => rfl)
    intro x y
    simp only [EnrichedFunctor.comp_map, Category.assoc, eqToHom_refl, Category.comp_id]
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp, he]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorIsoOfStrictNatTrans R C
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPrecomp L (dgKernelTensorYonedaStrict R D C P))
    (fun x => (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.rightUnitIso R C D P x.label.down).hom)
    (fun _ => rfl) (fun _ => inferInstance)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
