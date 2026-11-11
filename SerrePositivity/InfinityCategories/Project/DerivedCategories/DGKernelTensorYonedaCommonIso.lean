module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelTensorYonedaNerveIso
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStrictNatTransCommonIso
/-!
概要：独立の係数圏宇宙における tensor・Yoneda の比較を共通 nerve の実関手同型にする。
方針：対角右単位の既存の全 Hom 自然性を厳密自然変換と共通宇宙比較に接続する。
規約：全加群圏の Small 仮定を使わず、既存の同一宇宙版を変更しない。
使われ方：前三角始域から全加群圏への混在宇宙版の完全性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w t
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) (C : Type w)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R C D)

lemma dgKernelTensorYoneda_naturality_general (d d' : D) :
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
  rw [eq_of_heq hm0]
  exact _root_.SerrePositivity.DifferentialGraded.BimoduleTensor.rightUnitIso_naturality R C D P d d'

def dgKernelTensorYonedaStrict_general :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans ((dgYoneda R D).comp (Morita.kernelTensor R D C P)) P.toFunctor :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleStrictNatTransOfHomNaturality R C
    (fun d => (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.rightUnitIso R C D P d).hom)
    (dgKernelTensorYoneda_naturality_general R D C P)

def dgKernelTensorYonedaCommonIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCommonMap.{u, v, max (u + 1) v, max (u + 1) v w t} (dgYoneda R D) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCommonMap.{u, max (u + 1) v, max (u + 1) w, max (u + 1) v w t}
          (_root_.SerrePositivity.DifferentialGraded.Morita.kernelTensor R D C P))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCommonMap.{u, v, max (u + 1) w, max (u + 1) v w t} P.toFunctor) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCommonMap_comp.{u, v, max (u + 1) v, max (u + 1) w, t}]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransCommonFunctorIso.{u, v, max (u + 1) w, max (u + 1) v w t}
    (dgKernelTensorYonedaStrict_general R D C P)
    (fun d => _root_.SerrePositivity.DifferentialGraded.BimoduleTensor.rightUnitIso R C D P d) (fun _ => rfl)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
