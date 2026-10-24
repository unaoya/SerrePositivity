module
public import SerrePositivity.InfinityCategories.Derived.DGKernelTensorYonedaNerveIso
public import SerrePositivity.InfinityCategories.Derived.DGStrictNatTransCommonIso
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (D : Type v) (C : Type w)
  [DGCategory R D] [Small.{u} D] [DGCategory R C] [Small.{u} C]
  (P : Bimodule R C D)

lemma dgKernelTensorYoneda_naturality_general (d d' : D) :
    ((dgYoneda R D).comp (Morita.kernelTensor R D C P)).map d d' ≫
      moduleHomPostcompose R C _ _ _ (BimoduleTensor.rightUnitIso R C D P d').hom =
    P.toFunctor.map d d' ≫
      moduleHomPrecompose R C _ _ _ (BimoduleTensor.rightUnitIso R C D P d).hom := by
  have hh : ∀ (F G : DGFunctor R D (RightModule R C)), F = G →
      HEq (F.map d d') (G.map d d') := by
    intro F G h
    cases h
    rfl
  have hm0 := hh ((dgYoneda R D).comp (Morita.kernelTensor R D C P))
    (BimoduleTensor.compose R C D D P (Bimodule.diagonal R D)).toFunctor
    (Morita.criterionPerfYonedaTensor_eq R D C P)
  rw [eq_of_heq hm0]
  exact BimoduleTensor.rightUnitIso_naturality R C D P d d'

def dgKernelTensorYonedaStrict_general :
    StrictNatTrans ((dgYoneda R D).comp (Morita.kernelTensor R D C P)) P.toFunctor :=
  dgModuleStrictNatTransOfHomNaturality R C
    (fun d => (BimoduleTensor.rightUnitIso R C D P d).hom)
    (dgKernelTensorYoneda_naturality_general R D C P)

def dgKernelTensorYonedaCommonIso :
    FunctorIso
      (dgNerveCommonMap.{u, v, max (u + 1) v, max (u + 1) v w t} (dgYoneda R D) ≫
        dgNerveCommonMap.{u, max (u + 1) v, max (u + 1) w, max (u + 1) v w t}
          (Morita.kernelTensor R D C P))
      (dgNerveCommonMap.{u, v, max (u + 1) w, max (u + 1) v w t} P.toFunctor) := by
  rw [dgNerveCommonMap_comp.{u, v, max (u + 1) v, max (u + 1) w, t}]
  exact dgStrictNatTransCommonFunctorIso.{u, v, max (u + 1) w, max (u + 1) v w t}
    (dgKernelTensorYonedaStrict_general R D C P)
    (fun d => BimoduleTensor.rightUnitIso R C D P d) (fun _ => rfl)

end SerrePositivity.InfinityCategories
