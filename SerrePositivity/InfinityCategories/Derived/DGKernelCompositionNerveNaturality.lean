module
public import SerrePositivity.InfinityCategories.Derived.DGKernelInverseAssociatorNaturality
public import SerrePositivity.InfinityCategories.Derived.DGKernelBimoduleMapWhisker
public import SerrePositivity.InfinityCategories.Derived.DGKernelCompositionNerveHom
public import SerrePositivity.InfinityCategories.Derived.FunctorHomTwoThreeTransport
/-!
概要：元の通常 kernel 合成比較 α の双加群射に対する二変数自然性を証明する。
方針：同じ逆結合子の自然性と二変数の実作用を、明示した全端点に沿って照合する。
規約：射の可逆性・原 Hom の平坦性を追加しない。使われ方：左単位と模型変更 coherence。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve MonoidalClosed
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] (D E F : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
  [DGCategory R F] [Small.{u} F]
private lemma source_eq (P : Bimodule R E D) (Q : Bimodule R F E) :
    dgNerve.map (Morita.kernelTensor R D E P) ≫ dgNerve.map (Morita.kernelTensor R E F Q) =
    dgNerve.map (BimoduleTensor.compose R F E (RightModule R D) Q
      (BimoduleTensor.compose R E D (RightModule R D) P
        (DGFunctor.id (RightModule R D)))).toFunctor := by
  rw [← dgNerve.map_comp, Morita.kernelTensorComposition_eq]
variable {P P' : BimoduleCategory R E D} {Q Q' : BimoduleCategory R F E}
local notation "P₀" => BimoduleCategory.underlying R E D P
local notation "P₁" => BimoduleCategory.underlying R E D P'
local notation "Q₀" => BimoduleCategory.underlying R F E Q
local notation "Q₁" => BimoduleCategory.underlying R F E Q'
/-- 元の通常合成比較 α は、任意の二つの閉零双加群射に対して全関手射として自然。 -/
lemma dgKernelTensorCompositionNerveIso_naturality_hom (f : P ⟶ P') (g : Q ⟶ Q') :
    (dgKernelTensorCompositionNerveIso R D E F P₀ Q₀).hom ≫
      (dgKernelTensorFunctorHomFunctor R D F).map (BimoduleTensor.composeMap R F E D g f) =
    (SSet.mapHomotopyCategory ((ihom (dgModuleNerve R D)).map
      (dgNerve.map (Morita.kernelTensor R E F Q₀)))).map
        ((dgKernelTensorFunctorHomFunctor R D E).map f) ≫
    (SSet.mapHomotopyCategory ((pre (dgNerve.map (Morita.kernelTensor R D E P₁))).app
      (dgModuleNerve R F))).map ((dgKernelTensorFunctorHomFunctor R E F).map g) ≫
      (dgKernelTensorCompositionNerveIso R D E F P₁ Q₁).hom := by
  have hc := dgKernelTensorCompositionNerveIso_hom_heq R D E F P₀ Q₀
  have hr := heq_of_eq (dgKernelTensorFunctorHomFunctor_map R D F
    (BimoduleTensor.composeMap R F E D g f))
  have hq := dgKernelTensorFunctorHomFunctor_postcomp_heq R D E F f Q₀
  have hd := dgKernelTensorFunctorHomFunctor_precomp_heq R D E F g P₁
  have ha := dgKernelTensorCompositionNerveIso_hom_heq R D E F P₁ Q₁
  have he := dgKernelInverseAssociatorNerve_naturality_factor R D E F f g
  exact functorHom_two_three_eq_of_heq
    (f := dgNerve.map (Morita.kernelTensor R D E P₀) ≫
      dgNerve.map (Morita.kernelTensor R E F Q₀))
    (g := dgNerve.map (Morita.kernelTensor R D F (BimoduleTensor.compose R F E D Q₀ P₀)))
    (h := dgNerve.map (Morita.kernelTensor R D E P₁) ≫
      dgNerve.map (Morita.kernelTensor R E F Q₀))
    (t := dgNerve.map (Morita.kernelTensor R D E P₁) ≫
      dgNerve.map (Morita.kernelTensor R E F Q₁))
    (k := dgNerve.map (Morita.kernelTensor R D F (BimoduleTensor.compose R F E D Q₁ P₁)))
    _ _ _ _ _ _ _ _ _ _
    (source_eq R D E F P₀ Q₀) rfl (source_eq R D E F P₁ Q₀)
    (source_eq R D E F P₁ Q₁) rfl hc hr hq hd ha he

end
end SerrePositivity.InfinityCategories
