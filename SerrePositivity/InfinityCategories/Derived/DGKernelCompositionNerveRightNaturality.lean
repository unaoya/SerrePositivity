module
public import SerrePositivity.InfinityCategories.Derived.DGKernelCompositionNerveNaturality
public import SerrePositivity.InfinityCategories.Derived.FunctorHomPostcompIdentityMap
/-!
概要：元の kernel 合成子の右変数自然性を、同じ通常比較と raw 経路で照合する。
方針：元の指定比較と射の値を保持し、全関手圏の実作用と可換四角形を使う。
規約：後続 kernel の平坦性・射の可逆性は要求しない。使われ方：模型変更の整合性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve MonoidalClosed
variable (R : Type u) [CommRing R] (D E K : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
  [DGCategory R K] [Small.{u} K]
lemma dgKernelTensorCompositionNerveIso_right_naturality
    (P : BimoduleCategory R E D) {Q0 Q1 : BimoduleCategory R K E} (g : Q0 ⟶ Q1) :
    (dgKernelTensorCompositionNerveIso R D E K
      (BimoduleCategory.underlying R E D P) (BimoduleCategory.underlying R K E Q0)).hom ≫
      (dgKernelTensorFunctorHomFunctor R D K).map
        (BimoduleTensor.composeMap R K E D g (𝟙 P)) =
    functorHomPrecomp
      (dgNerve.map (Morita.kernelTensor R E K (BimoduleCategory.underlying R K E Q0)))
      (dgNerve.map (Morita.kernelTensor R E K (BimoduleCategory.underlying R K E Q1)))
      (dgNerve.map (Morita.kernelTensor R D E (BimoduleCategory.underlying R E D P)))
      ((dgKernelTensorFunctorHomFunctor R E K).map g) ≫
    (dgKernelTensorCompositionNerveIso R D E K
      (BimoduleCategory.underlying R E D P) (BimoduleCategory.underlying R K E Q1)).hom := by
  have hi : (dgKernelTensorFunctorHomFunctor R D E).map (𝟙 P) =
      𝟙 (HomotopyCategory.mk (functorVertex (dgNerve.map
        (Morita.kernelTensor R D E (BimoduleCategory.underlying R E D P))))) :=
    (dgKernelTensorFunctorHomFunctor R D E).map_id P
  have hn := dgKernelTensorCompositionNerveIso_naturality_hom R D E K (𝟙 P) g
  rw [hi] at hn
  have hp : (SSet.mapHomotopyCategory ((ihom (dgModuleNerve R D)).map
      (dgNerve.map (Morita.kernelTensor R E K (BimoduleCategory.underlying R K E Q0))))).map
      (𝟙 (HomotopyCategory.mk (functorVertex (dgNerve.map
        (Morita.kernelTensor R D E (BimoduleCategory.underlying R E D P)))))) =
      𝟙 (HomotopyCategory.mk (functorVertex
        (dgNerve.map (Morita.kernelTensor R D E (BimoduleCategory.underlying R E D P)) ≫
          dgNerve.map (Morita.kernelTensor R E K (BimoduleCategory.underlying R K E Q0))))) :=
    functorHomPostcomp_identity _ _
  rw [hp] at hn
  let z : FunctorHom
      (dgNerve.map (Morita.kernelTensor R D E (BimoduleCategory.underlying R E D P)) ≫
        dgNerve.map (Morita.kernelTensor R E K (BimoduleCategory.underlying R K E Q0)))
      (dgNerve.map (Morita.kernelTensor R D K (BimoduleTensor.compose R K E D
        (BimoduleCategory.underlying R K E Q1) (BimoduleCategory.underlying R E D P)))) :=
    functorHomPrecomp
      (dgNerve.map (Morita.kernelTensor R E K (BimoduleCategory.underlying R K E Q0)))
      (dgNerve.map (Morita.kernelTensor R E K (BimoduleCategory.underlying R K E Q1)))
      (dgNerve.map (Morita.kernelTensor R D E (BimoduleCategory.underlying R E D P)))
      ((dgKernelTensorFunctorHomFunctor R E K).map g) ≫
    (dgKernelTensorCompositionNerveIso R D E K
      (BimoduleCategory.underlying R E D P) (BimoduleCategory.underlying R K E Q1)).hom
  exact hn.trans (Category.id_comp z)
end SerrePositivity.InfinityCategories
