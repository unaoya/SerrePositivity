module
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniverseCoefficientTensorIso
public import SerrePositivity.InfinityCategories.Stable.ExactFunctorChoice
/-!
概要：構成済みの共通宇宙の tensor 比較で、元の raw・導来係数脚へ完全性を移す。
方針：Yoneda 後の kernelTensor の完全性を実関手同型で戻し、実半自由分解と合成する。
規約：上流供給待ちの完全性は各実関手に関する明示入力として保持する。
使われ方：D-14 補足 2 の供給を G-1 e の元の係数脚へ差し替える接続口。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (hY : IsExactFunctor (dgGluingUniverseYoneda.{u, w, v} R D))
  (hT : IsExactFunctor
    (dgGluingUniverseNerveMap.{u, max (u + 1) w, max (u + 1) v, max (u + 1) v w}
      (Morita.kernelTensor R D C M)))
include hY hT
lemma dgGluingUniverseCoefficient_isExactFunctor_of_tensor :
    IsExactFunctor (dgGluingUniverseCoefficient R C D M) := by
  let := hY
  let := hT
  exact isExactFunctor_of_functorIso (dgGluingUniverseCoefficientTensorCompositeIso R C D M)

lemma dgGluingUniverseDerivedCoefficient_isExactFunctor_of_tensor
    (hL : IsExactFunctor (dgGluingUniverseModuleDerivedComparison.{u, v, w} R C)) :
    IsExactFunctor (dgGluingUniverseDerivedCoefficient R C D M) := by
  let := hL
  let := dgGluingUniverseCoefficient_isExactFunctor_of_tensor R C D M hY hT
  change IsExactFunctor (dgGluingUniverseCoefficient R C D M ≫
    dgGluingUniverseModuleDerivedComparison.{u, v, w} R C)
  infer_instance
end SerrePositivity.InfinityCategories
