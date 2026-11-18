module

public import SerrePositivity.AlgebraicGeometry.FrobeniusAugmentedRingCoefficients
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
概要：アフィン間の元の平坦全射から、実際の Γ の Frobenius 係数の Čech 完全性を得る。
方針：既存のアフィン忠実平坦性の判定と環の係数の完全性をつなぐ。
規約：非アフィン基底の大域切断の平坦性を仮定しない。
使われ方：同じアフィン nerve とタプル複体との比較。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry Opposite
universe u
variable {Y S : Scheme.{u}} (f : Y ⟶ S) [IsAffine Y] [IsAffine S]

set_option backward.isDefEq.respectTransparency false in
/-- アフィン間の同じ平坦全射の Γ の、元の Frobenius 係数の増大 Čech は完全。 -/
theorem affineGammaFrobeniusCech_exact_of_flat_surjective [Flat f] [Surjective f]
    (p : ℕ) (hp : p.Prime) (hS : (p : Γ(S, ⊤)) = 0) :
    SerrePositivity.Cech.AugmentedRingCechExact
      (frobeniusAugmentedRingCoefficients (Arrow.mk (Scheme.Γ.map f.op)) p hp hS) := by
  have hf : (Scheme.Γ.map f.op).hom.FaithfullyFlat := by
    rw [Scheme.Γ_map_op]
    exact (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine f).mp
      ⟨inferInstance, inferInstance⟩
  let B : Under (Scheme.Γ.obj (op S)) := Under.mk (Scheme.Γ.map f.op)
  haveI : Module.FaithfullyFlat (Scheme.Γ.obj (op S)) B.right := hf
  exact frobeniusAugmentedRingCoefficients_exact_of_faithfullyFlat B p hp hS

end SerrePositivity.AlgebraicGeometry
