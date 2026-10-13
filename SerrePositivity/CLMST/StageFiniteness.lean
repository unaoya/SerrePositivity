module

public import SerrePositivity.CLMST.StageAlgebra
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.RingTheory.Noetherian.Basic

/-! # CLMST の有限段の有限性と Noether 性

根の塔の有限自由性を基底変更し、`D_n=A_n⊗_A D` の D 上の有限性を証明する。
D が A 上有限なら A 上でも有限であり、D または A の Noether 性から
有限段の Noether 性が従う。零段については素数性を必要としない。
一般の有限段の局所性・次元は、このファイルの主張に含めない。
-/

@[expose] public noncomputable section
universe u
open scoped TensorProduct
namespace SerrePositivity.CLMST
open Section2

variable (A D : Type u) [CommRing A] [CommRing D] [Algebra A D]
    {h : ℕ} (t : Fin h → A) (p : ℕ)

/-- 零段は D と代数同型なので、D の Noether 性を継承する。素数性は不要。 -/
instance stage0IsNoetherian [IsNoetherianRing D] :
    IsNoetherianRing (StageAlgebra A D t p 0) :=
  isNoetherianRing_of_surjective D (StageAlgebra A D t p 0)
    (algebraMap D (StageAlgebra A D t p 0)) (stage0_algebraMap_surjective A D t p)

variable [Fact p.Prime]

/-- D が A 上有限なら、有限段の基底変更も A 上有限。 -/
instance stageAlgebraFiniteA [Module.Finite A D] (n : ℕ) :
    Module.Finite A (StageAlgebra A D t p n) := by
  have : Module.Finite A (TowerStage A t p n) := towerStage_finite A t p n
  exact inferInstanceAs (Module.Finite A (TowerStage A t p n ⊗[A] D))

/-- 有限段の基底変更は D 上有限。D の A 上の有限性や Noether 性は不要。 -/
instance stageAlgebraFiniteD (n : ℕ) : Module.Finite D (StageAlgebra A D t p n) := by
  have : Module.Finite A (TowerStage A t p n) := towerStage_finite A t p n
  let : Algebra D (TowerStage A t p n ⊗[A] D) := Algebra.TensorProduct.rightAlgebra
  let e : (D ⊗[A] TowerStage A t p n) ≃ₐ[D] StageAlgebra A D t p n :=
    Algebra.TensorProduct.commRight A D (TowerStage A t p n)
  exact Module.Finite.of_surjective e.toLinearMap e.surjective

/-- D が Noether 環なら、D 上有限なすべての段も Noether 環。 -/
instance stageAlgebraIsNoetherian [IsNoetherianRing D] (n : ℕ) :
    IsNoetherianRing (StageAlgebra A D t p n) :=
  IsNoetherianRing.of_finite D (StageAlgebra A D t p n)

/-- Noether 基底 A と有限な A 代数 D からも、有限段の Noether 性を供給できる。 -/
instance (priority := 90) stageAlgebraIsNoetherianOfBase
    [IsNoetherianRing A] [Module.Finite A D] (n : ℕ) :
    IsNoetherianRing (StageAlgebra A D t p n) :=
  IsNoetherianRing.of_finite A (StageAlgebra A D t p n)

end SerrePositivity.CLMST
