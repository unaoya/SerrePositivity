module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Module
public import SerrePositivity.CommutativeAlgebra.PowerTorsion.Basic

/-! # 一様なイデアル冪ねじれからの導来完備性

J の一つの冪が加群全体を消すとき、J の任意の元に関して導来完備となる。
元ごとに異なる消去冪を持つだけの条件とは区別する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.DerivedCompletion
open CategoryTheory

variable (R : Type u) [CommRing R]

/-- J の一つの冪で加群が消えれば、J の元 f の冪も消去するため導来 f 完備。 -/
theorem isModuleComplete_of_isPowTorsion (J : Ideal R) (f : R) (hf : f ∈ J)
    (M : ModuleCat.{u} R) (hM : IsPowTorsion J M) : IsModuleComplete R f M := by
  obtain ⟨N, hN⟩ := hM
  apply isModuleComplete_of_pow_smul_zero R f M N
  intro m
  exact hN (a := ⟨f ^ N, Ideal.pow_mem_pow hf N⟩) (x := m)

end SerrePositivity.DerivedCompletion
