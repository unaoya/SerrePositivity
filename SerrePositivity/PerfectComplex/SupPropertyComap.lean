module

public import SerrePositivity.PerfectComplex.SupProperty
public import SerrePositivity.PerfectComplex.NormalizedLengthComap
public import Mathlib.Algebra.Algebra.RestrictScalars

/-! # 係数制限での正規化長さの上限の性質

任意の環準同型に沿った係数制限は HasSup を保つ。
小さい環上の有限生成部分加群を、その有限生成元の大きい環上の張る部分加群へ
拡大することで上限を比較する。環準同型の有限性や全射性は必要ない。
-/

@[expose] public section
universe u
namespace SerrePositivity.NormalizedLength
open scoped ENNReal

variable {Λ C : Type u} [CommRing Λ] [CommRing C] {J : Ideal Λ}
    {lam : NormalizedLength Λ J}

/-- 正規化長さの上限の性質は、任意の環準同型に沿った係数制限で保たれる。 -/
theorem HasSup.comap (hsup : lam.HasSup) (f : Λ →+* C) (J' : Ideal C)
    (hJ : J.map f ≤ J') : (lam.comap f J' hJ).HasSup := by
  intro M _ _ hM
  let : Algebra Λ C := f.toAlgebra
  let : Module Λ M := Module.compHom M f
  let : IsScalarTower Λ C M := IsScalarTower.of_compHom Λ C M
  have hMR : IsPowTorsion J M := IsPowTorsion.comap f hJ M hM
  change lam.len M = ⨆ (V : Submodule C M) (_ : V.FG), (lam.comap f J' hJ).len V
  refine le_antisymm ?_ ?_
  · rw [hsup M hMR]
    refine iSup₂_le fun N hN ↦ ?_
    let V : Submodule C M := Submodule.span C (N : Set M)
    let : Module Λ V := Module.compHom V f
    let g : N →ₗ[Λ] V :=
      { toFun := fun n ↦ ⟨n, Submodule.subset_span n.property⟩
        map_add' := fun _ _ ↦ Subtype.ext rfl
        map_smul' := fun _ _ ↦ Subtype.ext rfl }
    have hg : Function.Injective g := fun _ _ h ↦
      Subtype.ext (congrArg (fun v : V ↦ (v : M)) h)
    have hVR : IsPowTorsion J V := IsPowTorsion.comap f hJ V (hM.submodule V)
    have hle : lam.len N ≤ (lam.comap f J' hJ).len V :=
      lam.len_le_of_injective g hg hVR
    exact hle.trans (le_iSup₂_of_le V hN.span le_rfl)
  · refine iSup₂_le fun V _ ↦ ?_
    exact (lam.comap f J' hJ).len_le_of_injective V.subtype V.injective_subtype hM

end SerrePositivity.NormalizedLength
