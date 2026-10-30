module

public import SerrePositivity.CommutativeAlgebra.PowerTorsion.Basic
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.RingTheory.Finiteness.Cardinality

/-!
# 冪ねじれ加群の有限表示被覆

有限生成イデアル `J` の冪で消える有限生成加群は、同じ条件を満たす有限表示加群の
全射像である。有限自由加群からの全射を選び、`J^n` 倍の部分加群で割る。
この部分加群は有限生成なので、商は有限表示である。環の Noether 性は不要。
-/

@[expose] public section

universe u

namespace SerrePositivity

variable {R : Type u} [CommRing R]

/-- 有限自由加群を有限生成イデアル倍の部分加群で割った商は有限表示。
零化関係の部分加群が有限生成であることを示して、有限表示加群の商の定理を適用する。 -/
theorem finitePresentation_free_quotient_ideal_smul (J : Ideal R) (hJ : J.FG) (r : ℕ) :
    Module.FinitePresentation R
      ((Fin r → R) ⧸ (J • (⊤ : Submodule R (Fin r → R)))) := by
  let K : Submodule R (Fin r → R) := J • ⊤
  have hK : K.FG := Submodule.FG.smul hJ
    (Module.Finite.fg_top : (⊤ : Submodule R (Fin r → R)).FG)
  apply Module.finitePresentation_of_surjective K.mkQ K.mkQ_surjective
  simpa only [Submodule.ker_mkQ] using hK

/-- 有限生成冪ねじれ加群は、有限自由加群を零化イデアル冪で割った商の全射像となる。
この商は有限表示であり、元の加群と同じ指数で `J` の冪により零化される。
元の加群の有限表示性や基底環の Noether 性は仮定しない。 -/
theorem exists_free_quotient_powTorsion_cover (J : Ideal R) (hJ : J.FG)
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hM : IsPowTorsion J M) :
    ∃ n r : ℕ, ∃ f :
      ((Fin r → R) ⧸ ((J ^ n) • (⊤ : Submodule R (Fin r → R)))) →ₗ[R] M,
      Function.Surjective f ∧
        Module.FinitePresentation R
          ((Fin r → R) ⧸ ((J ^ n) • (⊤ : Submodule R (Fin r → R)))) ∧
        IsPowTorsion J ((Fin r → R) ⧸ ((J ^ n) • (⊤ : Submodule R (Fin r → R)))) := by
  obtain ⟨n, hn⟩ := hM
  obtain ⟨r, f, hf⟩ := Module.Finite.exists_fin' R M
  let K : Submodule R (Fin r → R) := (J ^ n) • ⊤
  have hK : K ≤ f.ker := by
    apply Submodule.smul_le.mpr
    intro a ha x _
    change f (a • x) = 0
    rw [f.map_smul]
    exact @hn (f x) ⟨a, ha⟩
  refine ⟨n, r, K.liftQ f hK, ?_, finitePresentation_free_quotient_ideal_smul (J ^ n) hJ.pow r,
    n, Module.isTorsionBySet_quotient_ideal_smul (Fin r → R) (J ^ n)⟩
  intro m
  obtain ⟨x, rfl⟩ := hf m
  exact ⟨Submodule.Quotient.mk x, rfl⟩

/-- 有限生成冪ねじれ加群への全射を、冪ねじれ有限表示加群から作れる。
存在する被覆加群を `ModuleCat R` の対象として包装し、加群構造を明示的に保持する。 -/
theorem exists_finitePresentation_powTorsion_cover (J : Ideal R) (hJ : J.FG)
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hM : IsPowTorsion J M) :
    ∃ P : ModuleCat.{u} R, Module.FinitePresentation R P ∧ IsPowTorsion J P ∧
      ∃ f : P →ₗ[R] M, Function.Surjective f := by
  obtain ⟨n, r, f, hf, hfp, hP⟩ := exists_free_quotient_powTorsion_cover J hJ M hM
  exact ⟨ModuleCat.of R _, hfp, hP, f, hf⟩

end SerrePositivity
