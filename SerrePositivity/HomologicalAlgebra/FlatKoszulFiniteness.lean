module

public import SerrePositivity.HomologicalAlgebra.FlatBaseChange
public import SerrePositivity.HomologicalAlgebra.KoszulDirectedLimit
public import Mathlib.RingTheory.TensorProduct.Finite

/-! # 平坦な押し出しの Koszul ホモロジーの底環上の有限性

押し出し B=R⊗_S T において、R が S 上平坦、T が Noether 環かつ S 上有限なら、
T の列を B へ移した Koszul ホモロジーは R 上有限生成となる。
R や B の Noether 性は必要ない。係数制限の作用を明示し、
平坦基底変更の実際のホモロジー同型で有限生成性を移す。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity
open CategoryTheory
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false

/-- 自己係数加群に対する Koszul 関手の複体は、通常の Koszul 複体に一致する。 -/
theorem koszulModuleFunctor_self_eq {T : Type u} [CommRing T] {r : ℕ} (x : Fin r → T) :
    (koszulModuleFunctor x).obj (ModuleCat.of T T) = koszulComplex x :=
  koszulComplexOn_single x

/-- Noether 環上の Koszul 複体の全次数のホモロジーは有限生成。列の正則性は不要。 -/
theorem koszulHomology_moduleFinite {T : Type u} [CommRing T] [IsNoetherianRing T]
    {r : ℕ} (x : Fin r → T) (i : ℤ) : Module.Finite T ((koszulComplex x).homology i) := by
  let : Module.Finite T ((koszulComplex x).X i) := (koszulComplex_free_finite_X x i).2
  exact homology_moduleFinite (koszulComplex x) i

variable (S R T B : Type u) [CommRing S] [CommRing R] [CommRing T] [CommRing B]
    [Algebra S R] [Algebra S T] [Algebra R B] [Algebra T B] [Algebra S B]
    [IsScalarTower S R B] [IsScalarTower S T B] [Algebra.IsPushout S R T B]
    [Module.Flat S R] [IsNoetherianRing T] [Module.Finite S T]

include S

/-- 平坦な押し出しで得た通常の Koszul ホモロジーは、底 R 上有限生成である。
底環の作用は、B からの係数制限 Module.compHom として明示する。 -/
theorem pushout_koszulHomology_finite {r : ℕ} (x : Fin r → T) (i : ℤ) :
    letI := Module.compHom ((koszulComplex (algebraMap T B ∘ x)).homology i) (algebraMap R B)
    Module.Finite R ((koszulComplex (algebraMap T B ∘ x)).homology i) := by
  let H := (koszulComplex x).homology i
  let HB := (koszulComplex (algebraMap T B ∘ x)).homology i
  let : Module S H := Module.compHom H (algebraMap S T)
  let : IsScalarTower S T H := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let : Module R HB := Module.compHom HB (algebraMap R B)
  let : Module.Finite T H := koszulHomology_moduleFinite x i
  let : Module.Finite S H := Module.Finite.trans T H
  let : Module.Finite R (R ⊗[S] H) := inferInstance
  let e := pushoutKoszulHomologyEquiv S R T B x i
  exact Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective

/-- 自己係数加群モデルの Koszul ホモロジーも、押し出しの底 R 上有限生成である。
通常モデルとの複体の一致と、明示した係数制限の作用を使う。 -/
theorem pushout_koszulModuleHomology_finite {r : ℕ} (x : Fin r → T) (i : ℤ) :
    letI := Module.compHom
      (((koszulModuleFunctor (algebraMap T B ∘ x)).obj (ModuleCat.of B B)).homology i)
      (algebraMap R B)
    Module.Finite R
      (((koszulModuleFunctor (algebraMap T B ∘ x)).obj (ModuleCat.of B B)).homology i) := by
  rw [koszulModuleFunctor_self_eq]
  exact pushout_koszulHomology_finite S R T B x i

end SerrePositivity
