module

public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.MonicPowerFamilyCover
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-! # 通常根添加環上の後続多項式環の自由性と忠実平坦性

既存の係数基底と直和の忠実平坦性を使う。零環・任意添字を含む。
-/

@[expose] public noncomputable section
universe u v w
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open scoped DirectSum
variable (n : ℕ) (σ : Type u) (τ : Type v) (R : Type w) [CommRing R]

/-- 指定冪根添加環の任意後続多項式環は元の係数環上自由。 -/
theorem monicPowerFamilyPolynomial_moduleFree (c : σ → R) (hn : 0 < n) :
    Module.Free R (MvPolynomial τ (MonicPowerFamilyCover n σ R c)) := by
  let C := MonicPowerFamilyCover n σ R c
  let := monicPowerFamilyCover_moduleFree n σ R c hn
  exact Module.Free.of_equiv ((MvPolynomial.basisMonomials τ C).repr.restrictScalars R).symm

/-- 指定冪根添加環の任意後続多項式環は元の係数環上平坦。 -/
theorem monicPowerFamilyPolynomial_moduleFlat (c : σ → R) (hn : 0 < n) :
    Module.Flat R (MvPolynomial τ (MonicPowerFamilyCover n σ R c)) := by
  let := monicPowerFamilyPolynomial_moduleFree n σ τ R c hn
  infer_instance

/-- 指定冪根添加環の任意後続多項式環は元の係数環上忠実平坦。零環も含む。 -/
theorem monicPowerFamilyPolynomial_moduleFaithfullyFlat (c : σ → R) (hn : 0 < n) :
    Module.FaithfullyFlat R (MvPolynomial τ (MonicPowerFamilyCover n σ R c)) := by
  classical
  let C := MonicPowerFamilyCover n σ R c
  let ι := τ →₀ ℕ
  let := monicPowerFamilyCover_moduleFaithfullyFlat_all n σ R c hn
  let : Module.FaithfullyFlat R (ι →₀ C) :=
    Module.FaithfullyFlat.of_linearEquiv R (⨁ _ : ι, C) (finsuppLEquivDirectSum R C ι)
  exact Module.FaithfullyFlat.of_linearEquiv R (ι →₀ C)
    ((MvPolynomial.basisMonomials τ C).repr.restrictScalars R)

end SerrePositivity.BhattScholze
