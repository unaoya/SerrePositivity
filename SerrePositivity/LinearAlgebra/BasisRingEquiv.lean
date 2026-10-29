module

public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.Algebra.Algebra.Basic

/-! # 係数体と拡大体の同型に沿う基底の移送

係数写像との両立を明示し、Mathlib の `Basis.map` と `Basis.mapCoeffs` を組み合わせる。
基底そのものを `basisOfRingEquiv` として定義し、値は `basisOfRingEquiv_apply` で読む。
-/

@[expose] public section
namespace SerrePositivity

variable {F K F' K' ι : Type*} [CommSemiring F] [CommSemiring K] [CommSemiring F']
  [CommSemiring K'] [Algebra F K] [Algebra F' K']

/-- 両立する二つの環同型に沿って基底を移す。
係数側の同型 `eF` と元側の同型 `eK` が代数構造の写像と可換なら、`B i` を `eK (B i)` へ送る基底を作る。 -/
noncomputable def basisOfRingEquiv (B : Module.Basis ι F K)
    (eF : F ≃+* F') (eK : K ≃+* K')
    (h : ∀ c, eK (algebraMap F K c) = algebraMap F' K' (eF c)) :
    Module.Basis ι F' K' :=
  letI : Algebra F K' := (eK.toRingHom.comp (algebraMap F K)).toAlgebra
  (B.map { eK.toAddEquiv with
    map_smul' := fun c x ↦ by simp [Algebra.smul_def, RingHom.algebraMap_toAlgebra] }).mapCoeffs
    eF fun c x ↦ by simp [Algebra.smul_def, RingHom.algebraMap_toAlgebra, h]

@[simp] theorem basisOfRingEquiv_apply (B : Module.Basis ι F K)
    (eF : F ≃+* F') (eK : K ≃+* K')
    (h : ∀ c, eK (algebraMap F K c) = algebraMap F' K' (eF c)) (i : ι) :
    basisOfRingEquiv B eF eK h i = eK (B i) := by
  simp [basisOfRingEquiv]

end SerrePositivity
