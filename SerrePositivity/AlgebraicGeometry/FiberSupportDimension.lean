module

public import Mathlib.RingTheory.KrullDimension.Module
public import Mathlib.RingTheory.LocalRing.Module
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
概要：整なファイバーで生成点を失った有限加群の台は次元が下がる。
方針：零化イデアルの非零元を選び、その元で割った商環の次元を上限にする。
規約：零加群の台の次元は負の無限大。
使われ方：平坦化で、生成点上で自由加群と一致する写像の余核に帰納を適用する。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open scoped nonZeroDivisors TensorProduct

/--
概要：整域上の有限加群の台が生成点を含まなければ、その台の Krull 次元に
一を加えても環の Krull 次元以下である。
方針：零化イデアルの非零元で割った商環から、零化イデアルによる商環に全射を作る。
規約：次元の不等式は零加群と無限次元の環も含む。
使われ方：幾何学的整なファイバー上で余核の台の次元を下げる。
-/
theorem supportDim_add_one_le_of_generic_notMem
    (A M : Type*) [CommRing A] [IsDomain A] [AddCommGroup M] [Module A M]
    [Module.Finite A M] (h : (⊥ : PrimeSpectrum A) ∉ Module.support A M) :
    Module.supportDim A M + 1 ≤ ringKrullDim A := by
  have hann : ¬ Module.annihilator A M ≤ ⊥ := by
    simpa only [Module.mem_support_iff_of_finite, PrimeSpectrum.asIdeal_bot] using h
  obtain ⟨a, ha, ha₀⟩ : ∃ a ∈ Module.annihilator A M, a ≠ 0 := by
    by_contra! hn
    exact hann (fun a ha => Ideal.mem_bot.mpr (hn a ha))
  let I : Ideal A := Ideal.span {a}
  have hI : I ≤ Module.annihilator A M := by
    change Ideal.span {a} ≤ Module.annihilator A M
    rwa [Ideal.span_singleton_le_iff_mem]
  let f := Ideal.Quotient.factor hI
  rw [Module.supportDim_eq_ringKrullDim_quotient_annihilator]
  have hdim := ringKrullDim_le_of_surjective f (Ideal.Quotient.factor_surjective hI)
  have ha' : a ∈ A⁰ := mem_nonZeroDivisors_iff_ne_zero.mpr ha₀
  exact (add_le_add_left hdim 1).trans (ringKrullDim_quotient_succ_le_of_nonZeroDivisor ha')

/--
概要：整なファイバーの生成点の剰余体上で全射になる写像の余核は、台の次元が
ファイバーの次元より一つ以上小さい。
方針：テンソル積の右完全性で余核の生成点での消滅を示し、零化イデアルを使う。
規約：写像と余核はファイバー代数上の加群として扱う。
使われ方：生成点で自由加群と一致する写像の余核に、次元帰納を適用する。
-/
theorem supportDim_cokernel_add_one_le_of_generic_surjective
    {A M N : Type*} [CommRing A] [IsDomain A]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] [Module.Finite A N]
    (f : M →ₗ[A] N)
    (hf : Function.Surjective (f.lTensor ((⊥ : Ideal A).ResidueField))) :
    Module.supportDim A (N ⧸ LinearMap.range f) + 1 ≤ ringKrullDim A := by
  apply supportDim_add_one_le_of_generic_notMem
  rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct]
  let K := (⊥ : Ideal A).ResidueField
  let q := (LinearMap.range f).mkQ
  have hex : Function.Exact f q := LinearMap.exact_iff.mpr (Submodule.ker_mkQ _)
  have hq := lTensor_exact K hex (Submodule.mkQ_surjective _)
  have hker : LinearMap.ker (q.lTensor K) = ⊤ :=
    (LinearMap.exact_iff.mp hq).trans (LinearMap.range_eq_top.mpr hf)
  have hzero : q.lTensor K = 0 := LinearMap.ker_eq_top.mp hker
  have hsurj : Function.Surjective (q.lTensor K) :=
    LinearMap.lTensor_surjective K (Submodule.mkQ_surjective _)
  exact not_nontrivial_iff_subsingleton.mpr <| (subsingleton_iff_forall_eq 0).mpr fun x => by
    obtain ⟨y, rfl⟩ := hsurj x
    rw [hzero, LinearMap.zero_apply]

end SerrePositivity.AlgebraicGeometry
