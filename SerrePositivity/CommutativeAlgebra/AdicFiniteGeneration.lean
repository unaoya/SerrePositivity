module

public import SerrePositivity.CommutativeAlgebra.AdicCompleteness
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # adic 前完備性による有限生成判定

前完備な環上の分離加群について、イデアルで割った商の有限個の生成元を
持ち上げると、有限自由加群からの全射が得られる。
加群の完備性・有限生成性、環の局所性・Noether 性、イデアルの有限生成性は
要求しない。商での全射から元の全射への移行は Mathlib の一般定理を使う。
係数環を与えた有限正規化の構成に使用する。
-/

public section

namespace SerrePositivity

open Submodule

variable {R : Type*} [CommRing R] (I : Ideal R)
variable {M : Type*} [AddCommGroup M] [Module R M]
variable [IsPrecomplete I R] [IsHausdorff I M]

/-- 商を生成する有限列を持ち上げると、同じ列が元の加群を生成する。
有限自由な始域の前完備性と終域の分離性から、商での全射を反映する。 -/
theorem surjective_linearCombination_of_quotient {ι : Type*} [Fintype ι]
    (x : ι → M)
    (hx : Function.Surjective
      ((I • (⊤ : Submodule R M)).mkQ.comp (Fintype.linearCombination R x))) :
    Function.Surjective (Fintype.linearCombination R x) := by
  let := isPrecomplete_pi I ι
  exact surjective_of_mkQ_comp_surjective hx

/-- 有限生成な商の生成元を持ち上げ、有限自由加群からの全射を構成する。
商の有限生成性はまず基底環上で述べ、係数制限と構成の議論を分ける。 -/
theorem exists_surjective_pi_of_finite_quotient
    [Module.Finite R (M ⧸ I • (⊤ : Submodule R M))] :
    ∃ (n : ℕ) (f : (Fin n → R) →ₗ[R] M), Function.Surjective f := by
  classical
  let J : Submodule R M := I • ⊤
  obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin' R (M ⧸ J)
  let b := Pi.basisFun R (Fin n)
  choose x hx using fun i : Fin n ↦ J.mkQ_surjective (g (b i))
  let f : (Fin n → R) →ₗ[R] M := b.constr ℕ x
  have hfg : J.mkQ.comp f = g := by
    apply b.ext
    intro i
    change J.mkQ (f (b i)) = g (b i)
    rw [Module.Basis.constr_basis]
    exact hx i
  let := isPrecomplete_pi I (Fin n)
  refine ⟨n, f, surjective_of_mkQ_comp_surjective (I := I) (f := f) ?_⟩
  change Function.Surjective (J.mkQ.comp f)
  rw [hfg]
  exact hg

/-- 前完備な環上の分離加群は、イデアル商が有限生成なら有限生成。
商の自然な R/I 作用から基底環の作用へ制限し、明示的な全射を適用する。 -/
theorem finite_of_quotient_of_isPrecomplete
    [Module.Finite (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M))] : Module.Finite R M := by
  let : Module.Finite R (M ⧸ I • (⊤ : Submodule R M)) :=
    Module.Finite.trans (R ⧸ I) _
  obtain ⟨n, f, hf⟩ := exists_surjective_pi_of_finite_quotient (M := M) I
  exact Module.Finite.of_surjective f hf

omit [IsPrecomplete I R] in
/-- 商が零なら、分離性だけから加群自身も零となる。
零個の生成元を持つ自由加群の前完備性を使い、基底環の前完備性は不要である。 -/
theorem subsingleton_of_subsingleton_quotient_of_isHausdorff
    [Subsingleton (M ⧸ I • (⊤ : Submodule R M))] : Subsingleton M := by
  let f : (Fin 0 → R) →ₗ[R] M := 0
  have hf : Function.Surjective f := surjective_of_mkQ_comp_surjective
    (I := I) (f := f) (fun y ↦ ⟨0, Subsingleton.elim _ _⟩)
  exact Function.Surjective.subsingleton hf

omit [IsHausdorff I M] in
/-- 完備基底のイデアルの像で割った有限な閉ファイバーから、代数の有限性を得る。
商の係数制限とイデアル倍の同定を明示し、終域のNoether性や有限性を前提にしない。 -/
theorem finite_algebra_of_finite_quotient_map
    (S : Type*) [CommRing S] [Algebra R S] (J : Ideal S)
    [IsHausdorff J S] (hJ : I.map (algebraMap R S) = J)
    [Module.Finite R (S ⧸ J)] : Module.Finite R S := by
  let : IsHausdorff I S := (IsHausdorff.map_algebraMap_iff (I := I) (S := S) (M := S)).mp
    (by rw [hJ]; infer_instance)
  let e : (S ⧸ I • (⊤ : Submodule R S)) ≃ₗ[R] S ⧸ J :=
    (Submodule.quotEquivOfEq _ _ (by rw [Ideal.smul_top_eq_map, hJ])).trans
      (Submodule.Quotient.restrictScalarsEquiv R J)
  let : Module.Finite R (S ⧸ I • (⊤ : Submodule R S)) :=
    Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective
  obtain ⟨n, f, hf⟩ := exists_surjective_pi_of_finite_quotient (M := S) I
  exact Module.Finite.of_surjective f hf

end SerrePositivity
