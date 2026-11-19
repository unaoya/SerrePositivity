module

public meta import SerrePositivity.Util.DeprecatedAlias
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Noetherian.Basic

/-!
概要：KST §5、Stacks 05DJ・05D0・Algebra Proposition 10.89.3 の係数環の積とのテンソル比較。
方針：有限自由基底と有限表示の関係式を使い、Noether 基底では有限生成部分から任意の加群へ戻す。
規約：積の添字は任意で、係数環の積の平坦性を先に仮定しない。
使われ方：係数環の積の平坦 Mittag–Leffler 性と自由加群の完備化への準備。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct

/--
概要：係数環の積とのテンソル比較は加群の線形写像と可換。
方針：純テンソルと加法で成分ごとに計算する。
規約：KST §5、Stacks 05D0・Algebra Proposition 10.89.3、有限性は不要。
使われ方：有限自由表示からテンソル比較を降ろす。
-/
theorem piScalarRightHom_rTensor_apply
    {R U V A : Type*} [CommRing R] [AddCommGroup U] [Module R U]
    [AddCommGroup V] [Module R V] (f : U →ₗ[R] V) (x : U ⊗[R] (A → R)) (a : A) :
    TensorProduct.piScalarRightHom R R V A (f.rTensor (A → R) x) a =
      f (TensorProduct.piScalarRightHom R R U A x a) := by
  induction x using TensorProduct.inductionOn with
  | tmul u r => simp
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

/--
概要：自由基底のテンソル座標は係数環の積との比較の各成分と可換。
方針：純テンソルでは係数の可換性を使い、加法で延長する。
規約：KST §5、Stacks 05D0・Algebra Proposition 10.89.3、基底の有限性は不要。
使われ方：自由加群の係数積比較の単射性。
-/
theorem piScalarRightHom_basis_apply
    {R U A κ : Type*} [CommRing R] [AddCommGroup U] [Module R U] [DecidableEq κ]
    (b : Module.Basis κ R U) (x : U ⊗[R] (A → R)) (k : κ) (a : A) :
    TensorProduct.equivFinsuppOfBasisLeft b x k a =
      b.repr (TensorProduct.piScalarRightHom R R U A x a) k := by
  induction x using TensorProduct.inductionOn with
  | tmul u r => simp [smul_eq_mul, mul_comm]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, Pi.add_apply, hx, hy]

/--
概要：自由加群の係数環の積とのテンソル比較は単射。
方針：基底座標と各積成分の等式から元のテンソルを区別する。
規約：KST §5、Stacks 05D0・Algebra Proposition 10.89.3、無限階数も許す。
使われ方：有限表示加群の比較の単射性の自由段階。
-/
theorem piScalarRightHom_injective_of_basis
    {R U A κ : Type*} [CommRing R] [AddCommGroup U] [Module R U]
    (b : Module.Basis κ R U) : Function.Injective (TensorProduct.piScalarRightHom R R U A) := by
  classical
  intro x y hxy
  apply (TensorProduct.equivFinsuppOfBasisLeft b).injective
  ext k a
  rw [piScalarRightHom_basis_apply, piScalarRightHom_basis_apply, hxy]

/--
概要：有限自由加群の係数環の積とのテンソル比較は全射。
方針：各基底座標の関数を束ねて純テンソルの有限和を作る。
規約：KST §5、Stacks 05D0・Algebra Proposition 10.89.3、積の添字は任意。
使われ方：有限個の生成元と関係式の係数を同時に持ち上げる。
-/
theorem piScalarRightHom_surjective_of_finite_basis
    {R U A κ : Type*} [CommRing R] [AddCommGroup U] [Module R U] [Finite κ]
    (b : Module.Basis κ R U) : Function.Surjective (TensorProduct.piScalarRightHom R R U A) := by
  classical
  let : Fintype κ := Fintype.ofFinite κ
  intro v
  refine ⟨∑ k, b k ⊗ₜ[R] (fun a => b.repr (v a) k), ?_⟩
  funext a
  simp only [map_sum, Finset.sum_apply, TensorProduct.piScalarRightHom_tmul]
  exact b.sum_repr (v a)

/--
概要：有限生成加群の係数環の積とのテンソル比較は全射。
方針：有限自由全射で各成分を持ち上げ、自由基底の全射性と自然性を使う。
規約：KST §5、Stacks 05D0・Algebra Proposition 10.89.3、基礎環は任意。
使われ方：有限表示加群の比較の全射性。
-/
theorem piScalarRightHom_surjective_of_finite
    (R Q A : Type*) [CommRing R] [AddCommGroup Q] [Module R Q] [Module.Finite R Q] :
    Function.Surjective (TensorProduct.piScalarRightHom R R Q A) := by
  classical
  obtain ⟨n, q, hq⟩ := Module.Finite.exists_fin' R Q
  intro v
  choose w hw using fun a => hq (v a)
  obtain ⟨x, hx⟩ := piScalarRightHom_surjective_of_finite_basis (A := A) (Pi.basisFun R (Fin n)) w
  refine ⟨q.rTensor (A → R) x, ?_⟩
  funext a
  rw [piScalarRightHom_rTensor_apply, hx]
  exact hw a

/--
概要：有限表示加群の係数環の積とのテンソル比較は単射。
方針：テンソルを生成元側へ持ち上げ、各成分の関係式を有限関係式側で束ねる。
規約：KST §5、Stacks 05D0・Algebra Proposition 10.89.3、積の添字は任意。
使われ方：Noether 基底で任意の加群の比較を有限部分から判定する。
-/
theorem piScalarRightHom_injective_of_finitePresentation
    (R Q A : Type*) [CommRing R] [AddCommGroup Q] [Module R Q] [Module.FinitePresentation R Q] :
    Function.Injective (TensorProduct.piScalarRightHom R R Q A) := by
  classical
  obtain ⟨n, m, q, g, hq, hexact⟩ := Module.FinitePresentation.exists_fin' R Q
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  obtain ⟨y, rfl⟩ := LinearMap.rTensor_surjective (A → R) hq x
  have hzero (a : A) : q (TensorProduct.piScalarRightHom R R (Fin n → R) A y a) = 0 := by
    rw [← piScalarRightHom_rTensor_apply]
    exact congrFun hx a
  choose v hv using fun a => (hexact _).mp (hzero a)
  obtain ⟨z, hz⟩ := piScalarRightHom_surjective_of_finite_basis (A := A) (Pi.basisFun R (Fin m)) v
  have hy : g.rTensor (A → R) z = y := by
    apply piScalarRightHom_injective_of_basis (Pi.basisFun R (Fin n))
    funext a
    rw [piScalarRightHom_rTensor_apply, hz]
    exact hv a
  rw [← hy, ← LinearMap.rTensor_comp_apply, hexact.linearMap_comp_eq_zero]
  simp

/--
概要：有限表示加群の係数環の任意の積とのテンソル比較は実際の線形同型。
方針：構成済みの単射性と有限生成性による全射性を使う。
規約：KST §5、Stacks 05D0・Algebra Proposition 10.89.3 の係数環のコピーの積の場合。
使われ方：有限部分加群のテンソルを成分の族と正確に比較する。
-/
def piScalarRightEquivOfFinitePresentation
    (R Q A : Type*) [CommRing R] [AddCommGroup Q] [Module R Q] [Module.FinitePresentation R Q] :
    Q ⊗[R] (A → R) ≃ₗ[R] (A → Q) :=
  LinearEquiv.ofBijective (TensorProduct.piScalarRightHom R R Q A)
    ⟨piScalarRightHom_injective_of_finitePresentation R Q A,
      piScalarRightHom_surjective_of_finite R Q A⟩

/--
概要：Noether 基礎環では任意の加群の係数環の積とのテンソル比較が単射。
方針：各テンソルを有限生成部分加群から持ち上げ、その有限表示性と成分ごとの包含の単射性を使う。
規約：KST §5、Stacks 05D0, Lemma 10.91.3、係数環の積の平坦性は仮定しない。
使われ方：係数環の任意の積の平坦性と Mittag–Leffler 性の証明。
-/
theorem piScalarRightHom_injective_of_noetherian
    (R Q A : Type*) [CommRing R] [IsNoetherianRing R] [AddCommGroup Q] [Module R Q] :
    Function.Injective (TensorProduct.piScalarRightHom R R Q A) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  obtain ⟨Q', hfinite, hcap⟩ := TensorProduct.exists_finite_submodule_left_of_setFinite
    ({x} : Set (Q ⊗[R] (A → R))) (Set.finite_singleton x)
  let : Module.Finite R Q' := hfinite
  let : Module.FinitePresentation R Q' := Module.finitePresentation_of_finite R Q'
  obtain ⟨y, hy⟩ := hcap (Set.mem_singleton x)
  have hy0 : TensorProduct.piScalarRightHom R R Q' A y = 0 := by
    funext a
    apply Subtype.val_injective
    change Q'.subtype (TensorProduct.piScalarRightHom R R Q' A y a) = 0
    rw [← piScalarRightHom_rTensor_apply, hy]
    exact congrFun hx a
  have hy' : y = 0 := (piScalarRightHom_injective_of_finitePresentation R Q' A)
    (by simpa only [map_zero] using hy0)
  rw [← hy, hy', map_zero]

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
