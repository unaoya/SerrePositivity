module

public meta import SerrePositivity.Util.DeprecatedAlias
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.Algebra.Module.Projective

/-!
概要：KST §5、Stacks 05DP・05FS の射影性判定に使う Mittag–Leffler 加群の積比較。
方針：テンソル積と積の実際の比較射を使い、自然性と基底座標で単射性を扱う。
規約：係数環・加群・試験族は同じ宇宙、未証明の射影性判定を定義に含めない。
使われ方：完備化からの普遍単射性による Mittag–Leffler 性の降下の準備。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct

/--
概要：任意の加群族に対するテンソル積と積の比較射が単射となる性質。
方針：Mathlib の実際の比較線形写像の単射性を量化する。
規約：KST §5、Stacks 05DP・Algebra §10.89、添字と試験加群は係数環と同じ宇宙。
使われ方：射影性の存在への原典経路における Mittag–Leffler 性を表す。
-/
def IsModuleMittagLeffler (R M : Type u) [CommRing R] [AddCommGroup M] [Module R M] : Prop :=
  ∀ (ι : Type u) (N : ι → Type u) [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)],
    Function.Injective (TensorProduct.piRightHom R R M N)

/--
概要：積とテンソル積の比較写像は左因子の線形写像と可換。
方針：純テンソルと加法への帰納法で各成分を計算する。
規約：KST §5、Stacks 05DP・Algebra §10.89、任意の加群族を許す。
使われ方：普遍単射な部分加群への比較写像の単射性の降下。
-/
theorem tensorPiRightHom_rTensor_apply
    {R M M' ι : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M'] (e : M →ₗ[R] M')
    (N : ι → Type u) [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]
    (x : M ⊗[R] (∀ i, N i)) (i : ι) :
    TensorProduct.piRightHom R R M' N (e.rTensor (∀ i, N i) x) i =
      e.rTensor (N i) (TensorProduct.piRightHom R R M N x i) := by
  induction x using TensorProduct.inductionOn with
  | tmul m n => rfl
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

/--
概要：積とのテンソル写像で単射な部分加群は、周囲の積比較写像の単射性を継承する。
方針：成分ごとの自然性から周囲での等式を得て、二つの単射性を順に使う。
規約：KST §5、Stacks 05DP・Algebra Lemma 10.89.7、固定した試験族の比較。
使われ方：普遍単射な埋め込みから Mittag–Leffler 性を降下する核の補題。
-/
theorem tensorPiRightHom_injective_of_rTensor_injective
    {R M M' ι : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M'] (e : M →ₗ[R] M')
    (N : ι → Type u) [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]
    (he : Function.Injective (e.rTensor (∀ i, N i)))
    (hM' : Function.Injective (TensorProduct.piRightHom R R M' N)) :
    Function.Injective (TensorProduct.piRightHom R R M N) := by
  intro x y hxy
  apply he
  apply hM'
  funext i
  rw [tensorPiRightHom_rTensor_apply, tensorPiRightHom_rTensor_apply, hxy]

/--
概要：普遍単射な線形埋め込みの始域は終域の Mittag–Leffler 性を継承する。
方針：各試験族の積に対するテンソル写像の単射性を自然性の核の補題に渡す。
規約：KST §5、Stacks 05DP・Algebra Lemma 10.89.7、普遍単射性は実際の写像について量化する。
使われ方：完備化の Mittag–Leffler 性を元の加群へ戻す。
-/
theorem isModuleMittagLeffler_of_universally_injective
    {R M M' : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M'] (e : M →ₗ[R] M')
    (he : ∀ (P : Type u) [AddCommGroup P] [Module R P], Function.Injective (e.rTensor P))
    (hM' : IsModuleMittagLeffler R M') : IsModuleMittagLeffler R M := by
  intro ι N hN hRN
  exact tensorPiRightHom_injective_of_rTensor_injective e N (he _) (hM' ι N)

/--
概要：自由な左因子の基底座標は積とテンソル積の比較写像の各成分と可換。
方針：純テンソルでは基底係数の作用を計算し、加法で延長する。
規約：KST §5、Stacks 05DP・Algebra §10.89、右因子の自由性は要求しない。
使われ方：自由加群の積比較写像の単射性を座標ごとに示す。
-/
theorem tensorPiRightHom_basis_apply
    {R M κ ι : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    [DecidableEq κ] (b : Module.Basis κ R M) (N : ι → Type u)
    [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]
    (x : M ⊗[R] (∀ i, N i)) (k : κ) (i : ι) :
    TensorProduct.equivFinsuppOfBasisLeft b x k i =
      TensorProduct.equivFinsuppOfBasisLeft b (TensorProduct.piRightHom R R M N x i) k := by
  induction x using TensorProduct.inductionOn with
  | tmul m n => simp
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, Pi.add_apply, hx, hy]

/--
概要：自由加群の積とテンソル積の比較写像は任意の族に対して単射。
方針：左因子の基底による有限台座標で、各成分の等式から元の等式を得る。
規約：KST §5、Stacks 05DP・Algebra §10.89、自由加群の階数は有限とは限らない。
使われ方：射影加群の Mittag–Leffler 性を実分裂から導く。
-/
theorem isModuleMittagLeffler_of_free
    (R M : Type u) [CommRing R] [AddCommGroup M] [Module R M] [Module.Free R M] :
    IsModuleMittagLeffler R M := by
  classical
  intro ι N hN hRN x y hxy
  let b := Module.Free.chooseBasis R M
  apply (TensorProduct.equivFinsuppOfBasisLeft b).injective
  ext k i
  rw [tensorPiRightHom_basis_apply, tensorPiRightHom_basis_apply, hxy]

/--
概要：実際の分裂埋め込みの始域は終域の Mittag–Leffler 性を継承する。
方針：分裂の右テンソル積が左逆を持つため、普遍単射性による降下を適用する。
規約：KST §5、Stacks 05DP・Algebra §10.89、実際の線形写像と分裂等式を保持する。
使われ方：自由加群の直和因子である射影加群の Mittag–Leffler 性。
-/
theorem isModuleMittagLeffler_of_split
    {R M M' : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M'] (e : M →ₗ[R] M') (p : M' →ₗ[R] M)
    (hpe : p.comp e = LinearMap.id) (hM' : IsModuleMittagLeffler R M') :
    IsModuleMittagLeffler R M := by
  apply isModuleMittagLeffler_of_universally_injective e ?_ hM'
  intro P hP hRP
  have hleft : Function.LeftInverse (p.rTensor P) (e.rTensor P) := by
    intro x
    change ((p.rTensor P).comp (e.rTensor P)) x = x
    rw [← LinearMap.rTensor_comp, hpe, LinearMap.rTensor_id_apply]
  exact hleft.injective

/--
概要：射影加群は Mittag–Leffler である。
方針：自由加群への実分裂を選び、基底座標による自由加群の性質を直和因子へ降下する。
規約：KST §5、Stacks 05DP・Algebra §10.89、有限生成性は要求しない。
使われ方：完備化と射影性判定を結ぶ原典経路の基本例。
-/
theorem isModuleMittagLeffler_of_projective
    (R M : Type u) [CommRing R] [AddCommGroup M] [Module R M] [Module.Projective R M] :
    IsModuleMittagLeffler R M := by
  obtain ⟨e, he⟩ := Module.projective_def'.mp (inferInstance : Module.Projective R M)
  exact isModuleMittagLeffler_of_split e (Finsupp.linearCombination R id) he
    (isModuleMittagLeffler_of_free R (M →₀ R))

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
