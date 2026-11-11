module

public import Mathlib.RingTheory.NoetherNormalization
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.FiniteStability
public import Mathlib.RingTheory.RingHom.Finite

/-!
概要：アフィン射のファイバーを正規化する多項式の変数を、元の代数の元で選ぶ。
方針：体上の Noether 正規化を使い、剰余体の分母を消して多項式変数を単元倍する。
規約：ファイバーが空でないことを環の非自明性で表す。
使われ方：相対 Noether 正規化で、もとのアフィン射から多項式スキームへの射を選ぶ。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry
open TensorProduct
open scoped TensorProduct

private theorem exists_residueField_denominator
    {R : Type*} [CommRing R] (p : Ideal R) [p.IsPrime] (x : p.ResidueField) :
    ∃ r s : R, s ∉ p ∧ x * algebraMap R p.ResidueField s = algebraMap R p.ResidueField r := by
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
  obtain ⟨⟨r, s⟩, h⟩ := IsLocalization.surj p.primeCompl a
  refine ⟨r, s, s.property, ?_⟩
  simpa only [map_mul, ← IsLocalRing.ResidueField.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
    using congrArg (IsLocalRing.residue (Localization.AtPrime p)) h

/--
概要：ファイバー代数の元は、基底の素イデアルを避ける元を掛ければ元の代数から来る。
方針：純テンソルで剰余体の分母を消し、和では二つの分母の積を使う。
規約：基底環や代数に Noether 性を仮定しない。
使われ方：Noether 正規化で得た有限個の変数の値を元の代数に持ち上げる。
-/
theorem exists_fiber_denominator
    {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
    (p : Ideal R) [p.IsPrime] (x : p.ResidueField ⊗[R] B) :
    ∃ (s : R) (b : B), s ∉ p ∧
      algebraMap R p.ResidueField s • x = (1 : p.ResidueField) ⊗ₜ[R] b := by
  let K := p.ResidueField
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
      obtain ⟨r, s, hs, h⟩ := exists_residueField_denominator p a
      refine ⟨s, r • b, hs, ?_⟩
      rw [smul_tmul', smul_eq_mul, mul_comm, h, Algebra.algebraMap_eq_smul_one, smul_tmul]
  | add x y hx hy =>
      obtain ⟨r, b, hr, hb⟩ := hx
      obtain ⟨s, c, hs, hc⟩ := hy
      have hrs : r * s ∉ p := fun h => (Ideal.IsPrime.mem_or_mem ‹p.IsPrime› h).elim hr hs
      refine ⟨r * s, s • b + r • c, hrs, ?_⟩
      have hx' : algebraMap R K (r * s) • x = (1 : K) ⊗ₜ[R] (s • b) := by
        rw [mul_comm r s, map_mul, mul_smul, hb, algebraMap_smul K, smul_tmul', smul_tmul]
      have hy' : algebraMap R K (r * s) • y = (1 : K) ⊗ₜ[R] (r • c) := by
        rw [map_mul, mul_smul, hc, algebraMap_smul K, smul_tmul', smul_tmul]
      rw [smul_add, hx', hy', tmul_add]

private theorem aeval_scaled_finite_injective
    {K A ι : Type*} [Field K] [CommRing A] [Algebra K A]
    (x : ι → A) (d : ι → K) (hd : ∀ i, d i ≠ 0)
    (hinj : Function.Injective (MvPolynomial.aeval (R := K) x))
    (hfin : (MvPolynomial.aeval (R := K) x).Finite) :
    Function.Injective (MvPolynomial.aeval (R := K) fun i => d i • x i) ∧
      (MvPolynomial.aeval (R := K) fun i => d i • x i).Finite := by
  let P := MvPolynomial ι K
  let g : P →ₐ[K] P := MvPolynomial.aeval fun i => d i • MvPolynomial.X i
  let h : P →ₐ[K] P := MvPolynomial.aeval fun i => (d i)⁻¹ • MvPolynomial.X i
  have hgh : g.comp h = AlgHom.id K P := by
    refine MvPolynomial.algHom_ext fun i => ?_
    simp [g, h, P, MvPolynomial.aeval_X, smul_smul, hd]
  have hhg : h.comp g = AlgHom.id K P := by
    refine MvPolynomial.algHom_ext fun i => ?_
    simp [g, h, P, MvPolynomial.aeval_X, smul_smul, hd]
  have e : (MvPolynomial.aeval (R := K) x).comp g = MvPolynomial.aeval (fun i => d i • x i) := by
    refine MvPolynomial.algHom_ext fun i => ?_
    simp [g]
  rw [← e]
  have hgInj : Function.Injective g := Function.LeftInverse.injective (g := h) fun y =>
    DFunLike.congr_fun hhg y
  have hgSurj : Function.Surjective g := Function.RightInverse.surjective (g := h) fun y =>
    DFunLike.congr_fun hgh y
  exact ⟨hinj.comp hgInj, RingHom.Finite.comp hfin (RingHom.Finite.of_surjective _ hgSurj)⟩

/--
概要：空でないアフィンファイバーの Noether 正規化を、元の代数の有限個の元で実現する。
方針：剰余体上で選んだ変数の値を非零スカラー倍し、元の代数から来るようにする。
規約：評価写像はファイバー上で単射かつ有限。
使われ方：相対 Noether 正規化における多項式代数への準有限射の構成。
-/
theorem exists_fiber_noether_normalization_generators
    {R B : Type*} [CommRing R] [CommRing B] [Algebra R B] [Algebra.FiniteType R B]
    (p : Ideal R) [p.IsPrime] [Nontrivial (p.ResidueField ⊗[R] B)] :
    ∃ n : ℕ, ∃ b : Fin n → B,
      let g := MvPolynomial.aeval (R := p.ResidueField)
        (fun i => (1 : p.ResidueField) ⊗ₜ[R] b i)
      Function.Injective g ∧ g.Finite := by
  let K := p.ResidueField
  obtain ⟨n, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg K (K ⊗[R] B)
  let x (i : Fin n) := g (MvPolynomial.X i)
  have he : MvPolynomial.aeval (R := K) x = g := by ext i; simp [x]
  choose s b hs hb using fun i => exists_fiber_denominator p (x i)
  let d (i : Fin n) := algebraMap R K (s i)
  have hd (i : Fin n) : d i ≠ 0 := fun h => hs i (Ideal.algebraMap_residueField_eq_zero.mp h)
  refine ⟨n, b, ?_⟩
  change Function.Injective (MvPolynomial.aeval _) ∧ (MvPolynomial.aeval _).Finite
  simp_rw [← hb]
  exact aeval_scaled_finite_injective x d hd (he ▸ hinj) (he ▸ hfin)

/--
概要：持ち上げた多項式評価写像は、剰余体で基底変更すると有限かつ単射。
方針：多項式環のテンソル積の同型を使い、二つの評価写像を変数上で比較する。
規約：元の環上の写像の有限性はファイバー上でのみ主張する。
使われ方：元のアフィンスキームから多項式スキームへの写像のファイバーを計算する。
-/
theorem exists_fiber_noether_normalization_baseChange
    {R B : Type*} [CommRing R] [CommRing B] [Algebra R B] [Algebra.FiniteType R B]
    (p : Ideal R) [p.IsPrime] [Nontrivial (p.ResidueField ⊗[R] B)] :
    ∃ n : ℕ, ∃ b : Fin n → B,
      let g := Algebra.TensorProduct.map (AlgHom.id p.ResidueField p.ResidueField)
        (MvPolynomial.aeval (R := R) b)
      Function.Injective g ∧ g.Finite := by
  obtain ⟨n, b, hinj, hfin⟩ := exists_fiber_noether_normalization_generators (B := B) p
  let K := p.ResidueField
  let e := MvPolynomial.algebraTensorAlgEquiv (σ := Fin n) R K
  let a := Algebra.TensorProduct.map (AlgHom.id K K) (MvPolynomial.aeval (R := R) b)
  let g := MvPolynomial.aeval (R := K) (fun i => (1 : K) ⊗ₜ[R] b i)
  have h : a.comp e.symm.toAlgHom = g := by
    refine MvPolynomial.algHom_ext fun i => ?_
    simp [a, e, g]
  have he : a = g.comp e.toAlgHom := by
    rw [← h, AlgHom.comp_assoc]
    simp
  refine ⟨n, b, ?_⟩
  change Function.Injective a ∧ a.Finite
  rw [he]
  exact ⟨hinj.comp e.injective,
    RingHom.Finite.comp hfin (RingHom.Finite.of_surjective _ e.surjective)⟩

end SerrePositivity.AlgebraicGeometry
