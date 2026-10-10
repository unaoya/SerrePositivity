module

public import Mathlib.FieldTheory.PurelyInseparable.Tower
public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.FieldTheory.Perfect
public import Mathlib.Algebra.CharP.Algebra

/-!
# 分離拡大と純非分離拡大の積写像

分離拡大の基底は純非分離拡大後も線形独立である、という Mathlib の定理を
テンソル積の積写像の単射性として利用する。
さらに、局所化と平坦性により、環のテンソル積から体のテンソル積へ単射で移す。
完全な係数体への有限分離拡大の係数拡大については、積写像の全射性も証明し、
元の基底を移した基底と次数の一致を得る。
定理2.5の `B_q` のテンソル積表示とトレースのための一般論であり、塔固有の仮定は含めない。
-/

public section
universe u
open scoped TensorProduct
namespace SerrePositivity

/-- 分離拡大と純非分離拡大を共通の体に入れたとき、テンソル積の積写像は単射。
有限次元性は不要で、任意の基底の線形独立性を用いる。 -/
theorem tensorProduct_injective_of_separable_purelyInseparable
    (K E L Ω : Type u) [Field K] [Field E] [Field L] [Field Ω]
    [Algebra K E] [Algebra K L] [Algebra K Ω] [Algebra E Ω] [Algebra L Ω]
    [IsScalarTower K E Ω] [IsScalarTower K L Ω]
    [IsPurelyInseparable K E] [Algebra.IsSeparable K L] :
    Function.Injective (Algebra.TensorProduct.productLeftAlgHom
      (Algebra.ofId E Ω) (IsScalarTower.toAlgHom K L Ω)) := by
  let b := Module.Free.chooseBasis K L
  let f : E ⊗[K] L →ₗ[E] Ω :=
    (Algebra.TensorProduct.productLeftAlgHom
      (Algebra.ofId E Ω) (IsScalarTower.toAlgHom K L Ω)).toLinearMap
  have hlin : LinearIndependent K (fun i ↦ algebraMap L Ω (b i)) :=
    b.linearIndependent.map' (IsScalarTower.toAlgHom K L Ω).toLinearMap
      (LinearMap.ker_eq_bot_of_injective (algebraMap L Ω).injective)
  have hsep : ∀ i, IsSeparable K (algebraMap L Ω (b i)) := fun i ↦
    (Algebra.IsSeparable.isSeparable K (b i)).map
      (IsScalarTower.toAlgHom K L Ω) (algebraMap L Ω).injective
  have hind := hlin.map_of_isPurelyInseparable_of_isSeparable E hsep
  have heq : f = (b.baseChange E).constr E (fun i ↦ algebraMap L Ω (b i)) := by
    apply (b.baseChange E).ext
    intro i
    rw [Module.Basis.constr_basis, Module.Basis.baseChange_apply]
    change algebraMap E Ω 1 * algebraMap L Ω (b i) = algebraMap L Ω (b i)
    rw [map_one, one_mul]
  change Function.Injective f
  rw [heq]
  exact (b.baseChange E).injective_constr_of_linearIndependent hind

/-- 有限分離拡大を完全な純非分離拡大へ係数拡大すると、共通の純非分離拡大体全体になる。
単射性は線形無関連性による。像は完全体上有限次元の整域なので完全体となり、
純非分離拡大内の根は既に像に含まれるため全射でもある。 -/
theorem tensorProduct_bijective_of_perfect_of_purelyInseparable
    (K E L Ω : Type u) [Field K] [Field E] [Field L] [Field Ω]
    [Algebra K E] [Algebra K L] [Algebra K Ω] [Algebra E Ω] [Algebra L Ω]
    [IsScalarTower K E Ω] [IsScalarTower K L Ω]
    [IsPurelyInseparable K E] [Algebra.IsSeparable K L]
    [FiniteDimensional K L] [PerfectField E] [IsPurelyInseparable L Ω]
    (p : ℕ) [ExpChar K p] :
    Function.Bijective (Algebra.TensorProduct.productLeftAlgHom
      (Algebra.ofId E Ω) (IsScalarTower.toAlgHom K L Ω)) := by
  let T := E ⊗[K] L
  let f : T →ₐ[E] Ω := Algebra.TensorProduct.productLeftAlgHom
    (Algebra.ofId E Ω) (IsScalarTower.toAlgHom K L Ω)
  have hf : Function.Injective f :=
    tensorProduct_injective_of_separable_purelyInseparable K E L Ω
  let : IsDomain T := Function.Injective.isDomain f.toRingHom hf
  let : Field T := fieldOfFiniteDimensional E T
  let : PerfectField T := Algebra.IsAlgebraic.perfectField E
  let : ExpChar E p := expChar_of_injective_algebraMap (algebraMap K E).injective p
  let : ExpChar L p := expChar_of_injective_algebraMap (algebraMap K L).injective p
  let : ExpChar Ω p := expChar_of_injective_algebraMap (algebraMap K Ω).injective p
  let : ExpChar T p := expChar_of_injective_algebraMap (algebraMap E T).injective p
  refine ⟨hf, fun x ↦ ?_⟩
  obtain ⟨n, y, hy⟩ := IsPurelyInseparable.pow_mem L p x
  obtain ⟨z, hz⟩ := (PerfectRing.bijective_frobenius (R := T) (p := p ^ n)).surjective
    (1 ⊗ₜ[K] y)
  refine ⟨z, iterateFrobenius_inj Ω p n ?_⟩
  change f z ^ (p ^ n) = x ^ (p ^ n)
  change z ^ (p ^ n) = 1 ⊗ₜ[K] y at hz
  rw [← map_pow, hz]
  change algebraMap E Ω 1 * algebraMap L Ω y = x ^ (p ^ n)
  rw [map_one, one_mul, hy]

/-- 上の積写像を係数体上の代数同型として用いる形。 -/
noncomputable def tensorProductEquiv_of_perfect_of_purelyInseparable
    (K E L Ω : Type u) [Field K] [Field E] [Field L] [Field Ω]
    [Algebra K E] [Algebra K L] [Algebra K Ω] [Algebra E Ω] [Algebra L Ω]
    [IsScalarTower K E Ω] [IsScalarTower K L Ω]
    [IsPurelyInseparable K E] [Algebra.IsSeparable K L]
    [FiniteDimensional K L] [PerfectField E] [IsPurelyInseparable L Ω]
    (p : ℕ) [ExpChar K p] : E ⊗[K] L ≃ₐ[E] Ω :=
  AlgEquiv.ofBijective _ (tensorProduct_bijective_of_perfect_of_purelyInseparable K E L Ω p)

section PerfectBasis

variable (K E L Ω : Type u) [Field K] [Field E] [Field L] [Field Ω]
    [Algebra K E] [Algebra K L] [Algebra K Ω] [Algebra E Ω] [Algebra L Ω]
    [IsScalarTower K E Ω] [IsScalarTower K L Ω]
    [IsPurelyInseparable K E] [Algebra.IsSeparable K L]
    [FiniteDimensional K L] [PerfectField E] [IsPurelyInseparable L Ω]
    (p : ℕ) [ExpChar K p]

/-- 元の有限分離拡大の基底を完全な係数体へ移した基底。
基底ベクトルは共通の拡大体への自然な像である。 -/
noncomputable def basisOfPerfectBaseChange {ι : Type*} (b : Module.Basis ι K L) :
    Module.Basis ι E Ω :=
  (b.baseChange E).map (tensorProductEquiv_of_perfect_of_purelyInseparable K E L Ω p).toLinearEquiv

/-- 係数拡大した基底の各元は、元の基底の自然な像に一致する。 -/
@[simp] theorem basisOfPerfectBaseChange_apply {ι : Type*} (b : Module.Basis ι K L) (i : ι) :
    basisOfPerfectBaseChange K E L Ω p b i = algebraMap L Ω (b i) := by
  rw [basisOfPerfectBaseChange, Module.Basis.map_apply, Module.Basis.baseChange_apply]
  change algebraMap E Ω 1 * algebraMap L Ω (b i) = _
  rw [map_one, one_mul]

include p in
/-- 有限分離拡大の次数は、完全な純非分離係数拡大の後も変わらない。 -/
theorem finrank_perfectBaseChange : Module.finrank E Ω = Module.finrank K L := by
  simpa using Module.finrank_eq_card_basis
    (basisOfPerfectBaseChange K E L Ω p (Module.finBasis K L))

end PerfectBasis

set_option backward.isDefEq.respectTransparency false in
/-- 代数的な整域拡大 `A → D` では、`D` の像が `Frac(D)` を `Frac(A)` 上張る。
Mathlib の、分母を底環側へ移して線形包を比較する定理を単位イデアルに適用する。 -/
theorem span_range_fractionRing_eq_top
    (A D K L : Type u) [CommRing A] [IsDomain A] [CommRing D] [IsDomain D]
    [Field K] [Field L] [Algebra A D] [Algebra.IsAlgebraic A D]
    [Algebra A K] [IsFractionRing A K] [Algebra D L] [IsFractionRing D L]
    [Algebra A L] [Algebra K L] [IsScalarTower A D L] [IsScalarTower A K L] :
    Submodule.span K (Set.range (algebraMap D L)) = ⊤ := by
  have hinj : Function.Injective (algebraMap A L) := by
    rw [IsScalarTower.algebraMap_eq A K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
  have hh := IsFractionRing.ideal_span_singleton_map_subset (R := A) (S := D) (K := K) (L := L)
    (a := 1) (b := Set.univ) hinj (by simp)
  apply top_unique
  intro x _
  have hx : x ∈ (Ideal.span {(algebraMap D L) 1} : Ideal L) := by simp
  simpa only [Set.image_univ, SetLike.mem_coe] using hh hx

/-- 有限な整域拡大の分数体拡大は有限次元である。
有限加群の係数拡大から分数体への全射を、元の環の像が張ることから構成する。 -/
theorem finiteDimensional_fractionRing_of_finite
    (A D K L : Type u) [CommRing A] [IsDomain A] [CommRing D] [IsDomain D]
    [Field K] [Field L] [Algebra A D] [Module.Finite A D]
    [Algebra A K] [IsFractionRing A K] [Algebra D L] [IsFractionRing D L]
    [Algebra A L] [Algebra K L] [IsScalarTower A D L] [IsScalarTower A K L] :
    FiniteDimensional K L := by
  let f : K ⊗[A] D →ₐ[K] L := Algebra.TensorProduct.productLeftAlgHom
    (Algebra.ofId K L) (IsScalarTower.toAlgHom A D L)
  apply Module.Finite.of_surjective f.toLinearMap
  rw [← LinearMap.range_eq_top]
  apply top_unique
  rw [← span_range_fractionRing_eq_top A D K L]
  apply Submodule.span_le.mpr
  rintro _ ⟨d, rfl⟩
  refine ⟨1 ⊗ₜ[A] d, ?_⟩
  change algebraMap K L 1 * algebraMap D L d = _
  rw [map_one, one_mul]

/-- 分数体の基底は、元の整域の像の中から選べる。
有限拡大に限らず、代数的な整域拡大について成立する。 -/
theorem exists_basis_fractionRing_mem_range
    (A D K L : Type u) [CommRing A] [IsDomain A] [CommRing D] [IsDomain D]
    [Field K] [Field L] [Algebra A D] [Algebra.IsAlgebraic A D]
    [Algebra A K] [IsFractionRing A K] [Algebra D L] [IsFractionRing D L]
    [Algebra A L] [Algebra K L] [IsScalarTower A D L] [IsScalarTower A K L] :
    ∃ (s : Set L) (b : Module.Basis s K L), ∀ i, b i ∈ Set.range (algebraMap D L) := by
  have hs : ⊤ ≤ Submodule.span K (Set.range (algebraMap D L)) :=
    (span_range_fractionRing_eq_top A D K L).ge
  refine ⟨_, Module.Basis.ofSpan hs, ?_⟩
  intro i
  exact Module.Basis.ofSpan_subset hs (Set.mem_range_self i)

/-- 分数体に係数を移した最小多項式が分離的なら、分数体の拡大も分離的。
分子・分母の最小多項式への整除性と、分離的な元が商で閉じることを使う。
環上の `Algebra.IsSeparable` は仮定しない。 -/
theorem isSeparable_fractionRing_of_separable_minpoly
    (A D K L : Type u) [CommRing A] [CommRing D] [Field K] [Field L]
    [Algebra A D] [Algebra A K] [Algebra A L] [Algebra D L] [Algebra K L]
    [IsScalarTower A D L] [IsScalarTower A K L] [IsFractionRing D L]
    (hsep : ∀ d : D, ((minpoly A d).map (algebraMap A K)).Separable) :
    Algebra.IsSeparable K L := by
  have hmem (d : D) : algebraMap D L d ∈ separableClosure K L :=
    (hsep d).of_dvd (minpoly.dvd_map_of_isScalarTower' A K L d)
  constructor
  intro z
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective D z
  exact (separableClosure K L).div_mem (hmem a) (hmem b)

/-- 正規な整域上の整拡大では、採用した最小多項式の条件と分数体の分離性は同値。
Mathlib の正規環と分数体の最小多項式の一致を用いる。 -/
theorem separable_minpoly_iff_fractionRing
    (A D K L : Type u) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [CommRing D] [IsDomain D] [Field K] [Field L]
    [Algebra A D] [Algebra.IsIntegral A D]
    [Algebra A K] [IsFractionRing A K] [Algebra A L] [Algebra D L]
    [IsFractionRing D L] [Algebra K L]
    [IsScalarTower A D L] [IsScalarTower A K L] :
    (∀ d : D, ((minpoly A d).map (algebraMap A K)).Separable) ↔
      Algebra.IsSeparable K L := by
  constructor
  · exact isSeparable_fractionRing_of_separable_minpoly A D K L
  · intro hsep d
    let := hsep
    rw [← minpoly.isIntegrallyClosed_eq_field_fractions K L
      (Algebra.IsIntegral.isIntegral (R := A) d)]
    exact Algebra.IsSeparable.isSeparable K (algebraMap D L d)

/-- 標準分数環での最小多項式の分離性を、別の分数体での分離性に移す。 -/
theorem separable_minpoly_map_of_isFractionRing
    (A D K : Type u) [CommRing A] [IsDomain A] [CommRing D] [Algebra A D]
    [Field K] [Algebra A K] [IsFractionRing A K]
    (hsep : ∀ d : D, ((minpoly A d).map (algebraMap A (FractionRing A))).Separable)
    (d : D) : ((minpoly A d).map (algebraMap A K)).Separable := by
  have hh := (hsep d).map (f := (FractionRing.algEquiv A K).toRingHom)
  have heq : (FractionRing.algEquiv A K).toRingHom.comp
      (algebraMap A (FractionRing A)) = algebraMap A K := by
    ext a
    exact (FractionRing.algEquiv A K).commutes a
  simpa only [Polynomial.map_map, heq] using hh

/-- 可換な環同型の組に沿って、生成的分離性を分数体の拡大へ移す。
環上の最小多項式の分離性ではなく、分数体に移した後の分離性を仮定する。 -/
theorem isSeparable_fractionRing_of_equiv
    (A D A' D' K L : Type u)
    [CommRing A] [IsDomain A] [CommRing D] [CommRing A'] [CommRing D']
    [Field K] [Field L] [Algebra A D] [Algebra A' D']
    [Algebra A' K] [IsFractionRing A' K]
    [Algebra D' L] [IsFractionRing D' L] [Algebra A' L] [Algebra K L]
    [IsScalarTower A' D' L] [IsScalarTower A' K L]
    (eA : A ≃+* A') (eD : D ≃+* D')
    (he : ∀ a : A, eD (algebraMap A D a) = algebraMap A' D' (eA a))
    (hsep : ∀ d : D, ((minpoly A d).map (algebraMap A (FractionRing A))).Separable) :
    Algebra.IsSeparable K L := by
  let : Algebra A K := ((algebraMap A' K).comp eA.toRingHom).toAlgebra
  let : Algebra A L := ((algebraMap A' L).comp eA.toRingHom).toAlgebra
  let : Algebra D L := ((algebraMap D' L).comp eD.toRingHom).toAlgebra
  let : IsFractionRing A K := IsFractionRing.of_ringEquiv_left eA (fun _ ↦ rfl)
  let : IsFractionRing D L := IsFractionRing.of_ringEquiv_left eD (fun _ ↦ rfl)
  let : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq fun a ↦ by
    change algebraMap A' L (eA a) = algebraMap K L (algebraMap A' K (eA a))
    exact IsScalarTower.algebraMap_apply A' K L (eA a)
  let : IsScalarTower A D L := IsScalarTower.of_algebraMap_eq fun a ↦ by
    change algebraMap A' L (eA a) = algebraMap D' L (eD (algebraMap A D a))
    rw [he, ← IsScalarTower.algebraMap_apply A' D' L]
  exact isSeparable_fractionRing_of_separable_minpoly A D K L
    (separable_minpoly_map_of_isFractionRing A D K hsep)

/-- 環の各元が底体の元の `p` 冪根なら、その分数体も底体上純非分離である。
分子と分母に使う Frobenius の回数をそろえてから、商を取る。 -/
theorem isPurelyInseparable_fractionRing_of_pow_mem
    (R K E : Type u) [CommRing R] [Field K] [Field E]
    [Algebra R E] [IsFractionRing R E] [Algebra K E]
    (p : ℕ) [ExpChar K p]
    (hpow : ∀ r : R, ∃ n : ℕ, ∃ a : K,
      algebraMap K E a = (algebraMap R E r) ^ (p ^ n)) :
    IsPurelyInseparable K E := by
  apply (isPurelyInseparable_iff_pow_mem K p).mpr
  intro z
  obtain ⟨r, s, _, rfl⟩ := IsFractionRing.div_surjective R z
  obtain ⟨n, a, ha⟩ := hpow r
  obtain ⟨m, b, hb⟩ := hpow s
  refine ⟨n + m, a ^ (p ^ m) / b ^ (p ^ n), ?_⟩
  rw [map_div₀, map_pow, map_pow, ha, hb, div_pow, ← pow_mul, ← pow_mul,
    ← pow_add, ← pow_add, Nat.add_comm m n]

/-- 局所化後に分離拡大と純非分離拡大へ埋め込める環の積写像は単射。
左因子の平坦性で両因子の埋め込みをテンソル積へ移し、局所化で底環を体に替える。
局所化する乗法的集合も、各埋め込みの単射性も明示的に指定する。 -/
theorem tensorProduct_injective_of_flat_of_localized_separable
    (A R T K E L Ω : Type u)
    [CommRing A] [CommRing R] [CommRing T]
    [Field K] [Field E] [Field L] [Field Ω]
    [Algebra A R] [Algebra A T] [Module.Flat A R]
    [Algebra A K] (S : Submonoid A) [IsLocalization S K]
    [Algebra A E] [Algebra A L] [Algebra A Ω]
    [Algebra K E] [Algebra K L] [Algebra K Ω]
    [Algebra E Ω] [Algebra L Ω]
    [IsScalarTower A K E] [IsScalarTower A K L]
    [IsScalarTower A E Ω] [IsScalarTower A L Ω]
    [IsScalarTower K E Ω] [IsScalarTower K L Ω]
    [IsPurelyInseparable K E] [Algebra.IsSeparable K L]
    (f : R →ₐ[A] E) (g : T →ₐ[A] L)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective (Algebra.TensorProduct.productMap
      ((IsScalarTower.toAlgHom A E Ω).comp f)
      ((IsScalarTower.toAlgHom A L Ω).comp g)) := by
  let : Module.Flat A K := IsLocalization.flat K S
  let : Module.Flat A L := Module.Flat.trans A K L
  have hmap := TensorProduct.map_injective_of_flat_flat'
    f.toLinearMap g.toLinearMap hf hg
  let e := IsLocalization.algebraTensorEquiv S K E L
  let m := Algebra.TensorProduct.productLeftAlgHom
    (Algebra.ofId E Ω) (IsScalarTower.toAlgHom K L Ω)
  have hm : Function.Injective m :=
    tensorProduct_injective_of_separable_purelyInseparable K E L Ω
  have hcomp := hm.comp (e.symm.injective.comp hmap)
  have heq : ∀ x : R ⊗[A] T,
      Algebra.TensorProduct.productMap
        ((IsScalarTower.toAlgHom A E Ω).comp f)
        ((IsScalarTower.toAlgHom A L Ω).comp g) x =
      m (e.symm (TensorProduct.map f.toLinearMap g.toLinearMap x)) := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul r t => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  intro x y hxy
  apply hcomp
  simpa only [Function.comp_apply, ← heq] using hxy

end SerrePositivity
