module

public import SerrePositivity.CommutativeAlgebra.HilbertSamuel.Basic
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.LinearAlgebra.Isomorphisms
public import SerrePositivity.CommutativeAlgebra.Koszul
public import SerrePositivity.CommutativeAlgebra.HilbertSamuel.PolynomialGrowth
public import SerrePositivity.CategoryTheory.AlternatingSum
public import SerrePositivity.CategoryTheory.FiniteSupportBounds
public import Mathlib.Algebra.FiniteSupport.Basic
public import SerrePositivity.HomologicalAlgebra.AdicFilteredComplex
public import SerrePositivity.CommutativeAlgebra.Length.Euler
public import SerrePositivity.CommutativeAlgebra.HilbertSamuel

/-! # adic な項の Euler 和と Samuel 差分

## 概要

有限自由な複体の各項を `I` 進に切った商の長さの交代和（項の Euler 和 `euler`）を定義し、写像錐で加法的で
あること、フィルトレーションの長さとの比較、Koszul 複体では Samuel 関数の `h` 回の前進差分になること
（`euler_koszul_eq_fwdDiff`）、パラメータ系では十分先で重複度に一致すること
（`eventually_euler_koszul_eq_multiplicity`）を示す。

## 方針

Koszul 複体は錐の反復なので、錐での加法性から差分が出る。差分は Mathlib の `fwdDiff` で表し、十分先の値は
`HilbertSamuel/PolynomialGrowth` の補題で `h! · P_h` になる。

## 規約

名前空間は `KoszulMultiplicity`（Koszul 重複度の公式の証明鎖）。

## 使われ方

Koszul 重複度の公式（`KoszulMultiplicity/Formula`）。
-/

@[expose] public noncomputable section

universe u v w

section ModuleProduct

namespace SerrePositivity.KoszulMultiplicity

variable {R M N : Type u} [CommRing R]
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

theorem smul_top_prod (I : Ideal R) :
    (I • ⊤ : Submodule R (M × N)) =
      (I • ⊤ : Submodule R M).prod (I • ⊤ : Submodule R N) := by
  apply le_antisymm
  · intro x hx
    exact ⟨Submodule.smul_top_le_comap_smul_top I (LinearMap.fst R M N) hx,
      Submodule.smul_top_le_comap_smul_top I (LinearMap.snd R M N) hx⟩
  · intro x hx
    have h1 := Submodule.smul_top_le_comap_smul_top I (LinearMap.inl R M N) hx.1
    have h2 := Submodule.smul_top_le_comap_smul_top I (LinearMap.inr R M N) hx.2
    simpa using (I • (⊤ : Submodule R (M × N))).add_mem h1 h2

def quotientProdEquiv (I : Ideal R) :
    ((M × N) ⧸ (I • ⊤ : Submodule R (M × N))) ≃ₗ[R]
      (M ⧸ (I • ⊤ : Submodule R M)) × (N ⧸ (I • ⊤ : Submodule R N)) := by
  let f := (I • (⊤ : Submodule R M)).mkQ.prodMap (I • (⊤ : Submodule R N)).mkQ
  have hf : Function.Surjective f :=
    (I • (⊤ : Submodule R M)).mkQ_surjective.prodMap (I • (⊤ : Submodule R N)).mkQ_surjective
  have hker : f.ker = I • (⊤ : Submodule R (M × N)) := by
    rw [LinearMap.ker_prodMap, Submodule.ker_mkQ, Submodule.ker_mkQ, ← smul_top_prod]
  exact (Submodule.quotEquivOfEq _ _ hker.symm).trans (f.quotKerEquivOfSurjective hf)

theorem samuelFunction_prod (I : Ideal R) (n : ℕ) :
    HilbertSamuel.samuelFunction R I (M × N) n =
      HilbertSamuel.samuelFunction R I M n + HilbertSamuel.samuelFunction R I N n := by
  change Module.length R ((M × N) ⧸ (I ^ n • ⊤ : Submodule R (M × N))) = _
  rw [(quotientProdEquiv (M := M) (N := N) (I ^ n)).length_eq, Module.length_prod]
  rfl

end SerrePositivity.KoszulMultiplicity

end ModuleProduct

section TermEuler

namespace SerrePositivity.KoszulMultiplicity

open CategoryTheory CategoryTheory.Limits

variable {R : Type u} [CommRing R]

/-- 項の shifted adic 商の長さ。無限長を零に送る全域定義で、加法性には有限性が必要。 -/
def termLength (P : CochainComplex (ModuleCat.{u} R) ℤ) (I : Ideal R) (n q : ℤ) : ℝ :=
  ((HilbertSamuel.samuelFunction R I (P.X q) (n + q).toNat).toNat : ℝ)

/-- 項の adic 長さの交代和。有界性から有限台を確認して計算する。 -/
def euler (P : CochainComplex (ModuleCat.{u} R) ℤ) (I : Ideal R) (n : ℤ) : ℝ :=
  ∑ᶠ q : ℤ, ((q.negOnePow : ℤ) : ℝ) * termLength P I n q

lemma termLength_eq_zero_of_isZero (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (I : Ideal R) (n q : ℤ) (hq : IsZero (P.X q)) : termLength P I n q = 0 := by
  let : Subsingleton (P.X q) := ModuleCat.isZero_iff_subsingleton.mp hq
  simp [termLength, HilbertSamuel.samuelFunction, Module.length_eq_zero]

lemma finiteSupport_termLength (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (I : Ideal R) (n : ℤ)
    (hb : ∃ a b : ℤ, ∀ q, q < a ∨ b < q → IsZero (P.X q)) :
    Function.HasFiniteSupport (termLength P I n) := by
  obtain ⟨a, b, hab⟩ := hb
  exact finiteSupport_of_bounded_zero _ a b
    (fun q hq => termLength_eq_zero_of_isZero P I n q (hab q hq))

/-- 二つの adic 商の有限性だけから、錐の項の長さを計算する。
環の局所性・Noether 性、項の有限生成性は要求しない。 -/
lemma termLength_cone_of_finite {P Q : CochainComplex (ModuleCat.{u} R) ℤ} (f : P ⟶ Q)
    (I : Ideal R) (n q : ℤ)
    (hP : HilbertSamuel.samuelFunction R I (P.X (q + 1)) (n + q).toNat ≠ ⊤)
    (hQ : HilbertSamuel.samuelFunction R I (Q.X q) (n + q).toNat ≠ ⊤) :
    termLength (CochainComplex.mappingCone f) I n q =
      termLength P I (n - 1) (q + 1) + termLength Q I n q := by
  let e : (CochainComplex.mappingCone f).X q ≃ₗ[R] (P.X (q + 1) × Q.X q) :=
    ((HomologicalComplex.homotopyCofiber.XIsoBiprod f q (q + 1) rfl) ≪≫
      ModuleCat.biprodIsoProd _ _).toLinearEquiv
  dsimp only [termLength]
  rw [show n - 1 + (q + 1) = n + q by ring,
    HilbertSamuel.samuelFunction_eq_of_linearEquiv I e,
    KoszulMultiplicity.samuelFunction_prod,
    ENat.toNat_add hP hQ, Nat.cast_add]

/-- 各次数の adic 商の有限性から、錐の項の Euler 和は後退差分になる。
環の局所性・Noether 性や項の有限生成性は要求しない。 -/
theorem euler_cone_of_finite {P Q : CochainComplex (ModuleCat.{u} R) ℤ} (f : P ⟶ Q)
    (I : Ideal R) (n : ℤ)
    (hP : ∀ q, HilbertSamuel.samuelFunction R I (P.X (q + 1)) (n + q).toNat ≠ ⊤)
    (hQ : ∀ q, HilbertSamuel.samuelFunction R I (Q.X q) (n + q).toNat ≠ ⊤)
    (bP : ∃ a b : ℤ, ∀ q, q < a ∨ b < q → IsZero (P.X q))
    (bQ : ∃ a b : ℤ, ∀ q, q < a ∨ b < q → IsZero (Q.X q)) :
    euler (CochainComplex.mappingCone f) I n = euler Q I n - euler P I (n - 1) := by
  have hflP : Function.HasFiniteSupport (fun q => termLength P I (n - 1) (q + 1)) :=
    (finiteSupport_termLength P I (n - 1) bP).preimage
    (Equiv.addRight (1 : ℤ)).injective.injOn
  have hflQ := finiteSupport_termLength Q I n bQ
  have hwP : Function.HasFiniteSupport
      (fun q : ℤ => ((q.negOnePow : ℤ) : ℝ) * termLength P I (n - 1) (q + 1)) :=
    hflP.mul_right _
  have hwQ : Function.HasFiniteSupport
      (fun q : ℤ => ((q.negOnePow : ℤ) : ℝ) * termLength Q I n q) := hflQ.mul_right _
  have heq : (fun q : ℤ => ((q.negOnePow : ℤ) : ℝ) *
      termLength (CochainComplex.mappingCone f) I n q) =
      fun q => ((q.negOnePow : ℤ) : ℝ) * termLength P I (n - 1) (q + 1) +
        ((q.negOnePow : ℤ) : ℝ) * termLength Q I n q := by
    funext q
    rw [termLength_cone_of_finite f I n q (hP q) (hQ q), mul_add]
  unfold euler
  rw [heq, finsum_add_distrib hwP hwQ, alternatingFinsum_add_one]
  ring

variable [IsNoetherianRing R] [IsLocalRing R]

/-- 準素 adic 商の有限性を供給する、従来の錐の項の長さ公式。 -/
lemma termLength_cone {P Q : CochainComplex (ModuleCat.{u} R) ℤ} (f : P ⟶ Q)
    (I : Ideal R) (hI : I.radical = IsLocalRing.maximalIdeal R) (n q : ℤ)
    [Module.Finite R (P.X (q + 1))] [Module.Finite R (Q.X q)] :
    termLength (CochainComplex.mappingCone f) I n q =
      termLength P I (n - 1) (q + 1) + termLength Q I n q :=
  termLength_cone_of_finite f I n q
    (HilbertSamuel.samuelFunction_ne_top R I hI _ _)
    (HilbertSamuel.samuelFunction_ne_top R I hI _ _)

/-- Noether 局所環の準素商から有限性を供給する、従来の Euler 錐公式。 -/
theorem euler_cone {P Q : CochainComplex (ModuleCat.{u} R) ℤ} (f : P ⟶ Q)
    (I : Ideal R) (hI : I.radical = IsLocalRing.maximalIdeal R) (n : ℤ)
    (hP : ∀ q, Module.Finite R (P.X q)) (hQ : ∀ q, Module.Finite R (Q.X q))
    (bP : ∃ a b : ℤ, ∀ q, q < a ∨ b < q → IsZero (P.X q))
    (bQ : ∃ a b : ℤ, ∀ q, q < a ∨ b < q → IsZero (Q.X q)) :
    euler (CochainComplex.mappingCone f) I n = euler Q I n - euler P I (n - 1) := by
  apply euler_cone_of_finite f I n ?_ ?_ bP bQ
  · intro q
    let : Module.Finite R (P.X (q + 1)) := hP _
    exact HilbertSamuel.samuelFunction_ne_top R I hI _ _
  · intro q
    let : Module.Finite R (Q.X q) := hQ _
    exact HilbertSamuel.samuelFunction_ne_top R I hI _ _

end SerrePositivity.KoszulMultiplicity

end TermEuler

section FilteredLength

namespace SerrePositivity.AdicFilteredComplex
open CategoryTheory CategoryTheory.Limits IsLocalRing
variable {R : Type u} [CommRing R]
variable (P : CochainComplex (ModuleCat.{u} R) ℤ) (I : Ideal R)
variable (hd : ∀ q, (P.d q (q + 1)).hom.range ≤ I • ⊤)

/-- 準素イデアルと有限生成の項から、adic 商の各項の有限長性を得る。 -/
theorem finiteLength_quotient_term [IsNoetherianRing R] [IsLocalRing R]
    (hI : I.radical = maximalIdeal R) (q n : ℤ) [Module.Finite R (P.X q)] :
    IsFiniteLength R ((quotient P I hd n).X q) :=
  Module.length_ne_top_iff.mp (HilbertSamuel.samuelFunction_ne_top R I hI (P.X q) (n + q).toNat)

end SerrePositivity.AdicFilteredComplex

end FilteredLength

section Comparison

namespace SerrePositivity.KoszulMultiplicity

open CategoryTheory CategoryTheory.Limits IsLocalRing

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
variable (P : CochainComplex (ModuleCat.{u} R) ℤ) (I : Ideal R)
variable (hd : ∀ q, (P.d q (q + 1)).hom.range ≤ I • ⊤)

omit [IsNoetherianRing R] [IsLocalRing R] in
theorem quotient_bounded (n : ℤ)
    (hb : ∃ a b : ℤ, ∀ q, q < a ∨ b < q → IsZero (P.X q)) :
    ∃ a b : ℤ, ∀ q, q < a ∨ b < q →
      IsZero ((AdicFilteredComplex.quotient P I hd n).X q) := by
  obtain ⟨a, b, hab⟩ := hb
  refine ⟨a, b, fun q hq => ?_⟩
  let : Subsingleton (P.X q) := ModuleCat.isZero_iff_subsingleton.mp (hab q hq)
  change IsZero (ModuleCat.of R (P.X q ⧸ AdicFilteredComplex.term P I n q))
  exact ModuleCat.isZero_iff_subsingleton.mpr inferInstance

/-- Once the adic tail is acyclic, the ordinary Euler characteristic is the
alternating sum of lengths of the finite adic term quotients. -/
theorem chiOrd_eq_adicEuler (n : ℤ) (hI : I.radical = maximalIdeal R)
    (hf : ∀ q, Module.Finite R (P.X q))
    (hb : ∃ a b : ℤ, ∀ q, q < a ∨ b < q → IsZero (P.X q))
    (hacyclic : ∀ q, IsZero ((AdicFilteredComplex.tail P I hd n).homology q)) :
    chiOrd P = KoszulMultiplicity.euler P I n := by
  let f := AdicFilteredComplex.projection P I hd n
  let : QuasiIso f := AdicFilteredComplex.quasiIso_projection P I hd n hacyclic
  have hfin : ∀ q, IsFiniteLength R ((AdicFilteredComplex.quotient P I hd n).X q) := by
    intro q
    let : Module.Finite R (P.X q) := hf q
    exact AdicFilteredComplex.finiteLength_quotient_term P I hd hI q n
  calc
    chiOrd P = chiOrd (AdicFilteredComplex.quotient P I hd n) :=
      FiniteLengthComplexEuler.chiOrd_eq_of_quasiIso f
    _ = _ := by
      rw [FiniteLengthComplexEuler.chiOrd_eq_alternating_term_lengths _
        (quotient_bounded P I hd n hb) hfin]
      rfl

end SerrePositivity.KoszulMultiplicity

end Comparison

section Koszul

namespace SerrePositivity.KoszulMultiplicity

open CategoryTheory CategoryTheory.Limits IsLocalRing Filter fwdDiff

variable {R : Type u} [CommRing R]

/-- The empty Koszul complex has just the base module's Samuel length as its term Euler sum. -/
theorem euler_koszul_zero (z : Fin 0 → R) (I : Ideal R) (n : ℤ) :
    KoszulMultiplicity.euler (koszulComplex z) I n =
      ((HilbertSamuel.samuelFunction R I R n.toNat).toNat : ℝ) := by
  unfold KoszulMultiplicity.euler
  rw [finsum_eq_single _ (0 : ℤ)]
  · rw [Int.negOnePow_zero, Units.val_one, Int.cast_one, one_mul]
    unfold KoszulMultiplicity.termLength
    rw [add_zero]
    have e : (koszulComplex z).X 0 ≃ₗ[R] R :=
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of R R)).toLinearEquiv
    rw [HilbertSamuel.samuelFunction_eq_of_linearEquiv I e]
  · intro q hq
    have hzero : IsZero ((koszulComplex z).X q) :=
      HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 (ModuleCat.of R R) q hq
    rw [KoszulMultiplicity.termLength_eq_zero_of_isZero _ _ _ _ hzero, mul_zero]

/-- The Koszul complex supplies the finite term bounds needed in the cone recursion. -/
theorem koszul_bounded {h : ℕ} (z : Fin h → R) :
    ∃ a b : ℤ, ∀ q, q < a ∨ b < q → IsZero ((koszulComplex z).X q) :=
  ⟨-(h : ℤ), 0, fun q hq => hq.elim
    (koszulComplex_isZero_X_of_lt z q) (koszulComplex_isZero_X_of_pos z q)⟩

variable [IsNoetherianRing R] [IsLocalRing R]

/-- The `h`-generator Koszul term Euler sum at `n` is the `h`th forward difference of the
Samuel function at `n - h`. The bound on `n` handles the truncation in natural-number subtraction. -/
theorem euler_koszul_eq_fwdDiff {h : ℕ} (z : Fin h → R)
    (I : Ideal R) (hI : I.radical = maximalIdeal R) (n : ℕ) (hn : h ≤ n) :
    KoszulMultiplicity.euler (koszulComplex z) I (n : ℤ) =
      ((Δ_[1]^[h]
        (fun m => ((HilbertSamuel.samuelFunction R I R m).toNat : ℚ))) (n - h) : ℝ) := by
  induction h generalizing n with
  | zero =>
    rw [euler_koszul_zero, Int.toNat_natCast, Function.iterate_zero_apply, Nat.sub_zero]
    simp only [Rat.cast_natCast]
  | succ h ih =>
    let P := koszulComplex (Fin.init z)
    have hfinite : ∀ q, Module.Finite R (P.X q) :=
      fun q => (koszulComplex_free_finite_X (Fin.init z) q).2
    have hbounded := koszul_bounded (Fin.init z)
    rw [koszulComplex_succ,
      KoszulMultiplicity.euler_cone _ I hI (n : ℤ) hfinite hfinite hbounded hbounded,
      ih (Fin.init z) n (by omega)]
    have hnat : (n : ℤ) - 1 = ((n - 1 : ℕ) : ℤ) := by omega
    rw [hnat, ih (Fin.init z) (n - 1) (by omega), Function.iterate_succ_apply', fwdDiff,
      Rat.cast_sub, show n - (h + 1) + 1 = n - h by omega, show n - 1 - h = n - (h + 1) by omega]

/-- For a system of parameters, the adic term Euler sum is eventually its multiplicity. -/
theorem eventually_euler_koszul_eq_multiplicity {h : ℕ} (z : Fin h → R)
    (hz : IsSystemOfParameters R z) :
    ∀ᶠ n : ℕ in atTop,
      KoszulMultiplicity.euler (koszulComplex z) (Ideal.span (Set.range z)) (n : ℤ) =
        (HilbertSamuel.multiplicity R (Ideal.span (Set.range z)) R : ℝ) := by
  let I := Ideal.span (Set.range z)
  let P := HilbertSamuel.poly R I R
  have hI : I.radical = maximalIdeal R := hz.2
  have hd : dimToNat (ringKrullDim R) = h := by rw [hz.1]; simp [dimToNat]
  have hp := HilbertSamuel.isSamuelPoly_poly_of_radical R I hI R
  have hpval : ∀ᶠ n : ℕ in atTop,
      ((HilbertSamuel.samuelFunction R I R n).toNat : ℚ) = P.eval (n : ℚ) := by
    filter_upwards [hp] with n hn
    exact hn.2
  have hdegree : P.natDegree ≤ h :=
    ((HilbertSamuel.natDegree_poly_eq_dim R I hI).trans hd).le
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (eventually_fwdDiff_iter_eq_factorial_mul_coeff hpval h hdegree)
  have hmult : HilbertSamuel.multiplicity R I R = (h.factorial : ℚ) * P.coeff h := by
    dsimp only [HilbertSamuel.multiplicity]
    rw [Module.supportDim_self_eq_ringKrullDim, hd]
  refine eventually_atTop.mpr ⟨N + h, fun n hn => ?_⟩
  rw [euler_koszul_eq_fwdDiff z I hI n (by omega), hN (n - h) (by omega), hmult]

end SerrePositivity.KoszulMultiplicity

end Koszul
