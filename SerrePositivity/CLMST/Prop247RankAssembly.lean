module

public import SerrePositivity.CLMST.Prop247RankBaseChangeDiagram
public import SerrePositivity.CommutativeAlgebra.PerfectoidizationAlgebraMap
public import SerrePositivity.CommutativeAlgebra.ScalarIsogeny
public import SerrePositivity.HomologicalAlgebra.ConeComparisonSquare

/-! # Prop 2.4.7：元の rank 比較から指定した元の写像の錐への合流

通常 tensor の単位、各成分の指定 perfectoid 化、および元の普遍性からの比較を使う。
almost 零化は明示入力とし、未供給の Cor 8.12 を引用しない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.CLMST
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    {ι : Type*} [Finite ι] (T : ι → Type u)
    [∀ i, CommRing (T i)] [∀ i, Algebra R (T i)]

/-- 元の S を各元の Ti⊗R S に送る標準代数写像の直積。 -/
def prop247_rankTensorUnit : S →ₐ[R] (i : ι) → T i ⊗[R] S :=
  AlgHom.pi (fun _ => Algebra.TensorProduct.includeRight)

/-- 元の R→∏Ti の almost 条件から、元の S→∏(Ti⊗R S) の核・余核を g² で消す。
S の平坦性は要求しない。 -/
theorem prop247_rankTensorUnit_ker_coker (g : R)
    (hk : ∀ x : (Algebra.linearMap R ((i : ι) → T i)).ker, g • x = 0)
    (hc : ∀ y : ((i : ι) → T i) ⧸ (Algebra.linearMap R ((i : ι) → T i)).range,
      g • y = 0) :
    (∀ x : (prop247_rankTensorUnit R S T).toLinearMap.ker, g ^ 2 • x = 0) ∧
      (∀ y : ((i : ι) → T i ⊗[R] S) ⧸ (prop247_rankTensorUnit R S T).toLinearMap.range,
        g ^ 2 • y = 0) := by
  let u := TensorProduct.mk R ((i : ι) → T i) S (1 : (i : ι) → T i)
  let s := (prop247_rankTensorUnit R S T).toLinearMap
  let e := (finiteProductBaseChangeEquiv R S T).toLinearEquiv.restrictScalars R
  have he (x : S) : e (u x) = s x := by
    ext i
    exact finiteProductBaseChangeEquiv_unit R S T x i
  obtain ⟨hk0, hc0⟩ := tensor_unit_ker_coker_annihilated R ((i : ι) → T i) S g g hk hc
  constructor
  · intro x
    apply Subtype.ext
    change g ^ 2 • (x : S) = 0
    have hx0 : u (x : S) = 0 := e.injective (by rw [he, map_zero]; exact x.property)
    have h := congrArg Subtype.val (hk0 ⟨(x : S), hx0⟩)
    change (g * g) • (x : S) = 0 at h
    simpa only [pow_two] using h
  · intro y
    obtain ⟨y, rfl⟩ := s.range.mkQ_surjective y
    have hm : (g * g) • e.symm y ∈ u.range := by
      apply (Submodule.Quotient.mk_eq_zero u.range).mp
      exact (u.range.mkQ.map_smul (g * g) (e.symm y)).trans (hc0 _)
    obtain ⟨x, hx⟩ := hm
    rw [← map_smul]
    apply (Submodule.Quotient.mk_eq_zero s.range).mpr
    refine ⟨x, ?_⟩
    calc
      s x = e (u x) := (he x).symm
      _ = e ((g * g) • e.symm y) := congrArg e hx
      _ = g ^ 2 • y := by rw [map_smul, e.apply_symm_apply, pow_two]

variable (p : ℕ) [Fact p.Prime] (C : Type u) [CommRing C] [Algebra R C]
    (f : S →ₐ[R] C) (hf : IsPerfectoidization p f.toRingHom)
    (P : ι → Type u) [∀ i, CommRing (P i)] [∀ i, Algebra R (P i)]
    (β : ∀ i, T i ⊗[R] S →ₐ[R] P i)
    (hβ : ∀ i, IsPerfectoidization p (β i).toRingHom)

/-- 元の指定 perfectoid 化から各指定 perfectoid 化への元の誘導写像の直積。 -/
def prop247_rankPerfectoidComparison : C →ₐ[R] (i : ι) → P i :=
  AlgHom.pi (fun i => IsPerfectoidization.mapAlgHom hf (hβ i)
    (Algebra.TensorProduct.includeRight : S →ₐ[R] T i ⊗[R] S))

/-- 元の単位と元の誘導写像が、元の各 βi と実可換図式をなす。 -/
theorem prop247_rankPerfectoidComparison_square :
    (prop247_rankPerfectoidComparison R S T p C f hf P β hβ).toLinearMap.comp f.toLinearMap =
      (LinearMap.piMap (fun i => (β i).toLinearMap)).comp
        (prop247_rankTensorUnit R S T).toLinearMap := by
  ext x i
  exact AlgHom.congr_fun (IsPerfectoidization.mapAlgHom_comp hf (hβ i)
    (Algebra.TensorProduct.includeRight : S →ₐ[R] T i ⊗[R] S)) x

/-- rank 比較の実データと有限成分の錐零化を元の f の実錐へ合流する。
almost 条件は係数写像の核・余核と元の perfectoid 比較の核だけを明示する。 -/
theorem prop247_isogeny_of_actual_rank_comparisons (g : R) (a b : ℕ)
    (hk : ∀ x : (Algebra.linearMap R ((i : ι) → T i)).ker, g ^ a • x = 0)
    (hc : ∀ y : ((i : ι) → T i) ⧸ (Algebra.linearMap R ((i : ι) → T i)).range,
      g ^ a • y = 0)
    (htk : ∀ x : (prop247_rankPerfectoidComparison R S T p C f hf P β hβ).toLinearMap.ker,
      g ^ b • x = 0)
    (hcomponent : ∀ i, ∃ q : ℕ,
      (∀ x : (β i).toLinearMap.ker, g ^ q • x = 0) ∧
        (∀ y : P i ⧸ (β i).toLinearMap.range, g ^ q • y = 0)) :
    ∃ q : ℕ, moduleMapConeScalar R f.toLinearMap (g ^ q) = 0 := by
  obtain ⟨hsk, hsc⟩ := prop247_rankTensorUnit_ker_coker R S T (g ^ a) hk hc
  obtain ⟨q, hhk, hhc⟩ := exists_uniform_pow_ker_coker_piMap
    (fun i => (β i).toLinearMap) g hcomponent
  have hcone := moduleMapConeScalar_of_comparison_square f.toLinearMap
    (prop247_rankTensorUnit R S T).toLinearMap
    (LinearMap.piMap (fun i => (β i).toLinearMap))
    (prop247_rankPerfectoidComparison R S T p C f hf P β hβ).toLinearMap
    (prop247_rankPerfectoidComparison_square R S T p C f hf P β hβ)
    (g ^ (a * 2)) (g ^ (a * 2)) (g ^ q) (g ^ q) (g ^ b)
    (by simpa only [pow_mul] using hsk) (by simpa only [pow_mul] using hsc) hhk hhc htk
  exact ⟨(a * 2 + q) + (b + a * 2 + q), by simpa only [← pow_add] using hcone⟩

end SerrePositivity.CLMST
