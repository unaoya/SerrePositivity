module

public import SerrePositivity.FieldTheory.FrobeniusMonomialBasis
public import SerrePositivity.CommutativeAlgebra.FrobeniusMonomialCarry
public import Mathlib.LinearAlgebra.Basis.Bilinear
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.Algebra.Algebra.Operations

/-! # 冪関係からの p-basis の環写像の構成

高い冪の係数写像と指定生成元の冪関係だけから、単項式展開を送る環写像を作る。
乗法性は繰り上がり公式を基底上で確認し、双線形写像の外延性で全体へ延長する。
-/

@[expose] public section
namespace SerrePositivity

variable {k A ι : Type*} [Field k] [CommRing A] {p : ℕ} [Fact p.Prime] [CharP k p]
  {b : ι → k}

/-- 指定した単項式を送る環写像。係数の作用と乗法性を実際に証明する。 -/
theorem IsPBasis.exists_ringHom_of_frobeniusRelations (hb : IsPBasis k p b) (n : ℕ)
    (c : frobeniusPowerSubfield k p n →+* A) (β : ι → A)
    (hβ : ∀ i, β i ^ p ^ n = c (frobeniusPowerEquiv k p n (b i))) :
    ∃ g : k →+* A,
      (∀ a : frobeniusPowerSubfield k p n, g (a : k) = c a) ∧
        ∀ d : PExponent (p ^ n) ι, g (pMonomial b d) = pMonomial β d := by
  let F := frobeniusPowerSubfield k p n
  let : Algebra F A := c.toAlgebra
  let B := hb.frobeniusMonomialBasis n
  let L : k →ₗ[F] A := B.constr F (pMonomial β)
  have hL : ∀ d : PExponent (p ^ n) ι, L (pMonomial b d) = pMonomial β d := by
    intro d
    simpa only [B, hb.frobeniusMonomialBasis_apply] using B.constr_basis F (pMonomial β) d
  have h₁ : L 1 = 1 := by
    simpa using hL 0
  have hm : ∀ d e : PExponent (p ^ n) ι,
      L (pMonomial b d * pMonomial b e) = L (pMonomial b d) * L (pMonomial b e) := by
    intro d e
    let a : F := frobeniusPowerEquiv k p n
      ((d.val + e.val).prod (fun i m ↦ b i ^ (m / p ^ n)))
    let r := PExponent.remainder (p ^ n) (d.val + e.val)
    have hs := pMonomial_mul_frobeniusCarry n b b F.subtype (fun _ ↦ rfl) d e
    rw [hs, hL, hL]
    change L (a • pMonomial b r) = pMonomial β d * pMonomial β e
    rw [L.map_smul, hL]
    change c a * pMonomial β r = pMonomial β d * pMonomial β e
    exact (pMonomial_mul_frobeniusCarry n b β c hβ d e).symm
  have hmul : (LinearMap.mul F k).compr₂ L = (LinearMap.mul F A).compl₁₂ L L := by
    apply LinearMap.ext_basis B B
    intro d e
    change L (B d * B e) = L (B d) * L (B e)
    simpa only [B, hb.frobeniusMonomialBasis_apply] using hm d e
  let g : k →+* A :=
    { L.toAddMonoidHom with
      map_one' := h₁
      map_mul' := fun x y ↦ congrArg (fun f : k →ₗ[F] k →ₗ[F] A ↦ f x y) hmul }
  refine ⟨g, ?_, hL⟩
  intro a
  change L (a : k) = c a
  have h := L.map_smul a (1 : k)
  simp only [Algebra.smul_def] at h
  change L ((a : k) * 1) = c a * L 1 at h
  simpa only [h₁, mul_one] using h

/-- 上の環写像は、指定した p-basis の元を実際に送る。n=0も含む。 -/
theorem IsPBasis.exists_ringHom_prescribed_of_frobeniusRelations (hb : IsPBasis k p b) (n : ℕ)
    (c : frobeniusPowerSubfield k p n →+* A) (β : ι → A)
    (hβ : ∀ i, β i ^ p ^ n = c (frobeniusPowerEquiv k p n (b i))) :
    ∃ g : k →+* A,
      (∀ a : frobeniusPowerSubfield k p n, g (a : k) = c a) ∧ ∀ i, g (b i) = β i := by
  obtain ⟨g, hc, hm⟩ := hb.exists_ringHom_of_frobeniusRelations n c β hβ
  refine ⟨g, hc, ?_⟩
  intro i
  cases n with
  | zero =>
    have h := hc (frobeniusPowerEquiv k p 0 (b i))
    simpa using h.trans (hβ i).symm
  | succ n =>
    have hq : 1 < p ^ (n + 1) := by
      have hp : 1 < p := (Fact.out : p.Prime).one_lt
      have hn : 1 ≤ p ^ n := Nat.one_le_pow n p (by omega)
      have h := Nat.mul_le_mul_left p hn
      rw [Nat.mul_one, ← Nat.pow_succ'] at h
      exact hp.trans_le h
    simpa using hm (PExponent.single i ⟨1, hq⟩)

end SerrePositivity
