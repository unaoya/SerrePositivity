module

public import SerrePositivity.BhattScholze.Delta.Free.Finite.RelativeFreeWittCoordinateChange

/-! # 逆Witt変数の段数と初期変数部分代数への制限

三角形同型の順逆射が各初期変数部分代数を保存する。
-/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

private theorem aeval_mem_supported {τ : Type*}
    (S : Subalgebra A (RelativeFreeDeltaRing (R := A) σ))
    (v : τ → RelativeFreeDeltaRing (R := A) σ) (hv : ∀ i, v i ∈ S) (c : MvPolynomial τ A) :
    MvPolynomial.aeval v c ∈ S := by
  exact MvPolynomial.eval₂_mem (fun _ _ => S.algebraMap_mem _) hv

/-- 第n逆変数は第n段以下の変数だけの多項式。 -/
theorem relativeFreeWittInverseVariable_mem_supported (D : DeltaStructure p A)
    (hp : Function.Injective (fun a : A => (p : A) * a)) (n : ℕ) (s : σ) :
    relativeFreeWittInverseVariable D hp n s ∈
      MvPolynomial.supported A {z : σ × ℕ | z.2 ≤ n} := by
  classical
  induction n using Nat.strong_induction_on generalizing s with
  | h n ih =>
      let S := MvPolynomial.supported A {z : σ × ℕ | z.2 ≤ n}
      rw [relativeFreeWittInverseVariable_eq]
      apply S.sub_mem
      · apply Algebra.subset_adjoin
        exact ⟨(s, n), (by change n ≤ n; exact le_rfl), rfl⟩
      · apply aeval_mem_supported
        intro z
        exact (MvPolynomial.supported_mono (R := A)
          (fun x hx => Nat.le_trans hx (Nat.le_of_lt z.2.isLt)))
          (ih z.2.val z.2.isLt z.1)

/-- 構成した逆変数の変数段数上界。 -/
theorem relativeFreeWittInverseVariable_variable_bound (D : DeltaStructure p A)
    (hp : Function.Injective (fun a : A => (p : A) * a)) (n : ℕ) (s : σ)
    (z : σ × ℕ) (hz : z ∈ (relativeFreeWittInverseVariable D hp n s).vars) : z.2 ≤ n :=
  MvPolynomial.mem_supported.mp (relativeFreeWittInverseVariable_mem_supported D hp n s) hz

/-- 順座標射は任意初期N段の変数部分代数を保存する。 -/
theorem relativeFreeWittCoordinateMap_mem_supported (D : DeltaStructure p A)
    (hp : Function.Injective (fun a : A => (p : A) * a)) (N : ℕ)
    (f : RelativeFreeDeltaRing (R := A) σ)
    (hf : f ∈ MvPolynomial.supported A {z : σ × ℕ | z.2 < N}) :
    relativeFreeWittCoordinateMap D f ∈ MvPolynomial.supported A {z : σ × ℕ | z.2 < N} := by
  let S := MvPolynomial.supported A {z : σ × ℕ | z.2 < N}
  have h : S ≤ S.comap (relativeFreeWittCoordinateMap D) := by
    apply Algebra.adjoin_le
    intro v hv
    obtain ⟨z, hz, rfl⟩ := hv
    change relativeFreeWittCoordinateMap D (MvPolynomial.X z) ∈ S
    rw [relativeFreeWittCoordinateMap, MvPolynomial.aeval_X]
    apply MvPolynomial.mem_supported.mpr
    intro x hx
    exact Nat.lt_of_le_of_lt (relativeFreeWittGhostCoefficient_variable_bound D hp z.1 z.2 x hx) hz
  exact h hf

/-- 逆座標射も任意初期N段の変数部分代数を保存する。 -/
theorem relativeFreeWittInverseMap_mem_supported (D : DeltaStructure p A)
    (hp : Function.Injective (fun a : A => (p : A) * a)) (N : ℕ)
    (f : RelativeFreeDeltaRing (R := A) σ)
    (hf : f ∈ MvPolynomial.supported A {z : σ × ℕ | z.2 < N}) :
    relativeFreeWittInverseMap D hp f ∈ MvPolynomial.supported A {z : σ × ℕ | z.2 < N} := by
  let S := MvPolynomial.supported A {z : σ × ℕ | z.2 < N}
  have h : S ≤ S.comap (relativeFreeWittInverseMap D hp) := by
    apply Algebra.adjoin_le
    intro v hv
    obtain ⟨z, hz, rfl⟩ := hv
    change relativeFreeWittInverseMap D hp (MvPolynomial.X z) ∈ S
    rw [relativeFreeWittInverseMap, MvPolynomial.aeval_X]
    exact (MvPolynomial.supported_mono (R := A) (fun x hx => Nat.lt_of_le_of_lt hx hz))
      (relativeFreeWittInverseVariable_mem_supported D hp z.2 z.1)
  exact h hf

/-- 全Witt座標同型は、任意初期N段の変数部分代数の実際の代数同型に制限できる。 -/
def relativeFreeWittSupportedEquiv (D : DeltaStructure p A)
    (hp : Function.Injective (fun a : A => (p : A) * a)) (N : ℕ) :
    MvPolynomial.supported A {z : σ × ℕ | z.2 < N} ≃ₐ[A]
      MvPolynomial.supported A {z : σ × ℕ | z.2 < N} where
  toFun f := ⟨relativeFreeWittCoordinateMap D f.val,
    relativeFreeWittCoordinateMap_mem_supported D hp N f.val f.property⟩
  invFun f := ⟨relativeFreeWittInverseMap D hp f.val,
    relativeFreeWittInverseMap_mem_supported D hp N f.val f.property⟩
  left_inv f := by
    apply Subtype.ext
    exact (relativeFreeWittCoordinateEquiv D hp).symm_apply_apply f.val
  right_inv f := by
    apply Subtype.ext
    exact (relativeFreeWittCoordinateEquiv D hp).apply_symm_apply f.val
  map_mul' f g := by apply Subtype.ext; exact map_mul _ _ _
  map_add' f g := by apply Subtype.ext; exact map_add _ _ _
  commutes' a := by apply Subtype.ext; exact AlgHom.commutes _ a

/-- 制限した代数同型の標準包含図式。 -/
theorem relativeFreeWittSupportedEquiv_coe (D : DeltaStructure p A)
    (hp : Function.Injective (fun a : A => (p : A) * a)) (N : ℕ)
    (f : MvPolynomial.supported A {z : σ × ℕ | z.2 < N}) :
    (relativeFreeWittSupportedEquiv D hp N f : RelativeFreeDeltaRing (R := A) σ) =
      relativeFreeWittCoordinateMap D (f : RelativeFreeDeltaRing (R := A) σ) := rfl

end SerrePositivity.BhattScholze
