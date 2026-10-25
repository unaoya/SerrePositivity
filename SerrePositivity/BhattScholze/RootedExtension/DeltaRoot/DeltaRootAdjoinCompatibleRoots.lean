module

public import SerrePositivity.BhattScholze.RootedExtension.PerfectDeltaRankOneRoots

/-! # 根δ除算包の通常商における指定元の互換p冪根族 -/

@[expose] public noncomputable section
universe u v w z
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
variable (D : DeltaStructure p A) (d : A) (b : σ → A)
variable {C : Type w} [CommRing C] {T : Type z} [CommRing T]
variable (E : DeltaStructure p C) (hE : E.IsPerfect)
variable (f : DeltaRootAdjoinDivision D d b →+* C) (q : C →+* T)

/-- raw根変数のδ値零は、任意の指定δ射で保存される。 -/
theorem deltaRootAdjoinDivisionVariable_map_delta
    (hf : (deltaAdjoinDivisionStructure (polynomialRankOneDeltaStructure σ D) (MvPolynomial.C d)
      (deltaRootRelationFamily (p := p) b)).IsDeltaHom E f) (s : σ) :
    E.delta (f (deltaRootAdjoinDivisionVariable D d b s)) = 0 := by
  have h := hf (deltaRootAdjoinDivisionVariable D d b s)
  rw [deltaRootAdjoinDivisionVariable_delta, map_zero] at h
  exact h.symm

/-- 指定元の像を零段とし、根変数への逆Frobenius列の通常商像を続ける具体的族。 -/
def deltaRootAdjoinCompatibleRoots (s : σ) : ℕ → T
  | 0 => q (f (deltaAdjoinDivisionMap (polynomialRankOneDeltaStructure σ D) (MvPolynomial.C d)
      (deltaRootRelationFamily (p := p) b) (MvPolynomial.C (b s))))
  | n + 1 => q (perfectDeltaRankOneRoot E hE (f (deltaRootAdjoinDivisionVariable D d b s)) n)

/-- 根族の零段は指定元の元の係数射による像。 -/
theorem deltaRootAdjoinCompatibleRoots_zero (s : σ) :
    deltaRootAdjoinCompatibleRoots D d b E hE f q s 0 =
      q (f (deltaAdjoinDivisionMap (polynomialRankOneDeltaStructure σ D) (MvPolynomial.C d)
        (deltaRootRelationFamily (p := p) b) (MvPolynomial.C (b s)))) := rfl

/-- 零段以降の根族は、根変数への逆Frobenius列の通常商像そのもの。 -/
theorem deltaRootAdjoinCompatibleRoots_succ (s : σ) (n : ℕ) :
    deltaRootAdjoinCompatibleRoots D d b E hE f q s (n + 1) =
      q (perfectDeltaRankOneRoot E hE (f (deltaRootAdjoinDivisionVariable D d b s)) n) := rfl

/-- dの像を消す通常商において、指定元の像から始まる根族は互換p冪根条件を満たす。 -/
theorem deltaRootAdjoinCompatibleRoots_pow
    (hf : (deltaAdjoinDivisionStructure (polynomialRankOneDeltaStructure σ D) (MvPolynomial.C d)
      (deltaRootRelationFamily (p := p) b)).IsDeltaHom E f)
    (hd : q (f (deltaAdjoinDivisionMap (polynomialRankOneDeltaStructure σ D) (MvPolynomial.C d)
      (deltaRootRelationFamily (p := p) b) (MvPolynomial.C d))) = 0) (s : σ) (n : ℕ) :
    deltaRootAdjoinCompatibleRoots D d b E hE f q s (n + 1) ^ p =
      deltaRootAdjoinCompatibleRoots D d b E hE f q s n := by
  cases n with
  | zero =>
      change q (f (deltaRootAdjoinDivisionVariable D d b s)) ^ p = _
      exact deltaRootAdjoinDivisionVariable_map_pow D d b (q.comp f) hd s
  | succ n =>
      change q (perfectDeltaRankOneRoot E hE (f (deltaRootAdjoinDivisionVariable D d b s))
        (n + 1)) ^ p =
          q (perfectDeltaRankOneRoot E hE (f (deltaRootAdjoinDivisionVariable D d b s)) n)
      exact perfectDeltaRankOneRoot_map_pow E hE _
        (deltaRootAdjoinDivisionVariable_map_delta D d b E f hf s) q n

end SerrePositivity.BhattScholze
