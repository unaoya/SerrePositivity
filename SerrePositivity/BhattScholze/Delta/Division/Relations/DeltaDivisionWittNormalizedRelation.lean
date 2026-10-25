module

public import SerrePositivity.BhattScholze.Delta.Division.Relations.DeltaDivisionWittFiniteRelationIdeal
public import SerrePositivity.BhattScholze.Delta.Free.Finite.RelativeFreeWittCoefficientNaturality
public import SerrePositivity.BhattScholze.Delta.Free.Finite.RelativeFreeFiniteTopVariableSplit

/-! # 逆Witt座標での具体的モニック有限関係式

最高変数のp乗と初期段の係数多項式を分離する。
-/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- 正規化した第n関係式の下位有限変数だけの係数。 -/
def deltaDivisionWittNormalizedCoefficient (D : DeltaStructure p A) (d : A)
    (a : σ → A) (u : Aˣ) (s : σ) (n : ℕ) : MvPolynomial (σ × Fin (n + 1)) A :=
  MvPolynomial.C ((u⁻¹ : Aˣ) : A) ^ (p ^ (n + 1)) *
    (MvPolynomial.C ((deltaWittGhostVector D (a s)).coeff (n + 2)) -
      MvPolynomial.eval₂Hom MvPolynomial.C (fun i : Fin (n + 1) => MvPolynomial.X (s, i))
        (wittDivisionRemainderPolynomial (deltaWittGhostVector D d) n))

/-- 下位係数多項式の標準包含像。 -/
theorem deltaDivisionWittNormalizedCoefficient_image (D : DeltaStructure p A) (d : A)
    (a : σ → A) (u : Aˣ) (s : σ) (n : ℕ) :
    relativeFreeFiniteInitialPolynomialMap (n + 1) σ A
      (deltaDivisionWittNormalizedCoefficient D d a u s n) =
    MvPolynomial.C ((u⁻¹ : Aˣ) : A) ^ (p ^ (n + 1)) *
      (MvPolynomial.C ((deltaWittGhostVector D (a s)).coeff (n + 2)) -
        MvPolynomial.eval₂Hom MvPolynomial.C
          (fun i : Fin (n + 1) => MvPolynomial.X (s, i.val))
          (wittDivisionRemainderPolynomial (deltaWittGhostVector D d) n)) := by
  let f := (relativeFreeFiniteInitialPolynomialMap (n + 1) σ A).toRingHom
  have hC (b : A) : f (MvPolynomial.C b) = MvPolynomial.C b := by
    simp [f, relativeFreeFiniteInitialPolynomialMap]
  have hX (i : Fin (n + 1)) : f (MvPolynomial.X (s, i)) = MvPolynomial.X (s, i.val) := by
    simp [f, relativeFreeFiniteInitialPolynomialMap]
  have he := MvPolynomial.map_eval₂Hom MvPolynomial.C
    (fun i : Fin (n + 1) => MvPolynomial.X (s, i)) f
    (wittDivisionRemainderPolynomial (deltaWittGhostVector D d) n)
  have hfc : f.comp MvPolynomial.C = MvPolynomial.C := by
    apply RingHom.ext
    exact hC
  have hfx : (fun i : Fin (n + 1) => f (MvPolynomial.X (s, i))) =
      fun i => MvPolynomial.X (s, i.val) := funext hX
  rw [hfc, hfx] at he
  change f (deltaDivisionWittNormalizedCoefficient D d a u s n) = _
  rw [deltaDivisionWittNormalizedCoefficient, map_mul, map_pow, map_sub, hC, hC, he]

/-- 最高有限変数のp乗から初期段係数を引いた、具体的なモニック有限関係式。 -/
def deltaDivisionWittNormalizedPolynomial (D : DeltaStructure p A) (d : A)
    (a : σ → A) (u : Aˣ) (s : σ) (n : ℕ) : MvPolynomial (σ × Fin (n + 2)) A :=
  MvPolynomial.X (s, Fin.last (n + 1)) ^ p -
    relativeFreeFiniteStepInclusion n σ (deltaDivisionWittNormalizedCoefficient D d a u s n)

/-- 正規化した有限関係式の包含像は最高変数のp乗から下位係数を引いた式。 -/
theorem deltaDivisionWittNormalizedPolynomial_image (D : DeltaStructure p A) (d : A)
    (a : σ → A) (u : Aˣ) (s : σ) (n : ℕ) :
    relativeFreeFiniteInitialPolynomialMap (n + 2) σ A
      (deltaDivisionWittNormalizedPolynomial D d a u s n) =
      MvPolynomial.X (s, n + 1) ^ p -
        relativeFreeFiniteInitialPolynomialMap (n + 1) σ A
          (deltaDivisionWittNormalizedCoefficient D d a u s n) := by
  rw [deltaDivisionWittNormalizedPolynomial, map_sub, map_pow]
  have hx : relativeFreeFiniteInitialPolynomialMap (n + 2) σ A
      (MvPolynomial.X (s, Fin.last (n + 1))) = MvPolynomial.X (s, n + 1) := by
    simp [relativeFreeFiniteInitialPolynomialMap]
  rw [hx]
  congr 1
  exact RingHom.congr_fun (relativeFreeFiniteStepInclusion_comp_initial (A := A) n σ) _

/-- 実際の源Witt根関係元の逆座標像は、構成した有限モニック関係式の包含像。 -/
theorem deltaDivisionRelativeWittRelationElement_inverse_image (D : DeltaStructure p A)
    (hp : Function.Injective (fun a : A => (p : A) * a))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (d : A) (a : σ → A) (u : Aˣ) (s : σ) (n : ℕ) :
    relativeFreeWittInverseMap D hp (deltaDivisionRelativeWittRelationElement D d a u s n) =
      relativeFreeFiniteInitialPolynomialMap (n + 2) σ A
        (deltaDivisionWittNormalizedPolynomial D d a u s n) := by
  let E := relativeFreeDeltaStructure σ D
  let q := (relativeFreeWittInverseMap (σ := σ) D hp).toRingHom
  have hX (i : ℕ) : q ((deltaWittGhostVector E (MvPolynomial.X (s, 0))).coeff i) =
      MvPolynomial.X (s, i) := by
    change relativeFreeWittInverseMap D hp (relativeFreeWittGhostCoefficient D s i) = _
    exact relativeFreeWittInverseMap_coefficient D hp s i
  have hC (b : A) (i : ℕ) : q ((deltaWittGhostVector E (MvPolynomial.C b)).coeff i) =
      MvPolynomial.C ((deltaWittGhostVector D b).coeff i) := by
    exact relativeFreeWittInverseMap_coefficient_C D hp hg b i
  have hqC (b : A) : q (MvPolynomial.C b) = MvPolynomial.C b :=
    AlgHom.commutes (relativeFreeWittInverseMap D hp) b
  have hw : WittVector.map q (deltaWittGhostVector E (MvPolynomial.C d)) =
      WittVector.map MvPolynomial.C (deltaWittGhostVector D d) :=
    (relativeFreeWittInverseMap_wittVector_C D hp hg d).trans
      (deltaWittGhostVector_relativeFree_C D hg d)
  have huq :
      ((((u.map (MvPolynomial.C : A →+* RelativeFreeDeltaRing (R := A) σ))).map
        q.toMonoidHom)⁻¹ :
      (RelativeFreeDeltaRing (R := A) σ)ˣ) =
      (u⁻¹).map (MvPolynomial.C : A →+* RelativeFreeDeltaRing (R := A) σ) := by
    apply Units.ext
    change q (MvPolynomial.C ((u⁻¹ : Aˣ) : A)) = MvPolynomial.C ((u⁻¹ : Aˣ) : A)
    exact hqC _
  have huqv := congrArg Units.val huq
  unfold deltaDivisionRelativeWittRelationElement
  change q (deltaDivisionWittRelationElement E (MvPolynomial.C d) (MvPolynomial.X (s, 0))
    (MvPolynomial.C (a s))
    (u.map (MvPolynomial.C : A →+* RelativeFreeDeltaRing (R := A) σ)) n) = _
  rw [deltaDivisionWittRelationElement_map]
  simp only [deltaDivisionWittRootPolynomial, Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C]
  simp only [hX, hC]
  rw [hw, ← wittDivisionRemainderPolynomial_map, MvPolynomial.eval₂Hom_map_hom]
  rw [deltaDivisionWittNormalizedPolynomial_image, deltaDivisionWittNormalizedCoefficient_image]
  congr 1
  apply congrArg₂ (fun b c : RelativeFreeDeltaRing (R := A) σ => b * c)
  · apply congrArg (fun b : RelativeFreeDeltaRing (R := A) σ => b ^ (p ^ (n + 1)))
    exact huqv
  · rfl

/-- 最高変数分離後の関係式は、各変数のp乗から下位係数を引いたモニック冪形。 -/
theorem deltaDivisionWittNormalizedPolynomial_top_split (D : DeltaStructure p A) (d : A)
    (a : σ → A) (u : Aˣ) (s : σ) (n : ℕ) :
    relativeFreeFiniteTopVariableSplitAlgEquiv n σ A
      (deltaDivisionWittNormalizedPolynomial D d a u s n) =
        MvPolynomial.X s ^ p -
          MvPolynomial.C (deltaDivisionWittNormalizedCoefficient D d a u s n) := by
  rw [deltaDivisionWittNormalizedPolynomial, map_sub, map_pow,
    relativeFreeFiniteTopVariableSplitAlgEquiv_X_top,
    relativeFreeFiniteTopVariableSplitAlgEquiv_inclusion]

end SerrePositivity.BhattScholze
