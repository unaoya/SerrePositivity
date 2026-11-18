module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.TensorPowerDegreeBasis
public import SerrePositivity.EInfinity.BarrattEccles.Degrees

/-!
# Barratt–Eccles の Schur 表示の語で添字づけた基底

## 概要
Berger–Fresse §1.1 の自由な arity と入力のテンソル基底を合わせる。

## 方針
係数の正次数では空基底、非正次数では正則表現の余不変の基底を使う。

## 規約
各入力は次数付き基底の添字で、同じ入力の重複を保つ。

## 使われ方
セル代数の次数ごとの自由な台と重みの照合。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory Limits MonoidalCategory HomologicalComplex DifferentialGraded
open scoped TensorProduct

variable {A : Type u} [CommRing A]

/-- The arity, coefficient simplex, and input word indices in a single bidegree. -/
def schurWordPieceIndex (I : ℤ → Type u) (i : ℤ) (n : ℕ)
    (a : {a : ℤ × ℤ // a.1 + a.2 = i}) : Type u :=
  if a.1.1 ≤ 0 then
    ULift.{u} (BasedNondegenerate n (-a.1.1).toNat) × powerGradedIndex I n a.1.2
  else PEmpty

/-- The specified word basis for the coinvariants in one Schur bidegree. -/
def schurWordPieceBasis {K : Complex A} {I : ℤ → Type u}
    (b : ∀ i, Module.Basis (I i) A (K.X i)) (i : ℤ) (n : ℕ)
    (a : {a : ℤ × ℤ // a.1 + a.2 = i}) :
    Module.Basis (schurWordPieceIndex I i n a) A
      (schurArityBidegreeRepresentation (sequence A) K i n a).ρ.Coinvariants := by
  classical
  obtain ⟨⟨p, r⟩, h⟩ := a
  by_cases hp : p ≤ 0
  · let q := (-p).toNat
    have hpq : p = -(q : ℤ) := by dsimp [q]; omega
    have hr : r = i + q := by omega
    have ha : (⟨(p, r), h⟩ : {a : ℤ × ℤ // a.1 + a.2 = i}) =
        ⟨(-(q : ℤ), i + q), by omega⟩ := Subtype.ext (Prod.ext hpq hr)
    rw [ha]
    simpa only [schurWordPieceIndex, ite_eq_left (show -(q : ℤ) ≤ 0 by omega),
      neg_neg, Int.toNat_natCast] using
      schurNonpositiveBidegreeBasis K i n q (powerGradedBasis b n (i + q))
  · haveI : Subsingleton ((complex A n).X p) :=
      ModuleCat.subsingleton_of_isZero (complex_isZero_positive A n p (by omega))
    let V := schurArityBidegreeRepresentation (sequence A) K i n ⟨(p, r), h⟩
    haveI : Subsingleton V := by
      change Subsingleton (((complex A n).X p) ⊗[A] ((TensorPowers.power K n).X r))
      infer_instance
    haveI : Subsingleton V.ρ.Coinvariants := by
      change Subsingleton (V ⧸ Representation.Coinvariants.ker V.ρ)
      infer_instance
    change Module.Basis (if p ≤ 0 then _ else PEmpty) A V.ρ.Coinvariants
    rw [ite_eq_right hp]
    exact Module.Basis.empty _

/-- The word indices in a degree of the Schur complex. -/
abbrev SchurWordIndex (I : ℤ → Type u) (i : ℤ) :=
  Σ n, Σ a : {a : ℤ × ℤ // a.1 + a.2 = i}, schurWordPieceIndex I i n a

/-- A word basis for each degree of the actual free Barratt–Eccles algebra carrier. -/
def schurWordBasis {K : Complex A} {I : ℤ → Type u}
    (b : ∀ i, Module.Basis (I i) A (K.X i)) (i : ℤ) :
    Module.Basis (SchurWordIndex I i) A (((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A (sequence A)).obj K).X i) :=
  schurDegreeBasis (sequence A) K i (schurWordPieceBasis b i)

/-- The finite list of homogeneous inputs of a Schur word basis index. -/
def schurWordInputs {I : ℤ → Type u} {i : ℤ} (x : SchurWordIndex I i) :
    List (Σ i, I i) := by
  classical
  obtain ⟨n, a, x⟩ := x
  by_cases hp : a.1.1 ≤ 0
  · have y : ULift.{u} (BasedNondegenerate n (-a.1.1).toNat) ×
        powerGradedIndex I n a.1.2 := by
      simpa only [schurWordPieceIndex, ite_eq_left hp] using x
    exact powerGradedInputs n a.1.2 y.2
  · have y : PEmpty := by
      simpa only [schurWordPieceIndex, ite_eq_right hp] using x
    exact y.elim

/-- The weight of a Schur basis word counts each occurrence of an input. -/
def schurWordWeight {I : ℤ → Type u} {i : ℤ} (w : (Σ i, I i) → ℕ)
    (x : SchurWordIndex I i) : ℕ :=
  ((schurWordInputs x).map w).sum

/-- Nonpositive coefficient degrees and bounded input degrees bound every Schur word degree. -/
lemma degree_le_schurWordWeight {I : ℤ → Type u} (w : (Σ i, I i) → ℕ)
    (hw : ∀ x, x.1 ≤ (w x : ℤ)) (i : ℤ) (x : SchurWordIndex I i) :
    i ≤ (schurWordWeight w x : ℤ) := by
  classical
  obtain ⟨n, a, x⟩ := x
  by_cases hp : a.1.1 ≤ 0
  · let y : ULift.{u} (BasedNondegenerate n (-a.1.1).toNat) ×
        powerGradedIndex I n a.1.2 := by
      simpa only [schurWordPieceIndex, ite_eq_left hp] using x
    have h := degree_le_powerGradedWeight w hw n a.1.2 y.2
    have he : schurWordWeight w ⟨n, a, x⟩ = powerGradedWeight w n a.1.2 y.2 := by
      simp only [schurWordWeight, schurWordInputs, dite_eq_left hp, y, powerGradedWeight]
    rw [he]
    have hdeg := a.2
    omega
  · have y : PEmpty := by
      simpa only [schurWordPieceIndex, ite_eq_right hp] using x
    exact y.elim

end SerrePositivity.EInfinity.BarrattEccles
