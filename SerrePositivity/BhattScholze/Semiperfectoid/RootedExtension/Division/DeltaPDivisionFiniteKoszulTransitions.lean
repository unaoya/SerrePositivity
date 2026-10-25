module

public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.Division.DeltaPDivisionFiniteKoszulComparison
public import Mathlib.CategoryTheory.Functor.OfSequence

/-! # 実有限p除算Koszul比較の段間自然性

末尾への関係付加は実mappingConeの包含、商側は既存の標準因子射を用いる。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory SerrePositivity.DerivedCompletion
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A] [Unique σ]
variable (D : DeltaStructure p A) (y : A)
local notation "L₀" => RelativeFreeDeltaRing (R := A) σ
local notation "a₀" => fun _ : σ ↦ D.frobeniusLift y
local notation "g₀" => deltaDivisionIteratedRelation D (p : A) a₀ (default : σ)
local notation "I₀" => deltaDivisionFiniteRelationIdeal D (p : A) a₀

/-- 次の実δ関係を末尾へ付加するKoszul複体の標準鎖写像。 -/
def deltaPDivisionFiniteKoszulTransition (N : ℕ) :
    SerrePositivity.koszulComplex (fun i : Fin (N + 1) => g₀ i.val) ⟶
      SerrePositivity.koszulComplex (fun i : Fin (N + 2) => g₀ i.val) :=
  CochainComplex.mappingCone.inr
    (SerrePositivity.smulId (g₀ (N + 1))
      (SerrePositivity.koszulComplex (fun i : Fin (N + 1) => g₀ i.val)))

/-- 実Koszul遷移射は、元の自由環からの標準H⁰単位を保存する。 -/
theorem deltaPDivisionFiniteKoszulTransition_unit (N : ℕ) (r : L₀) :
    (HomologicalComplex.homologyMap (deltaPDivisionFiniteKoszulTransition D y N) 0).hom
      (koszulH0Unit L₀ (fun i : Fin (N + 1) => g₀ i.val) r) =
        koszulH0Unit L₀ (fun i : Fin (N + 2) => g₀ i.val) r := by
  exact (LinearMap.congr_fun
    (koszulH0Unit_succ L₀ (fun i : Fin (N + 2) => g₀ i.val)) r).symm

/-- 実有限通常商の標準遷移射。 -/
def deltaPDivisionFiniteQuotientTransition (N : ℕ) :
    (L₀ ⧸ I₀ N) →+* (L₀ ⧸ I₀ (N + 1)) :=
  Ideal.Quotient.factor (deltaDivisionFiniteRelationIdeal_mono D (p : A) a₀ (Nat.le_succ N))

omit [Unique σ] in
/-- 商の標準遷移射は、元の自由環の標準商元を保つ。 -/
theorem deltaPDivisionFiniteQuotientTransition_mk (N : ℕ) (r : L₀) :
    deltaPDivisionFiniteQuotientTransition D y N (Ideal.Quotient.mk (I₀ N) r) =
      Ideal.Quotient.mk (I₀ (N + 1)) r :=
  Ideal.Quotient.factor_mk _ r

/-- 正規化した有限H⁰同型は、実Koszul遷移射と通常商の標準遷移射を比較する。 -/
theorem deltaPDivisionFiniteKoszulH0Equiv_transition (N : ℕ)
    (z : (SerrePositivity.koszulComplex (fun i : Fin (N + 1) => g₀ i.val)).homology 0) :
    deltaPDivisionFiniteKoszulH0Equiv D y (N + 1)
      ((HomologicalComplex.homologyMap (deltaPDivisionFiniteKoszulTransition D y N) 0).hom z) =
        deltaPDivisionFiniteQuotientTransition D y N
          (deltaPDivisionFiniteKoszulH0Equiv D y N z) := by
  obtain ⟨r, rfl⟩ := koszulH0Unit_surjective L₀ (fun i : Fin (N + 1) => g₀ i.val) z
  rw [deltaPDivisionFiniteKoszulTransition_unit, deltaPDivisionFiniteKoszulH0Equiv_unit,
    deltaPDivisionFiniteKoszulH0Equiv_unit, deltaPDivisionFiniteQuotientTransition_mk]

/-- 実有限Koszul複体を、その標準包含で繋いだ具体的な逐次図式。 -/
def deltaPDivisionFiniteKoszulDiagram :
    ℕ ⥤ CochainComplex (ModuleCat L₀) ℤ :=
  Functor.ofSequence (deltaPDivisionFiniteKoszulTransition D y)

/-- 逐次図式の隣接射は、定義した実Koszul標準遷移射。 -/
theorem deltaPDivisionFiniteKoszulDiagram_map_succ (N : ℕ) :
    (deltaPDivisionFiniteKoszulDiagram (σ := σ) D y).map (homOfLE (Nat.le_succ N)) =
      deltaPDivisionFiniteKoszulTransition D y N :=
  Functor.ofSequence_map_homOfLE_succ _ N

end SerrePositivity.BhattScholze
