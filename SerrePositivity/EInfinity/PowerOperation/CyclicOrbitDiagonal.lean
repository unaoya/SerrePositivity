module

public import SerrePositivity.EInfinity.PowerOperation.CyclicOrbitResolutionCoordinates
public import SerrePositivity.EInfinity.PowerOperation.RegularOrbitDifferential
public import SerrePositivity.EInfinity.PowerOperation.CoproductZeroSupport
public import Mathlib.Data.Int.Interval

/-!
# 上有界 orbit 全複体の有限な対角線

DAG XIII Construction 2.2.6 の鎖模型比較の補助。
上有界係数と非正次数の解像度の直和全複体で、零でない項は有限区間に限られる。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory CategoryTheory.Limits CochainComplex
variable (p : ℕ) [NeZero p] (k : Type u) [CommRing k]

/-- 元の直和全複体の次数 n の対角線。 -/
abbrev CyclicOrbitDiagonal (n : ℤ) := {q : ℤ × ℤ // q.1 + q.2 = n}

/-- 元の二重複体の同じ対角成分。 -/
def cyclicOrbitDiagonalSummand
    (M : CochainComplex (Rep.{u} k (PowerOperationCyclicGroup.{u} p)) ℤ)
    (n : ℤ) (q : CyclicOrbitDiagonal n) : ModuleCat.{u} k :=
  ((Rep.coinvariantsTensor k (PowerOperationCyclicGroup.{u} p)).obj (M.X q.1.1)).obj
    ((cyclicOrbitResolution p k).X q.1.2)

/-- 上有界係数の支持の外では、元の対角成分が零対象。 -/
lemma cyclicOrbitDiagonalSummand_isZero
    (M : CochainComplex (Rep.{u} k (PowerOperationCyclicGroup.{u} p)) ℤ)
    (d : ℤ) [M.IsStrictlyLE d] (n : ℤ) (q : CyclicOrbitDiagonal n)
    (hq : ¬ (q.1.2 ≤ 0 ∧ q.1.1 ≤ d)) :
    IsZero (cyclicOrbitDiagonalSummand p k M n q) := by
  by_cases h : q.1.2 ≤ 0
  · have hm : d < q.1.1 := by omega
    exact ((Rep.coinvariantsTensor k (PowerOperationCyclicGroup.{u} p)).flip.obj
      ((cyclicOrbitResolution p k).X q.1.2)).map_isZero
        (M.isZero_of_isStrictlyLE d q.1.1 hm)
  · exact ((Rep.coinvariantsTensor k (PowerOperationCyclicGroup.{u} p)).obj
      (M.X q.1.1)).map_isZero (cyclicOrbitResolution_isZero_positive p k q.1.2 (by omega))

/-- 支持する対角線は、Hom 側と同じ有限区間で添字付けられる。 -/
def cyclicOrbitFiniteDiagonalEquiv (d n : ℤ) :
    {q : CyclicOrbitDiagonal n // q.1.2 ≤ 0 ∧ q.1.1 ≤ d} ≃
      {s : ℤ // s ∈ Finset.Icc 0 (d - n)} where
  toFun q := ⟨-q.1.1.2, Finset.mem_Icc.mpr (by have h := q.1.2; have h' := q.2; omega)⟩
  invFun s := ⟨⟨(s.1 + n, -s.1), by simp⟩, by
    have h := Finset.mem_Icc.mp s.2
    dsimp
    omega⟩
  left_inv q := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext <;> dsimp
    · have h := q.1.2; omega
    · omega
  right_inv s := by
    apply Subtype.ext
    dsimp
    omega

end SerrePositivity.EInfinity.PowerOperation
