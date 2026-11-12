module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeBasisEquivalence
public import SerrePositivity.DifferentialGraded.Tensor.Graded
public import SerrePositivity.EInfinity.BarrattEccles.Theory.CellularWeights

/-!
# 次数を支配する基底の重みと K 平坦性

## 概要
Berger–Moerdijk 命題 4.1 のセル代数で、生成元の重みによる複体の上限を使う。

## 方針
重みから余鎖次数を引くと微分が高さを真に下げるので、既存の semifree 基底を使う。

## 規約
重みは自然数で、余鎖次数以上とする。

## 使われ方
セル代数の台の K 平坦性。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity

open CategoryTheory Limits HomologicalComplex DifferentialGraded

section CellWeights

variable {J : Type u} {earlier : J → J → Prop} (h : WellFounded earlier)
  (lower : J → ℕ) (terms : ∀ j, Finset (List {k : J // earlier k j}))

/-- The weights dominate the prescribed bounds and all monomials of each boundary. -/
def cellularWeightAbove : J → ℕ :=
  h.fix (fun j v => max (lower j)
    ((terms j).sup (fun m => (m.map (fun k => v k.val k.property)).sum) + 1))

lemma cellularWeightAbove_eq (j : J) :
    cellularWeightAbove h lower terms j = max (lower j)
      ((terms j).sup (fun m => (m.map (fun k => cellularWeightAbove h lower terms k.val)).sum)
        + 1) :=
  WellFounded.fix_eq h _ j

lemma le_cellularWeightAbove (j : J) :
    lower j ≤ cellularWeightAbove h lower terms j := by
  rw [cellularWeightAbove_eq]
  exact le_max_left _ _

lemma boundaryWeight_lt_cellularWeightAbove {j : J} {m : List {k : J // earlier k j}}
    (hm : m ∈ terms j) :
    (m.map (fun k => cellularWeightAbove h lower terms k.val)).sum <
      cellularWeightAbove h lower terms j := by
  rw [cellularWeightAbove_eq]
  exact (Nat.lt_succ_of_le (Finset.le_sup
    (f := fun l => (l.map (fun k => cellularWeightAbove h lower terms k.val)).sum) hm)).trans_le
      (le_max_right _ _)

end CellWeights

open SerrePositivity.InfinityCategories

variable {A : Type u} [CommRing A] {K : Complex A} {I : ℤ → Type u}
  (b : ∀ i, Module.Basis (I i) A (K.X i)) (w : ∀ i, I i → ℕ)
  (hb : ∀ i x, i ≤ (w i x : ℤ))
  (hd : ∀ i x y, y ∈ ((b (i + 1)).repr (K.d i (i + 1) (b i x))).support →
    w (i + 1) y ≤ w i x)

/-- Weight minus cochain degree is a natural-number height that decreases under the differential. -/
def weightedSemifreeBasis : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSemifreeBasis A K where
  Index := I
  basis := b
  height i x := Int.toNat ((w i x : ℤ) - i)
  lowering i x y hy := by
    have h₀ := hb i x
    have h₁ := hb (i + 1) y
    have h := hd i x y hy
    omega

include b w hb hd in
/-- A weight-stable basis with degree bounded by weight gives a K-flat complex. -/
lemma complexKFlat_of_weightedBasis : complexKFlat A K :=
  moduleSemifree_objectwiseKFlat A PUnit.{1} (fun _ _ => complexKFlat_unit A)
    (weightedSemifreeBasis b w hb hd).complexSemifree PUnit.unit

end SerrePositivity.EInfinity
