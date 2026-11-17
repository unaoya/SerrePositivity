module

public import SerrePositivity.AlgebraicGeometry.RectangularCechOpenRows
public import SerrePositivity.AlgebraicGeometry.OpenCoverCech

/-!
概要：元の full Čech のタプルの有限像の交叉を、同じ矩形タプルの開へ移す。
方針：有限像と全座標の交叉を一致させ、有限交叉と逆像の交換を使う。
規約：重複を持つ元のタプルと実際の交叉を保持する。
使われ方：元の二重 Čech の行への係数比較の代入。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry Opposite TopologicalSpace
universe u

/-- タプルの有限像の交叉は、重複も含む同じ全座標の交叉。 -/
theorem cechOpenIntersection_tupleSupport_eq_iInf {X : Type u} [TopologicalSpace X]
    {ι : Type} [DecidableEq ι] (U : ι → Opens X) {k : ℕ} (t : Fin k → ι) :
    cechOpenIntersection U (cechTupleSupport t) = ⨅ j, U (t j) := by
  apply le_antisymm
  · apply le_iInf
    intro j
    exact iInf_le_of_le (t j) (iInf_le_of_le
      (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩) le_rfl)
  · apply le_iInf
    intro i
    apply le_iInf
    intro hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
    exact iInf_le _ j

/-- 元の full Čech の交叉を、同じ矩形タプルの転置で表す。 -/
theorem schemeCechTupleIntersection_rectangular {Y S : Scheme.{u}}
    (f : Y ⟶ S) {ι : Type} [DecidableEq ι] (U : ι → Y.Opens)
    (n : SimplexCategory) (k : ℕ) (q : Fin (k + 1) → Fin (n.len + 1) → ι) :
    cechOpenIntersection (schemeCechTupleOpen f U (op n)) (cechTupleSupport q) =
      schemeCechTupleOpen f (fun a : Fin (k + 1) → ι ↦ ⨅ r, U (a r))
        (op n) (fun j r ↦ q r j) := by
  rw [cechOpenIntersection_tupleSupport_eq_iInf]
  exact (schemeCechTupleOpen_iInf f U n (fun j r ↦ q r j)).symm

/-- 元の全座標の交叉は、同じタプルの再添字付けによる交叉に含まれる。 -/
theorem openIntersectionFamily_refinement {X : Type u} [TopologicalSpace X]
    {ι κ τ : Type} (U : ι → Opens X) (a : κ → τ) (t : τ → ι) :
    (⨅ r, U (t r)) ≤ ⨅ r, U (t (a r)) :=
  le_iInf (fun r ↦ iInf_le _ (a r))

end SerrePositivity.AlgebraicGeometry
