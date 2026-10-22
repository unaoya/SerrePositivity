module
public import SerrePositivity.InfinityCategories.Stable.ExcisionGridRowColumnSources
public import SerrePositivity.InfinityCategories.Stable.ExcisionGridZeroValues

/-!
概要：元の二頂点と指定零頂点を保つ実 suspension 模型。
方針：同じ実図式の貼り合わせ・全パラメーターの評価・普遍的な切断比較を使う。
規約：一般安定性を先取りしない。使われ方：HA 1.4.2.15 の実 θ の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

lemma ExcisionSquareGrid.row_outer_zero_left {X : SSet.{u}}
    {R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X} {z : X _⦋0⦌} (d : ExcisionSquareGrid R z) :
    squareVertex (strip3Square (excisionGridRowStrip ≫ d.extension.full) 1 1) 0 1 = z := by
  let p : ExcisionGridSeedIndex.{u} :=
    ⟨excisionGridCorePoint 0 2, by change (0 : ℕ) + 2 ≤ 2; decide⟩
  exact d.zero_seed_full (nerveVertex p) (by
    change ¬ ((0 : ℕ) ≤ 1 ∧ (2 : ℕ) ≤ 1)
    decide)

lemma ExcisionSquareGrid.column_outer_zero_left {X : SSet.{u}}
    {R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X} {z : X _⦋0⦌} (d : ExcisionSquareGrid R z) :
    squareVertex (strip3Square (excisionGridColumnStrip ≫ d.extension.full) 1 1) 0 1 = z := by
  let p : ExcisionGridSeedIndex.{u} :=
    ⟨excisionGridCorePoint 2 0, by change (2 : ℕ) + 0 ≤ 2; decide⟩
  exact d.zero_seed_full (nerveVertex p) (by
    change ¬ ((2 : ℕ) ≤ 1 ∧ (0 : ℕ) ≤ 1)
    decide)

def ExcisionSquareGrid.row_suspension {X : SSet.{u}} [Quasicategory X]
    {R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X} {z : X _⦋0⦌} (d : ExcisionSquareGrid R z)
    (hz : IsZeroVertex z) : SuspensionSquare (squareVertex R 0 1) where
  square := strip3Square (excisionGridRowStrip ≫ d.extension.full) 1 1
  zero_corner := by rw [d.row_outer_zero_left]; exact hz
  source_eq := d.row_outer_source
  other_zero := by
    change IsZeroVertex (d.extension.full.app (Opposite.op ⦋0⦌)
      (nerveVertex excisionGridFirstNewZero.val))
    rw [d.extension.first_new_zero]
    exact hz
  isPushout := d.extension.row_outer_pushout

def ExcisionSquareGrid.column_suspension {X : SSet.{u}} [Quasicategory X]
    {R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X} {z : X _⦋0⦌} (d : ExcisionSquareGrid R z)
    (hz : IsZeroVertex z) : SuspensionSquare (squareVertex R 1 0) where
  square := strip3Square (excisionGridColumnStrip ≫ d.extension.full) 1 1
  zero_corner := by rw [d.column_outer_zero_left]; exact hz
  source_eq := d.column_outer_source
  other_zero := by
    change IsZeroVertex (d.extension.full.app (Opposite.op ⦋0⦌)
      (nerveVertex excisionGridSecondNewZero.val))
    rw [d.extension.second_new_zero]
    exact hz
  isPushout := d.extension.column_outer_pushout

lemma ExcisionSquareGrid.row_suspension_vertex {X : SSet.{u}} [Quasicategory X]
    {R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X} {z : X _⦋0⦌} (d : ExcisionSquareGrid R z)
    (hz : IsZeroVertex z) : (d.row_suspension hz).vertex =
      d.extension.full.app (Opposite.op ⦋0⦌) (nerveVertex excisionGridPoint32) := rfl

lemma ExcisionSquareGrid.column_suspension_vertex {X : SSet.{u}} [Quasicategory X]
    {R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X} {z : X _⦋0⦌} (d : ExcisionSquareGrid R z)
    (hz : IsZeroVertex z) : (d.column_suspension hz).vertex =
      d.extension.full.app (Opposite.op ⦋0⦌)
        (nerveVertex (excisionGridTranspose excisionGridPoint32)) := rfl

end SerrePositivity.InfinityCategories
