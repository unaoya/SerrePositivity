module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridRowColumnSources
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridZeroValues

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
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

lemma ExcisionSquareGrid.row_outer_zero_left {X : SSet.{u}}
    {R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X} {z : X _⦋0⦌} (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionSquareGrid R z) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.strip3Square (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridRowStrip ≫ d.extension.full) 1 1) 0 1 = z := by
  let p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridSeedIndex.{u} :=
    ⟨_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCorePoint 0 2, by change (0 : ℕ) + 2 ≤ 2; decide⟩
  exact d.zero_seed_full (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex p) (by
    change ¬ ((0 : ℕ) ≤ 1 ∧ (2 : ℕ) ≤ 1)
    decide)

lemma ExcisionSquareGrid.column_outer_zero_left {X : SSet.{u}}
    {R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X} {z : X _⦋0⦌} (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionSquareGrid R z) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.strip3Square (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridColumnStrip ≫ d.extension.full) 1 1) 0 1 = z := by
  let p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridSeedIndex.{u} :=
    ⟨_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCorePoint 2 0, by change (2 : ℕ) + 0 ≤ 2; decide⟩
  exact d.zero_seed_full (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex p) (by
    change ¬ ((2 : ℕ) ≤ 1 ∧ (0 : ℕ) ≤ 1)
    decide)

def ExcisionSquareGrid.row_suspension {X : SSet.{u}} [Quasicategory X]
    {R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X} {z : X _⦋0⦌} (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionSquareGrid R z)
    (hz : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex z) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex R 0 1) where
  square := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.strip3Square (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridRowStrip ≫ d.extension.full) 1 1
  zero_corner := by rw [d.row_outer_zero_left]; exact hz
  source_eq := d.row_outer_source
  other_zero := by
    change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (d.extension.full.app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridFirstNewZero.val))
    rw [d.extension.first_new_zero]
    exact hz
  isPushout := d.extension.row_outer_pushout

def ExcisionSquareGrid.column_suspension {X : SSet.{u}} [Quasicategory X]
    {R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X} {z : X _⦋0⦌} (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionSquareGrid R z)
    (hz : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex z) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex R 1 0) where
  square := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.strip3Square (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridColumnStrip ≫ d.extension.full) 1 1
  zero_corner := by rw [d.column_outer_zero_left]; exact hz
  source_eq := d.column_outer_source
  other_zero := by
    change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (d.extension.full.app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSecondNewZero.val))
    rw [d.extension.second_new_zero]
    exact hz
  isPushout := d.extension.column_outer_pushout

lemma ExcisionSquareGrid.row_suspension_vertex {X : SSet.{u}} [Quasicategory X]
    {R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X} {z : X _⦋0⦌} (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionSquareGrid R z)
    (hz : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex z) : (d.row_suspension hz).vertex =
      d.extension.full.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridPoint32) := rfl

lemma ExcisionSquareGrid.column_suspension_vertex {X : SSet.{u}} [Quasicategory X]
    {R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X} {z : X _⦋0⦌} (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionSquareGrid R z)
    (hz : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex z) : (d.column_suspension hz).vertex =
      d.extension.full.app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridTranspose _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridPoint32)) := rfl

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
