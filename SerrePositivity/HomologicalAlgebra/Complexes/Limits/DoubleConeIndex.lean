module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.NerveCone
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Index

/-!
概要：元の単体作用素を、実二重 cone の両端を保つ作用素へ延長する。
方針：既存の始点固定延長と終点固定延長を順に合成する。
規約：既存の二つの添字構成を再利用する。使われ方：二重 cone の全自然性。
-/
@[expose] public section
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory
open _root_.SerrePositivity.InfinityCategories
open scoped _root_.Simplicial

def doubleConeOrderHom {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) : Fin (m + 3) →o Fin (n + 3) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom θ.toOrderHom)

lemma doubleConeOrderHom_castSucc {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) (i : Fin (m + 2)) :
    _root_.SerrePositivity.ComplexLimits.doubleConeOrderHom θ i.castSucc = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom θ.toOrderHom i).castSucc :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom_castSucc _ i

lemma doubleConeOrderHom_last {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    _root_.SerrePositivity.ComplexLimits.doubleConeOrderHom θ (Fin.last (m + 2)) = Fin.last (n + 2) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom_last _

lemma doubleConeOrderHom_eq_last_iff {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) (i : Fin (m + 3)) :
    _root_.SerrePositivity.ComplexLimits.doubleConeOrderHom θ i = Fin.last (n + 2) ↔ i = Fin.last (m + 2) := by
  induction i using Fin.lastCases with
  | last => simp only [_root_.SerrePositivity.ComplexLimits.doubleConeOrderHom_last]
  | cast i =>
    rw [_root_.SerrePositivity.ComplexLimits.doubleConeOrderHom_castSucc]
    simp only [Fin.castSucc_ne_last]

lemma doubleConeOrderHom_predAbove {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (i : Fin (m + 3)) (hi : i ≠ Fin.last (m + 2)) :
    (Fin.last (n + 1)).predAboveOrderHom (_root_.SerrePositivity.ComplexLimits.doubleConeOrderHom θ i) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom θ.toOrderHom ((Fin.last (m + 1)).predAboveOrderHom i) := by
  induction i using Fin.lastCases with
  | last => exact False.elim (hi rfl)
  | cast i =>
    rw [_root_.SerrePositivity.ComplexLimits.doubleConeOrderHom_castSucc]
    exact (Fin.predAbove_last_castSucc).trans
      (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom θ.toOrderHom) Fin.predAbove_last_castSucc.symm)

end SerrePositivity.ComplexLimits
