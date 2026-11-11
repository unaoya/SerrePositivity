module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.TailAfterComparison
/-!
概要：正規化段の退化位置は、前側で切断した tail の正規化退化位置へ移る。
方針：次数付き単体の全体に退化先を定義し、加法表示した厳密な tail 比較を輸送する。
規約：次数の等号と元の単体ラベルを保持する。
使われ方：prefix の二つの合成で現れる最終直和包含を同定する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract
open CategoryTheory SSet
open scoped _root_.Simplicial
variable {I : SSet.{u}}

def dgCoherentBarDegeneracyAt (q : ℕ) (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarIndex I) : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarIndex I :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarDegeneracy s.2 ⟨s.1 - q, by omega⟩

lemma dgCoherentBarTail_degeneracy_at {n : ℕ} (s : I _⦋n⦌)
    (q r : ℕ) (hr : r ≤ n - q) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTail (I.σ ⟨n - q, by omega⟩ s) r (by omega) =
      dgCoherentBarDegeneracyAt q (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTail s r (by omega)) := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le (show r ≤ n by omega)
  have h := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarTail_degeneracy_after r a ⟨a - q, by omega⟩ s
  have hi : (⟨r + a - q, by omega⟩ : Fin (r + a + 1)) =
      ⟨r + (a - q), by omega⟩ := by
    apply Fin.ext
    change r + a - q = r + (a - q)
    omega
  rw [hi]
  have ht := congrArg (dgCoherentBarDegeneracyAt (I := I) q) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarTail_after r a s)
  exact h.trans ht.symm

variable (R : Type u) [CommRing R] (D : Type v)
  [DifferentialGraded.DGCategory R D] [Small.{u} D]
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (DifferentialGraded.RightModule R D))

set_option maxHeartbeats 1600000 in
-- 直和 Hom end の eta 比較を伴う端点照合に限った上限。
lemma dgCoherentBarDegeneracyAt_column (t : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarIndex I) (q : ℕ) :
    (eHomWhiskerLeft (DifferentialGraded.Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F t)
      (Limits.Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F) (dgCoherentBarDegeneracyAt q t))).f (-1)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarDegeneracyBlock R D F t.2 ⟨t.1 - q, by omega⟩) =
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarDegeneracyColumn R D F t.2 ⟨t.1 - q, by omega⟩ := by
  rcases t with ⟨n, s⟩
  rfl

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract
