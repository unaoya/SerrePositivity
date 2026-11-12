module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.PathCutMinimumComposition
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.LeftPrismCutCoordinates

/-!
概要：時間切断後の最小点と、native な左 Hom prism の同じ座標を同定する。
方針：零の頂点を初点へ潰した path の最初の正頂点を、元の時刻一部分の最小点と比較する。
規約：左区間の元の切断写像を使い、右区間の座標とは同一視しない。
使われ方：weighted cone の混合 Hom と、実際の左区間の共同評価との厳密な照合。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SimplicialThickening SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations


/-- 左切断の像の最初の正頂点は、元の path の時刻一部分の最小点。 -/
lemma pathCutMinimum_eq_pathFirstMinimum {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    {i j : Fin (n + 1)} (hj : t j = 1)
    (R : Path (ULift.up i : ULift.{u} (Fin (n + 1))) (ULift.up j))
    (P : Path (ULift.up i.succ : ULift.{u} (Fin (n + 2))) (ULift.up j.succ))
    (Q : Path (ULift.up 0 : ULift.{u} (Fin (n + 2))) (ULift.up j.succ))
    (hP : P.I = (fun k : ULift.{u} (Fin (n + 1)) => ULift.up k.down.succ) '' R.I)
    (hQ : Q.I = (fun k : ULift.{u} (Fin (n + 1)) =>
      ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.coherentLeftPrismCut t k.down)) '' R.I) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMinimum t hj P = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.pathFirstMinimum Q := by
  have hOne (k : Fin (n + 1)) (hk : t k = 1) : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.coherentLeftPrismCut t k = k.succ := by
    change (if t k = 0 then 0 else k.succ) = k.succ
    exact ite_eq_right (by rw [hk]; decide)
  apply le_antisymm
  · have hm := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.pathFirstMinimum_mem Q
    rw [hQ] at hm
    obtain ⟨⟨k⟩, hk, he⟩ := hm
    by_cases ht : t k = 0
    · have he' := congrArg (fun a : ULift.{u} (Fin (n + 2)) => a.down.val) he
      change (if t k = 0 then 0 else k.succ).val = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.pathFirstMinimum Q).val + 1 at he'
      rw [ite_eq_left ht] at he'
      change 0 = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.pathFirstMinimum Q).val + 1 at he'
      omega
    · have ht' : t k = 1 := Fin.ext (by have h := (t k).isLt; omega)
      have he' : k = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.pathFirstMinimum Q := by
        apply Fin.succ_inj.mp
        exact (hOne k ht').symm.trans (ULift.ext_iff.mp he)
      rw [← he']
      apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMinimum_le t hj P k ht'
      rw [hP]
      exact ⟨ULift.up k, hk, rfl⟩
  · have hm := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMinimum_spec t hj P
    have hp := hm.2
    rw [hP] at hp
    obtain ⟨⟨k⟩, hk, he⟩ := hp
    have he' : k = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMinimum t hj P := Fin.succ_inj.mp (ULift.ext_iff.mp he)
    subst k
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.pathFirstMinimum_le
    rw [hQ]
    exact ⟨ULift.up _, hk, congrArg ULift.up (hOne _ hm.1)⟩

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
