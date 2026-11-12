module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.LeftPrismCutMinimumMaps

/-!
概要：cone の正頂点への path の移送は、元の path の包含圏と厳密に同型。
方針：succ の逆像で path を戻し、初点より上の全点が正であることを使う。
規約：nerve の同型を明示し、Hom の表示変更で打ち消せる射を与える。
使われ方：左区間の対角単体の退化を tail に使い、元の cone の Hom の合成則へ移す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SimplicialThickening SSet
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial

/-- 正頂点間の path の succ による逆像を取る。 -/
def pathPositiveUnshift {n : ℕ} {i j : Fin (n + 1)}
    (P : Path (ULift.up i.succ : ULift.{u} (Fin (n + 2))) (ULift.up j.succ)) :
    Path (ULift.up i : ULift.{u} (Fin (n + 1))) (ULift.up j) where
  I := {k | ULift.up k.down.succ ∈ P.I}
  left := P.left
  right := P.right
  left_le k hk := Fin.succ_le_succ_iff.mp (P.left_le (ULift.up k.down.succ) hk)
  le_right k hk := Fin.succ_le_succ_iff.mp (P.le_right (ULift.up k.down.succ) hk)

/-- 正頂点からの逆移送は path の包含に自然。 -/
def pathPositiveUnshiftFunctor {n : ℕ} (i j : Fin (n + 1)) :
    Path (ULift.up i.succ : ULift.{u} (Fin (n + 2))) (ULift.up j.succ) ⥤
      Path (ULift.up i : ULift.{u} (Fin (n + 1))) (ULift.up j) where
  obj := pathPositiveUnshift
  map f := ⟨⟨⟨fun _ hk => f.1.1.1 hk⟩⟩⟩

/-- 正頂点へ移して戻すと、元の path の点集合を厳密に回収する。 -/
lemma pathPositiveUnshift_shift {n : ℕ} {i j : Fin (n + 1)}
    (P : Path (ULift.up i : ULift.{u} (Fin (n + 1))) (ULift.up j)) :
    pathPositiveUnshift (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pathPositiveShift P) = P := by
  apply SimplicialThickening.Path.ext
  ext k
  constructor
  · rintro ⟨l, hl, he⟩
    have h : l = k := ULift.ext (Fin.succ_inj.mp (ULift.ext_iff.mp he))
    simpa only [h] using hl
  · intro hk
    exact ⟨k, hk, rfl⟩

/-- 戻して正頂点へ移すと、元の正頂点間の path の全点を厳密に回収する。 -/
lemma pathPositiveShift_unshift {n : ℕ} {i j : Fin (n + 1)}
    (P : Path (ULift.up i.succ : ULift.{u} (Fin (n + 2))) (ULift.up j.succ)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pathPositiveShift (pathPositiveUnshift P) = P := by
  apply SimplicialThickening.Path.ext
  ext k
  constructor
  · rintro ⟨l, hl, he⟩
    exact he ▸ hl
  · intro hk
    rcases k with ⟨k⟩
    induction k using Fin.cases with
    | zero =>
      have h := P.left_le _ hk
      change i.succ ≤ 0 at h
      simp at h
    | succ k => exact ⟨ULift.up k, hk, rfl⟩

/-- 正頂点への移送の nerve は、明示した逆移送を逆とする単体集合の同型。 -/
def pathPositiveShiftIso {n : ℕ} (i j : Fin (n + 1)) :
    nerve (Path (ULift.up i : ULift.{u} (Fin (n + 1))) (ULift.up j)) ≅
      nerve (Path (ULift.up i.succ : ULift.{u} (Fin (n + 2))) (ULift.up j.succ)) where
  hom := nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pathPositiveShiftFunctor i j)
  inv := nerveMap (pathPositiveUnshiftFunctor i j)
  hom_inv_id := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro P
    apply CategoryTheory.Functor.ext (fun k => pathPositiveUnshift_shift (P.obj k))
  inv_hom_id := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro P
    apply CategoryTheory.Functor.ext (fun k => pathPositiveShift_unshift (P.obj k))

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial
