module
public import SerrePositivity.KST.Spectra.FibrationExactness

/-!
概要：長完全列による fiber の正次数消滅と射影の単射・全射。
方針：完全性を基点の逆像として使い、正次数では群準同型の核を判定する。
規約：n は KanHomotopy の実次数。
使われ方：Sp-8 (3)、厳密引き戻しの共終性供給。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.KST.LocalizingInvariants.CoreFlag
open Spectra

/-- 全空間の消滅と底の二以上の消滅から、fiber の正次数が消滅する。 -/
lemma fibration_positive_fiber_subsingleton {E B : SSet.{u}}
    [KanComplex E] [KanComplex B] (p : E ⟶ B) [Fibration p]
    (hE : ∀ n (e : E _⦋0⦌), Subsingleton (KanHomotopy E n e))
    (hB : ∀ n, 1 < n → ∀ b : B _⦋0⦌, Subsingleton (KanHomotopy B n b))
    (e : E _⦋0⦌) (n : ℕ) (hn : 0 < n) :
    Subsingleton (KanHomotopy (KanFiber p (p.app _ e)) n (fiberPoint p e)) := by
  have hzero (a : KanHomotopy (KanFiber p (p.app _ e)) n (fiberPoint p e)) :
      a = KanHomotopy.point n := by
    have := hE n e
    have hι : KanHomotopy.map n (fiberι p (p.app _ e)) (fiberι_point p e) a =
        KanHomotopy.point n := Subsingleton.elim _ _
    obtain ⟨b, hb⟩ := (exact_connecting_fiber_all p e n a).mp hι
    have : Subsingleton (KanHomotopyGroup B n (p.app _ e)) := hB (n + 1) (by omega) _
    have hb1 : b = 1 := Subsingleton.elim _ _
    exact hb.symm.trans (by rw [hb1, connecting_one])
  exact ⟨fun a b ↦ (hzero a).trans (hzero b).symm⟩

/-- 指定次数の fiber の消滅は同次数の射影の単射性を与える。 -/
lemma fibration_map_injective_of_fiber_subsingleton {E B : SSet.{u}}
    [KanComplex E] [KanComplex B] (p : E ⟶ B) [Fibration p]
    (e : E _⦋0⦌) (n : ℕ) (hn : 0 < n)
    (hf : Subsingleton (KanHomotopy (KanFiber p (p.app _ e)) n (fiberPoint p e))) :
    Function.Injective (KanHomotopy.map n p (x := e) rfl) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  change Function.Injective (KanHomotopyGroup.map (n := k) p (x := e) rfl)
  apply (injective_iff_map_eq_one _).mpr
  intro a ha
  obtain ⟨b, hb⟩ := (exact_fiber_total p e k a).mp ha
  have : Subsingleton (KanHomotopyGroup (KanFiber p (p.app _ e)) k (fiberPoint p e)) := hf
  have hb1 : b = 1 := Subsingleton.elim _ _
  rw [hb1, map_one] at hb
  exact hb.symm

/-- 一つ下の次数の fiber の消滅は射影の全射性を与える。 -/
lemma fibration_map_surjective_of_fiber_subsingleton {E B : SSet.{u}}
    [KanComplex E] [KanComplex B] (p : E ⟶ B) [Fibration p]
    (e : E _⦋0⦌) (n : ℕ)
    (hf : Subsingleton (KanHomotopy (KanFiber p (p.app _ e)) n (fiberPoint p e))) :
    Function.Surjective (KanHomotopy.map (n + 1) p (x := e) rfl) := by
  intro a
  exact (exact_total_base_all p e n a).mp (by have := hf; exact Subsingleton.elim _ _)

end SerrePositivity.KST.LocalizingInvariants.CoreFlag
