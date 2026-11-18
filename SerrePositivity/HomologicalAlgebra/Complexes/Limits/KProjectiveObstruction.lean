module

public import Mathlib.Algebra.Homology.HomotopyCategory.KProjective
public import Mathlib.Algebra.Homology.ModelCategory.Lifting

/-!
# 射影複体の持ち上げ障害の消滅

概要：K-projective 複体から非輪状複体への全 cocycle は coboundary。
方針：始域をシフトし、元の鎖写像の零ホモトピーを cochain へ戻す。
規約：任意のアーベル圏で全整数次数を扱う。
使われ方：正規化境界の射影 cofibration 判定。
-/

@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.CochainComplex _root_.CochainComplex.HomComplex
variable {C : Type u} [Category.{v} C] [Abelian C]

set_option backward.defeqAttrib.useBackward true in
lemma kProjective_eq_delta_of_cocycle {K L : CochainComplex C ℤ} {n : ℤ}
    (z : Cocycle K L n) [K.IsKProjective] (hL : L.Acyclic) (m : ℤ) (hm : m + 1 = n) :
    ∃ (α : Cochain K L m), δ m n α = z.1 := by
  obtain ⟨φ, hφ⟩ := (Cocycle.equivHom ..).surjective (z.leftShift (-n) 0 (add_neg_cancel n))
  rw [Cocycle.ext_iff] at hφ
  dsimp at hφ
  obtain ⟨h⟩ := IsKProjective.nonempty_homotopy_zero φ hL
  obtain ⟨f, hf⟩ := Cochain.equivHomotopy _ _ h
  simp only [Int.reduceNeg, Cochain.ofHom_zero, add_zero] at hf
  refine ⟨(-n).negOnePow • Cochain.leftUnshift f m (by omega), ?_⟩
  rw [δ_units_smul, Cochain.δ_leftUnshift _ _ _ _ 0 (by omega), ← hf, hφ]
  simp [smul_smul]

end SerrePositivity.ComplexLimits
