module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.LastBoundaryParts
/-!
概要：最後の正規化境界でも最初の面と prefix 単位項が相殺し、残る正の面だけで計算できる。
方針：有限和の先頭を取り出し、隣接する次数符号の反対性で消す。
規約：元の閉境界を計算し、正規化段階の安定性を仮定しない。
使われ方：段階作用素と Dold–Kan の始点保存係数の全段階比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial

private lemma cancel_first_face {A : Type*} [AddCommGroup A] {m : ℕ}
    (a : ℤˣ) (c : Fin (m + 1) → ℤˣ) (f : Fin (m + 1) → A)
    (hc : c 0 = -a) :
    a • ((∑ i, c i • f i) + a • f 0) =
      a • ∑ i : Fin m, c i.succ • f i.succ := by
  congr 1
  rw [Fin.sum_univ_succ, hc]
  simp only [Units.smul_def, Units.val_neg, neg_zsmul]
  abel

variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))

lemma dgCoherentBarNormalizationBoundary_restrict_last_faces {n : ℕ}
    (s : I _⦋n + 1⦌) :
    (eHomWhiskerRight (Complex R)
      (Sigma.ι (dgCoherentBarFamily R D F) ⟨n + 1, s⟩)
      (dgCoherentBarGraded R D F)).f 0
      (dgCoherentBarNormalizationBoundaryGraded R D F (n + 1)) =
    (((n + 1 : ℕ) : ℤ) + 1).negOnePow •
      ∑ i : Fin (n + 1),
        (((n + 1 : ℕ) : ℤ) + 1 + (i.succ.val : ℤ) + 1).negOnePow •
          dgCoherentBarFaceLeftTerm R D F s (n + 1) i.succ := by
  have hc :
      (((n + 1 : ℕ) : ℤ) + 1 + ((0 : Fin (n + 2)).val : ℤ) + 1).negOnePow =
        -(((n + 1 : ℕ) : ℤ) + 1).negOnePow := by
    change ((((n + 1 : ℕ) : ℤ) + 1) + 1).negOnePow = _
    rw [Int.negOnePow_add]
    simp
  exact (dgCoherentBarNormalizationBoundary_restrict_last_parts R D F s).trans
    (cancel_first_face (((n + 1 : ℕ) : ℤ) + 1).negOnePow
      (fun i : Fin (n + 2) => (((n + 1 : ℕ) : ℤ) + 1 + (i.val : ℤ) + 1).negOnePow)
      (fun i => dgCoherentBarFaceLeftTerm R D F s (n + 1) i) hc)

end SerrePositivity.InfinityCategories
