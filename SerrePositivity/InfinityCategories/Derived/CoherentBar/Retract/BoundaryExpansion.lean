module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.BoundaryFaceTerms
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.CompositionExpansion
/-!
概要：退化への theta の列と元の列へのホモトピーを面和・prefix 和に分ける。
方針：元の列の定義を等号として固定してから、抽象的な有限和の合成則を適用する。
規約：全高次 prefix を分配し、係数・単体ラベル・合成次数を保持する。
使われ方：prefix 相殺の後に残る正規化境界の面項を同定する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))

lemma dgCoherentBarColumn_degeneracy_comp_expansion {n : ℕ} (s : I _⦋n⦌) (q : ℕ) :
    compose R
      (x := ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F ⟨n, s⟩))
      (y := ForgetEnrichment.to (Complex R)
        (dgCoherentBarFamily R D F (dgCoherentBarDegeneracy s ⟨n - q, by omega⟩)))
      (z := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
      (dgCoherentBarColumn R D F (dgCoherentBarDegeneracy s ⟨n - q, by omega⟩))
      (dgCoherentBarDegeneracyBlock R D F s ⟨n - q, by omega⟩) rfl =
    (∑ i : Fin (n + 1), ((n : ℤ) + 1 + (i.val : ℤ) + 1).negOnePow •
      dgCoherentBarFaceLeftTerm R D F s q i) +
    ((n : ℤ) + 1).negOnePow •
      ∑ k : Fin (n + 1), dgCoherentBarPrefixLeftTerm R D F s q k := by
  exact dgBarRetract_compose_finite_sum_left (R := R) (C := RightModule R D)
    (M := ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F ⟨n, s⟩))
    (N := ForgetEnrichment.to (Complex R)
      (dgCoherentBarFamily R D F ⟨n + 1, I.σ ⟨n - q, by omega⟩ s⟩))
    (P := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
    (fun i : Fin (n + 1) => ((n : ℤ) + 1 + (i.val : ℤ) + 1).negOnePow)
    ((n : ℤ) + 1).negOnePow
    (fun i => dgCoherentBarFaceColumn R D F (I.σ ⟨n - q, by omega⟩ s) i)
    (fun k => dgCoherentBarPrefixColumn R D F (I.σ ⟨n - q, by omega⟩ s) k.val (by omega))
    (dgCoherentBarDegeneracyBlock R D F s ⟨n - q, by omega⟩) rfl

lemma dgCoherentBarHomotopy_comp_column_expansion {n : ℕ} (s : I _⦋n + 1⦌) (q : ℕ) :
    compose R
      (x := ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F ⟨n + 1, s⟩))
      (y := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
      (z := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
      (dgCoherentBarNormalizationHomotopyGraded R D F q) (dgCoherentBarColumn R D F ⟨n + 1, s⟩)
      rfl =
    (∑ i : Fin (n + 1), ((n : ℤ) + 1 + (i.val : ℤ) + 1).negOnePow •
      dgCoherentBarFaceRightTerm R D F s q i) +
    ((n : ℤ) + 1).negOnePow •
      ∑ k : Fin (n + 1), dgCoherentBarPrefixRightTerm R D F s q k := by
  exact dgBarRetract_compose_finite_sum_right (R := R) (C := RightModule R D)
    (M := ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F ⟨n + 1, s⟩))
    (N := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
    (P := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
    (fun i : Fin (n + 1) => ((n : ℤ) + 1 + (i.val : ℤ) + 1).negOnePow)
    ((n : ℤ) + 1).negOnePow (fun i => dgCoherentBarFaceColumn R D F s i)
    (fun k => dgCoherentBarPrefixColumn R D F s k.val (by omega))
    (dgCoherentBarNormalizationHomotopyGraded R D F q) rfl

end SerrePositivity.InfinityCategories
