module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.PrefixAtZero
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.BoundaryFiltration
/-!
概要：正規化境界の列に現れる面項を、同じ全 Hom の合成として記述する。
方針：退化列の直和包含を通した theta の作用を、退化先の実列へ制限する。
規約：元の theta と退化作用素を保持し、高次 prefix は別の相殺式で処理する。
使われ方：実正規化段階と Dold–Kan のラベル係数の比較。
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

abbrev dgCoherentBarFaceLeftTerm {n : ℕ} (s : I _⦋n⦌) (q : ℕ) (i : Fin (n + 1)) :
    GradedHom R (ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F ⟨n, s⟩))
      (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F)) 0 :=
  compose R
    (x := ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F ⟨n, s⟩))
    (y := ForgetEnrichment.to (Complex R)
      (dgCoherentBarFamily R D F (dgCoherentBarDegeneracy s ⟨n - q, by omega⟩)))
    (z := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
    (dgCoherentBarFaceColumn R D F (I.σ ⟨n - q, by omega⟩ s) i)
    (dgCoherentBarDegeneracyBlock R D F s ⟨n - q, by omega⟩) rfl

abbrev dgCoherentBarFaceRightTerm {n : ℕ} (s : I _⦋n + 1⦌) (q : ℕ) (i : Fin (n + 1)) :
    GradedHom R (ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F ⟨n + 1, s⟩))
      (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F)) 0 :=
  compose R
    (x := ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F ⟨n + 1, s⟩))
    (y := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
    (z := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
    (dgCoherentBarNormalizationHomotopyGraded R D F q)
    (dgCoherentBarFaceColumn R D F s i) rfl

lemma dgCoherentBarTheta_comp_degeneracyColumn {n : ℕ} (s : I _⦋n⦌) (j : Fin (n + 1)) :
    compose R
      (x := ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F ⟨n, s⟩))
      (y := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
      (z := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
      (dgCoherentBarTheta R D F) (dgCoherentBarDegeneracyColumn R D F s j) rfl =
    compose R
      (x := ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F ⟨n, s⟩))
      (y := ForgetEnrichment.to (Complex R)
        (dgCoherentBarFamily R D F (dgCoherentBarDegeneracy s j)))
      (z := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
      (dgCoherentBarColumn R D F (dgCoherentBarDegeneracy s j))
      (dgCoherentBarDegeneracyBlock R D F s j) rfl := by
  unfold dgCoherentBarDegeneracyColumn
  rw [moduleHomClosedInsertion R D, dgCoherentBarTheta_restrict]

lemma dgCoherentBarTheta_comp_homotopyColumn {n : ℕ} (s : I _⦋n⦌)
    (q : ℕ) (hq : q ≤ n) :
    compose R
      (x := ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F ⟨n, s⟩))
      (y := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
      (z := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
      (dgCoherentBarTheta R D F) (dgCoherentBarNormalizationHomotopyColumn R D F q ⟨n, s⟩)
      (show (-1 : ℤ) + 1 = 0 from rfl) =
    ((q : ℤ) + 1).negOnePow • compose R
      (x := ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F ⟨n, s⟩))
      (y := ForgetEnrichment.to (Complex R)
        (dgCoherentBarFamily R D F (dgCoherentBarDegeneracy s ⟨n - q, by omega⟩)))
      (z := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
      (dgCoherentBarColumn R D F (dgCoherentBarDegeneracy s ⟨n - q, by omega⟩))
      (dgCoherentBarDegeneracyBlock R D F s ⟨n - q, by omega⟩) rfl := by
  have hh : dgCoherentBarNormalizationHomotopyColumn R D F q ⟨n, s⟩ =
      ((q : ℤ) + 1).negOnePow • dgCoherentBarDegeneracyColumn R D F s
        ⟨n - q, by omega⟩ := by
    simp only [dgCoherentBarNormalizationHomotopyColumn,
      show ¬n < q from by omega, ite_false]
  have hc := congrArg (fun z => compose R
    (x := ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F ⟨n, s⟩))
    (y := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
    (z := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
    (dgCoherentBarTheta R D F) z (show (-1 : ℤ) + 1 = 0 from rfl)) hh
  exact hc.trans ((compose_units_smul_right (A := R) (D := RightModule R D)
    (x := ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F ⟨n, s⟩))
    (y := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
    (z := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
    ((q : ℤ) + 1).negOnePow
    (dgCoherentBarTheta R D F) (dgCoherentBarDegeneracyColumn R D F s ⟨n - q, by omega⟩)
    (show (-1 : ℤ) + 1 = 0 from rfl)).trans
      (congrArg (fun z => ((q : ℤ) + 1).negOnePow • z)
        (dgCoherentBarTheta_comp_degeneracyColumn R D F s ⟨n - q, by omega⟩)))

end SerrePositivity.InfinityCategories
