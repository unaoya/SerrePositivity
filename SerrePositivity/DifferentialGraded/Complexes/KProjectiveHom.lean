module
public import SerrePositivity.DifferentialGraded.Complexes.Shift
public import SerrePositivity.HomologicalAlgebra.CochainAcyclic
public import Mathlib.Algebra.Homology.HomotopyCategory.KProjective
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # K-projective複体からの全次数線形Homのacyclic性

次数nのcycleを値域のn shiftへの閉零射に移し、通常のchain homotopyを戻す。
戻す際の微分の符号をn.negOnePowで補正する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A]

/-- K-projective複体からacyclic複体への全次数Homはacyclicである。 -/
lemma homComplex_acyclic_of_isKProjective (P N : Complex A) [P.IsKProjective]
    (hN : N.Acyclic) : (homComplex A P N).Acyclic := by
  intro n
  apply (HomologicalComplex.exactAt_iff' (K := homComplex A P N)
    (i := n - 1) (j := n) (k := n + 1) (by simp) (by simp)).2
  rw [ShortComplex.moduleCat_exact_iff]
  change ∀ z : Cochain P N n, δ n (n + 1) z = 0 →
    ∃ t : Cochain P N (n - 1), δ (n - 1) n t = z
  intro z hz
  let c : Cocycle P N n := Cocycle.mk z (n + 1) rfl hz
  let c' : Cocycle P (N⟦n⟧) 0 := c.rightShift n 0 (by omega)
  let f : P ⟶ N⟦n⟧ := Cocycle.homOf c'
  let h := IsKProjective.homotopyZero f (cochainAcyclic_shift hN n)
  refine ⟨n.negOnePow • (Cochain.ofHomotopy h).rightUnshift (n - 1) (by omega), ?_⟩
  rw [δ_units_smul, Cochain.δ_rightUnshift _ (n - 1) (by omega) n 0 (by omega),
    δ_ofHomotopy]
  simp only [Cochain.ofHom_zero, sub_zero, smul_smul, Int.units_mul_self, one_smul]
  change (Cochain.ofHom (Cocycle.homOf c')).rightUnshift n (by omega) = z
  have hc : Cochain.ofHom (Cocycle.homOf c') = c'.val := by
    exact congrArg Subtype.val (Cocycle.ofHom_homOf_eq_self c')
  rw [hc]
  exact Cochain.rightUnshift_rightShift z n 0 (by omega)

/-- 全次数Homによるacyclic性の判定はMathlibのK-projective条件も反映する。 -/
lemma isKProjective_of_homComplex_acyclic (P : Complex A)
    (hP : ∀ N : Complex A, N.Acyclic → (homComplex A P N).Acyclic) :
    P.IsKProjective where
  nonempty_homotopy_zero {L} f hL := by
    have he := (HomologicalComplex.exactAt_iff' (K := homComplex A P L)
      (i := -1) (j := 0) (k := 1) (by simp) (by simp)).1 (hP L hL 0)
    rw [ShortComplex.moduleCat_exact_iff] at he
    obtain ⟨t, ht⟩ := he (Cochain.ofHom f) (δ_ofHom f)
    refine ⟨(Cochain.equivHomotopy f 0).symm ⟨t, ?_⟩⟩
    rw [Cochain.ofHom_zero, add_zero]
    exact ht.symm

/-- 既存K-projective性と全次数線形Homの条件の同値。 -/
lemma isKProjective_iff_homComplex_acyclic (P : Complex A) :
    P.IsKProjective ↔ ∀ N : Complex A, N.Acyclic → (homComplex A P N).Acyclic :=
  ⟨fun _ N hN => homComplex_acyclic_of_isKProjective A P N hN,
    isKProjective_of_homComplex_acyclic A P⟩

end SerrePositivity.DifferentialGraded
