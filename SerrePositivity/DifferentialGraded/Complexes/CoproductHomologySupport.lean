module
public import SerrePositivity.DifferentialGraded.Complexes.CoproductSupport
public import SerrePositivity.DifferentialGraded.Category.HomotopyHomologyNaturality

/-! # 余積の次数零ホモロジー類の有限support表示 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits HomologicalComplex
variable (A : Type u) [CommRing A]

def complexZeroHomologyClassLinearMap (K : Complex A) : zeroCycles K →ₗ[A] K.homology 0 :=
  (complexZeroHomologyQuotientIso A K).hom.hom.comp (Submodule.mkQ _)

lemma complexZeroHomologyClass_surjective (K : Complex A) :
    Function.Surjective (complexZeroHomologyClass A K) := by
  intro z
  obtain ⟨c, hc⟩ := Quotient.exists_rep ((complexZeroHomologyQuotientIso A K).inv z)
  refine ⟨c, ?_⟩
  change (complexZeroHomologyQuotientIso A K).hom (Quotient.mk _ c) = z
  rw [hc, ← ModuleCat.comp_apply, Iso.inv_hom_id, ModuleCat.id_apply]

lemma complexZeroHomologyClass_sum {J : Type*} (K : Complex A) (t : Finset J)
    (c : J → zeroCycles K) :
    complexZeroHomologyClass A K (∑ j ∈ t, c j) = ∑ j ∈ t, complexZeroHomologyClass A K (c j) :=
  map_sum (complexZeroHomologyClassLinearMap A K) c t

/-- 任意の非有界複体族の余積のH⁰は、有限個の成分H⁰の像の和で生成される。 -/
lemma complexCofan_zeroHomology_rep {J : Type u} (F : J → Complex A) (s : Cofan F)
    (hs : IsColimit s) (z : s.pt.homology 0) :
    ∃ (t : Finset J) (c : ∀ j, (F j).homology 0),
      ∑ j ∈ t, homologyMap (s.inj j) 0 (c j) = z := by
  classical
  obtain ⟨a, rfl⟩ := complexZeroHomologyClass_surjective A s.pt z
  obtain ⟨t, c, hc⟩ := complexCofan_cycle_rep A F s hs 0 a
  have h : ∑ j ∈ t, complexMapZeroCycle A (s.inj j) (c j) = a := by
    apply Subtype.ext
    change (zeroCycles s.pt).subtype (∑ j ∈ t, complexMapZeroCycle A (s.inj j) (c j)) = a.val
    rw [map_sum]
    exact hc
  refine ⟨t, fun j => complexZeroHomologyClass A (F j) (c j), ?_⟩
  simp only [complexZeroHomologyClass_naturality]
  rw [← complexZeroHomologyClass_sum, h]

end SerrePositivity.DifferentialGraded
