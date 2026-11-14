module

public import SerrePositivity.EInfinity.SimplexCuts.PreviousVertexPositions
public import SerrePositivity.EInfinity.IntervalCuts.GeneralDeletionCaesuras
public import SerrePositivity.EInfinity.IntervalCuts.DeletedActivePositions

/-!
# 展開色列の削除とcaesura集合の移送

Berger–Fresse §2.2.7、M14 L09a。
既存の一般の単語削除のcaesuraの公式を、活動頂点の有限集合と逆転数へ運ぶ。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts
open SerrePositivity.EInfinity.IntervalCuts
  (caesura_erase_of_caesura caesura_erase_final positionInversionCount positionInversionCount_image)

/-- 任意の色列のcaesuraの有限集合。隣接非退化性は要求しない。 -/
def caesuraPositions {N r : ℕ} (v : Fin N → Fin r) : Finset (Fin N) :=
  Finset.univ.filter (Surjection.Caesura v)

/-- C121：活動頂点の削除は、同じcaesura集合からその頂点だけを除く。 -/
lemma caesuraPositions_erase_active_image {N r : ℕ} (v : Fin (N + 1) → Fin r)
    (k : Fin (N + 1)) (hk : Surjection.Caesura v k) :
    (caesuraPositions (Surjection.erase v k)).image k.succAbove =
      (caesuraPositions v).erase k := by
  ext j
  simp only [caesuraPositions, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_erase]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨Fin.succAbove_ne k a, (caesura_erase_of_caesura v k hk a).mp ha⟩
  · rintro ⟨hne, hj⟩
    obtain ⟨a, ha⟩ := Fin.exists_succAbove_eq hne
    refine ⟨a, (caesura_erase_of_caesura v k hk a).mpr ?_, ha⟩
    simpa only [ha] using hj

/-- C122：最後の非活動頂点を削除すると、直前同色の活動性を失う。 -/
lemma caesuraPositions_erase_final_image {N r : ℕ} (v : Fin (N + 1) → Fin r)
    (k : Fin (N + 1)) (hk : ¬ Surjection.Caesura v k)
    (hp : (Surjection.previousOccurrences v k).Nonempty) :
    (caesuraPositions (Surjection.erase v k)).image k.succAbove =
      (caesuraPositions v).erase (previousVertex v k hp) := by
  have hgap : ∀ b, previousVertex v k hp < b → b < k → v b ≠ v k := by
    intro b hpb hbk hv
    have hb : b ∈ Surjection.previousOccurrences v k :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbk, hv⟩
    exact (not_le_of_gt hpb) ((Surjection.previousOccurrences v k).le_max' b hb)
  have he := caesura_erase_final v (previousVertex v k hp) k (previousVertex_lt v k hp)
    (previousVertex_value v k hp) hk hgap
  ext j
  simp only [caesuraPositions, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_erase]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨((he a).mp ha).2, ((he a).mp ha).1⟩
  · rintro ⟨hne, hc⟩
    have hnk : j ≠ k := by intro h; exact hk (h ▸ hc)
    obtain ⟨a, ha⟩ := Fin.exists_succAbove_eq hnk
    refine ⟨a, (he a).mpr ?_, ha⟩
    simpa only [ha] using And.intro hc hne

/-- C123：活動頂点の削除後の逆転数を、元の活動集合で読む。 -/
lemma inversionCount_erase_active {N r : ℕ} (v : Fin (N + 1) → Fin r)
    (k : Fin (N + 1)) (hk : Surjection.Caesura v k) :
    positionInversionCount (Surjection.erase v k) (caesuraPositions (Surjection.erase v k)) =
      positionInversionCount v ((caesuraPositions v).erase k) := by
  have h := positionInversionCount_image v k.succAbove (Fin.strictMono_succAbove k)
    (caesuraPositions (Surjection.erase v k))
  rw [caesuraPositions_erase_active_image v k hk] at h
  exact h.symm

/-- C124：最後の非活動頂点の削除後は、直前同色の頂点を除いた逆転集合で読む。 -/
lemma inversionCount_erase_final {N r : ℕ} (v : Fin (N + 1) → Fin r)
    (k : Fin (N + 1)) (hk : ¬ Surjection.Caesura v k)
    (hp : (Surjection.previousOccurrences v k).Nonempty) :
    positionInversionCount (Surjection.erase v k) (caesuraPositions (Surjection.erase v k)) =
      positionInversionCount v ((caesuraPositions v).erase (previousVertex v k hp)) := by
  have h := positionInversionCount_image v k.succAbove (Fin.strictMono_succAbove k)
    (caesuraPositions (Surjection.erase v k))
  rw [caesuraPositions_erase_final_image v k hk hp] at h
  exact h.symm

end SerrePositivity.EInfinity.SimplexCuts
