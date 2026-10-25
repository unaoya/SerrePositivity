module

public import SerrePositivity.BhattScholze.Prism.PerfectDeltaPCompletion

/-! # p進完備なδ完全化と普遍性

任意のδ環のFrobenius余極限を古典的p進完備化する。
完全かつ古典的p進完備なδ環への一意な延長を具体的に証明する。
prismやperfectoid環の定義を変更せず、導来完備化との比較は別工程に残す。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- δ完全化の古典的p進完備化。 -/
abbrev PCompletedDeltaPerfection (D : DeltaStructure p A) :=
  AdicCompletion (Ideal.span {(p : DeltaPerfection D)}) (DeltaPerfection D)

/-- p進完備なδ完全化のδ構造。 -/
def pCompletedDeltaPerfectionStructure (D : DeltaStructure p A) :
    DeltaStructure p (PCompletedDeltaPerfection D) :=
  (deltaPerfectionStructure D).adicCompletion (Ideal.span {(p : DeltaPerfection D)})
    (Ideal.subset_span (by simp))

/-- 元のδ環からp進完備なδ完全化への標準射。 -/
def pCompletedDeltaPerfectionMap (D : DeltaStructure p A) : A →+* PCompletedDeltaPerfection D :=
  (algebraMap (DeltaPerfection D) _).comp (deltaPerfectionOf D 0)

/-- p進完備なδ完全化への標準射はδ射。 -/
theorem pCompletedDeltaPerfectionMap_isDeltaHom (D : DeltaStructure p A) :
    D.IsDeltaHom (pCompletedDeltaPerfectionStructure D) (pCompletedDeltaPerfectionMap D) :=
  ((deltaPerfectionStructure D).isDeltaHom_adicCompletion _
    (Ideal.subset_span (by simp))).comp (deltaPerfectionOf_isDeltaHom D 0)

/-- p進完備化後もδ完全化は完全。 -/
theorem pCompletedDeltaPerfection_isPerfect (D : DeltaStructure p A) :
    (pCompletedDeltaPerfectionStructure D).IsPerfect :=
  (deltaPerfection_isPerfect D).adicCompletion_span_p

/-- p進完備なδ完全化は、環自身のp生成イデアルに関して古典的完備。 -/
theorem pCompletedDeltaPerfection_isAdicComplete (D : DeltaStructure p A) :
    IsAdicComplete (Ideal.span {(p : PCompletedDeltaPerfection D)})
      (PCompletedDeltaPerfection D) := by
  let I : Ideal (DeltaPerfection D) := Ideal.span {(p : DeltaPerfection D)}
  have hI : I.FG := Submodule.fg_span (Set.toFinite _)
  have h := AdicCompletion.isAdicComplete (M := DeltaPerfection D) hI
  have hmap : I.map (algebraMap (DeltaPerfection D) (PCompletedDeltaPerfection D)) =
      Ideal.span {(p : PCompletedDeltaPerfection D)} := by simp [I, Ideal.map_span]
  rw [← hmap]
  exact (IsAdicComplete.map_algebraMap_iff (I := I)
    (S := PCompletedDeltaPerfection D) (M := PCompletedDeltaPerfection D)).mpr h

/-- 完全かつ古典的p進完備なδ環への基底δ射は、p進完備なδ完全化から
一意なδ射へ延長する。源のp正則性・分離性・完備性は不要。 -/
theorem existsUnique_pCompletedDeltaPerfectionHom {B : Type v} [CommRing B]
    (D : DeltaStructure p A) (E : DeltaStructure p B) (hE : E.IsPerfect)
    [IsAdicComplete (Ideal.span {(p : B)}) B] (f : A →+* B) (hf : D.IsDeltaHom E f) :
    ∃! g : PCompletedDeltaPerfection D →+* B,
      (pCompletedDeltaPerfectionStructure D).IsDeltaHom E g ∧
        g.comp (pCompletedDeltaPerfectionMap D) = f := by
  let I : Ideal (DeltaPerfection D) := Ideal.span {(p : DeltaPerfection D)}
  let C := AdicCompletion I (DeltaPerfection D)
  let j := algebraMap (DeltaPerfection D) C
  have hI : I.FG := Submodule.fg_span (Set.toFinite _)
  have hp : (p : DeltaPerfection D) ∈ I := Ideal.subset_span (by simp)
  have hj := (deltaPerfectionStructure D).isDeltaHom_adicCompletion I hp
  obtain ⟨k, hk, hku⟩ := existsUnique_deltaPerfectionHom D E hE f hf
  have hIJ : I.map k ≤ Ideal.span {(p : B)} := by simp [I, Ideal.map_span]
  obtain ⟨g, hg, hgu⟩ := (deltaPerfectionStructure D).existsUnique_adicCompletion_lift
    E I hp hI (Ideal.span {(p : B)}) k hk.1 hIJ
  refine ⟨g, ⟨hg.2, ?_⟩, ?_⟩
  · change g.comp (j.comp (deltaPerfectionOf D 0)) = f
    rw [← RingHom.comp_assoc, hg.1, hk.2]
  · intro l hl
    have hlk : l.comp j = k := by
      apply hku (l.comp j)
      refine ⟨hl.1.comp hj, ?_⟩
      rw [RingHom.comp_assoc]
      exact hl.2
    apply hgu l
    exact ⟨hlk, hl.1⟩

end SerrePositivity.BhattScholze
