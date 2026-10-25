module

public import SerrePositivity.BhattScholze.Delta.Division.DeltaDivisionUniversal
public import SerrePositivity.BhattScholze.Prism.PCompletedDeltaRecovery

/-! # δ除算添加環のp進完備δ完全化

著者公開版Prop 7.2とLemma 3.9に使う具体的な代数的候補。
除算添加の後に既存のp進完備δ完全化を施し、完全p進完備δ環への普遍性を証明する。
mod d商のperfectoid性・prism性・導来(p,d)完備化との比較は結論しない。
-/

@[expose] public noncomputable section
universe u v w
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R] {σ : Type v}

/-- δ除算添加環に既存のp進完備δ完全化を適用した具体的な環。 -/
abbrev PCompletedDeltaDivision (D : DeltaStructure p R) (d : R) (a : σ → R) :=
  PCompletedDeltaPerfection (deltaAdjoinDivisionStructure D d a)

/-- 候補環のδ構造。既存の完全化δ構造を使用する。 -/
abbrev pCompletedDeltaDivisionStructure (D : DeltaStructure p R) (d : R) (a : σ → R) :
    DeltaStructure p (PCompletedDeltaDivision D d a) :=
  pCompletedDeltaPerfectionStructure (deltaAdjoinDivisionStructure D d a)

/-- 基底からp進完備δ除算完全化への具体的な標準射。 -/
def pCompletedDeltaDivisionMap (D : DeltaStructure p R) (d : R) (a : σ → R) :
    R →+* PCompletedDeltaDivision D d a :=
  (pCompletedDeltaPerfectionMap (deltaAdjoinDivisionStructure D d a)).comp
    (deltaAdjoinDivisionMap D d a)

/-- 標準基底射はδ射。 -/
theorem pCompletedDeltaDivisionMap_isDeltaHom (D : DeltaStructure p R) (d : R) (a : σ → R) :
    D.IsDeltaHom (pCompletedDeltaDivisionStructure D d a) (pCompletedDeltaDivisionMap D d a) :=
  (pCompletedDeltaPerfectionMap_isDeltaHom (deltaAdjoinDivisionStructure D d a)).comp
    (deltaAdjoinDivisionMap_isDeltaHom D d a)

/-- 候補のδ環は完全。 -/
theorem pCompletedDeltaDivision_isPerfect (D : DeltaStructure p R) (d : R) (a : σ → R) :
    (pCompletedDeltaDivisionStructure D d a).IsPerfect :=
  pCompletedDeltaPerfection_isPerfect (deltaAdjoinDivisionStructure D d a)

/-- 候補環は古典的p進完備。 -/
theorem pCompletedDeltaDivision_isAdicComplete (D : DeltaStructure p R) (d : R) (a : σ → R) :
    IsAdicComplete (Ideal.span {(p : PCompletedDeltaDivision D d a)})
      (PCompletedDeltaDivision D d a) :=
  pCompletedDeltaPerfection_isAdicComplete (deltaAdjoinDivisionStructure D d a)

/-- 候補環ではpが非零因子。 -/
theorem pCompletedDeltaDivision_p_mul_injective (D : DeltaStructure p R) (d : R) (a : σ → R) :
    Function.Injective (fun x : PCompletedDeltaDivision D d a ↦
      (p : PCompletedDeltaDivision D d a) * x) :=
  (pCompletedDeltaDivision_isPerfect D d a).p_mul_injective

/-- 候補環は実導来p完備。既存の具体的p進完備δ完全化の定理を使用する。 -/
theorem pCompletedDeltaDivision_isModuleComplete (D : DeltaStructure p R) (d : R) (a : σ → R) :
    DerivedCompletion.IsModuleComplete (PCompletedDeltaDivision D d a)
      (p : PCompletedDeltaDivision D d a)
      (ModuleCat.of (PCompletedDeltaDivision D d a) (PCompletedDeltaDivision D d a)) :=
  pCompletedDeltaPerfection_isModuleComplete (deltaAdjoinDivisionStructure D d a)

/-- 基底のdistinguished元dの像は候補環で非零因子。
一般の非完全δ除算商で新しいdねじれが無いとは主張しない。 -/
theorem pCompletedDeltaDivisionMap_mul_injective (D : DeltaStructure p R) (d : R) (a : σ → R)
    (hd : D.IsDistinguished d) :
    Function.Injective (fun x : PCompletedDeltaDivision D d a ↦
      pCompletedDeltaDivisionMap D d a d * x) := by
  let := pCompletedDeltaDivision_isAdicComplete D d a
  exact (pCompletedDeltaDivision_isPerfect D d a).distinguished_mul_injective
    ((pCompletedDeltaDivisionMap_isDeltaHom D d a).map_isDistinguished hd)

/-- 指定したすべてのa_sの像は、候補環でdの像で割り切れる。 -/
theorem pCompletedDeltaDivisionMap_dvd (D : DeltaStructure p R) (d : R) (a : σ → R) (s : σ) :
    pCompletedDeltaDivisionMap D d a d ∣ pCompletedDeltaDivisionMap D d a (a s) := by
  let j := pCompletedDeltaPerfectionMap (deltaAdjoinDivisionStructure D d a)
  refine ⟨j (deltaAdjoinDivisionVariable D d a s), ?_⟩
  have h := congrArg j (deltaAdjoinDivision_relation D d a s)
  rw [map_mul] at h
  exact h.symm

/-- 完全p進完備δ環への基底δ射で、各a_sがdで割り切れれば、候補環からの延長δ射は一意。
dの像の正則性は、distinguished性と終域の完全性・p完備性から内部で供給する。 -/
theorem existsUnique_pCompletedDeltaDivisionHom {A : Type w} [CommRing A]
    (D : DeltaStructure p R) (E : DeltaStructure p A) (hE : E.IsPerfect)
    [IsAdicComplete (Ideal.span {(p : A)}) A] (d : R) (hd : D.IsDistinguished d) (a : σ → R)
    (f : R →+* A) (hf : D.IsDeltaHom E f) (ha : ∀ s, f d ∣ f (a s)) :
    ∃! g : PCompletedDeltaDivision D d a →+* A,
      (pCompletedDeltaDivisionStructure D d a).IsDeltaHom E g ∧
        g.comp (pCompletedDeltaDivisionMap D d a) = f := by
  let DB := deltaAdjoinDivisionStructure D d a
  let j := deltaAdjoinDivisionMap D d a
  let c := pCompletedDeltaPerfectionMap DB
  have hfd := hE.distinguished_mul_injective (hf.map_isDistinguished hd)
  obtain ⟨k, hk, hku⟩ := existsUnique_deltaAdjoinDivisionHom_of_regular D E d a f hf hfd ha
  obtain ⟨g, hg, hgu⟩ := existsUnique_pCompletedDeltaPerfectionHom DB E hE k hk.1
  refine ⟨g, ⟨hg.1, ?_⟩, ?_⟩
  · change g.comp (c.comp j) = f
    rw [← RingHom.comp_assoc, hg.2, hk.2]
  · intro l hl
    have hlk : l.comp c = k := by
      apply hku (l.comp c)
      refine ⟨hl.1.comp (pCompletedDeltaPerfectionMap_isDeltaHom DB), ?_⟩
      rw [RingHom.comp_assoc]
      exact hl.2
    apply hgu l
    exact ⟨hl.1, hlk⟩

/-- 候補のd商のp冪ねじれはpで消える。具体的な有界ねじれ条件N=1。 -/
theorem pCompletedDeltaDivision_quotient_p_pow_torsion_killed_by_p
    (D : DeltaStructure p R) (d : R) (hd : D.IsDistinguished d) (a : σ → R) (n : ℕ)
    (x : PCompletedDeltaDivision D d a ⧸ Ideal.span {pCompletedDeltaDivisionMap D d a d})
    (hx : (p : PCompletedDeltaDivision D d a ⧸
      Ideal.span {pCompletedDeltaDivisionMap D d a d}) ^ n * x = 0) :
    (p : PCompletedDeltaDivision D d a ⧸
      Ideal.span {pCompletedDeltaDivisionMap D d a d}) * x = 0 :=
  (pCompletedDeltaDivision_isPerfect D d a).distinguished_quotient_p_pow_torsion_killed_by_p
    ((pCompletedDeltaDivisionMap_isDeltaHom D d a).map_isDistinguished hd) n x hx

end SerrePositivity.BhattScholze
