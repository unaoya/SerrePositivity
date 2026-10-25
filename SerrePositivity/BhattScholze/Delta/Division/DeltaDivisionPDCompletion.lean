module

public import SerrePositivity.BhattScholze.Delta.Extension.DeltaPDCompletion
public import SerrePositivity.BhattScholze.Delta.Division.DeltaDivisionClassicalCompletion

/-! # δ除算・旧ねじれ商・実導来(p,d)完備化の一段操作

著者公開版Prop 7.2の一段を、F3の実Koszul H⁰と証明済みδ延長に接続する。
完備化後の新dねじれの不存在やprismの存在は結論しない。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open SerrePositivity.DerivedCompletion
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R] {σ : Type u}

/-- 旧ねじれδ閉包商に実導来(p,d)完備化H⁰を施した具体的な候補。 -/
abbrev DerivedDeltaDivisionCompletion (D : DeltaStructure p R) (d : R) (a : σ → R) :=
  PDCompletionH0 (DeltaDivisionTorsionQuotient D d a) p (deltaDivisionTorsionMap D d a d)

/-- 候補の環構造はF3の実H⁰の環構造。 -/
@[instance_reducible] def derivedDeltaDivisionCommRing
    (D : DeltaStructure p R) (d : R) (a : σ → R) :
    CommRing (DerivedDeltaDivisionCompletion D d a) :=
  pdCompletionCommRing (DeltaDivisionTorsionQuotient D d a) p (deltaDivisionTorsionMap D d a d)

/-- 候補のδ構造は実導来完備化への一意延長。 -/
def derivedDeltaDivisionStructure (D : DeltaStructure p R) (d : R) (a : σ → R) :
    letI := derivedDeltaDivisionCommRing D d a
    DeltaStructure p (DerivedDeltaDivisionCompletion D d a) :=
  deltaPDCompletionStructure (deltaDivisionTorsionStructure D d a) (deltaDivisionTorsionMap D d a d)

/-- 元の環から一段候補への具体的な標準射。 -/
def derivedDeltaDivisionMap (D : DeltaStructure p R) (d : R) (a : σ → R) :
    letI := derivedDeltaDivisionCommRing D d a
    R →+* DerivedDeltaDivisionCompletion D d a :=
  (pdCompletionUnit (DeltaDivisionTorsionQuotient D d a) p (deltaDivisionTorsionMap D d a d)).comp
    (deltaDivisionTorsionMap D d a)

/-- 標準射はδ射。 -/
theorem derivedDeltaDivisionMap_isDeltaHom (D : DeltaStructure p R) (d : R) (a : σ → R) :
    letI := derivedDeltaDivisionCommRing D d a
    D.IsDeltaHom (derivedDeltaDivisionStructure D d a) (derivedDeltaDivisionMap D d a) := by
  let := derivedDeltaDivisionCommRing D d a
  exact (pdCompletionUnit_isDeltaHom (deltaDivisionTorsionStructure D d a)
    (deltaDivisionTorsionMap D d a d)).comp (deltaDivisionTorsionMap_isDeltaHom D d a)

/-- 一段候補は自身の作用について実p導来完備。 -/
theorem derivedDeltaDivision_complete_p (D : DeltaStructure p R) (d : R) (a : σ → R) :
    letI := derivedDeltaDivisionCommRing D d a
    IsModuleComplete (DerivedDeltaDivisionCompletion D d a)
      (p : DerivedDeltaDivisionCompletion D d a)
      (ModuleCat.of (DerivedDeltaDivisionCompletion D d a)
        (DerivedDeltaDivisionCompletion D d a)) :=
  pdCompletionH0_self_complete_p (DeltaDivisionTorsionQuotient D d a) p
    (deltaDivisionTorsionMap D d a d)

/-- 一段候補は自身の作用についてdの標準像に実導来完備。 -/
theorem derivedDeltaDivision_complete_d (D : DeltaStructure p R) (d : R) (a : σ → R) :
    letI := derivedDeltaDivisionCommRing D d a
    IsModuleComplete (DerivedDeltaDivisionCompletion D d a) (derivedDeltaDivisionMap D d a d)
      (ModuleCat.of (DerivedDeltaDivisionCompletion D d a)
        (DerivedDeltaDivisionCompletion D d a)) :=
  pdCompletionH0_self_complete_d (DeltaDivisionTorsionQuotient D d a) p
    (deltaDivisionTorsionMap D d a d)

/-- dがdistinguishedなら、一段候補での像もdistinguished。正則性とは区別する。 -/
theorem derivedDeltaDivisionMap_isDistinguished (D : DeltaStructure p R) (d : R) (a : σ → R)
    (hd : D.IsDistinguished d) :
    letI := derivedDeltaDivisionCommRing D d a
    (derivedDeltaDivisionStructure D d a).IsDistinguished (derivedDeltaDivisionMap D d a d) := by
  let := derivedDeltaDivisionCommRing D d a
  exact (derivedDeltaDivisionMap_isDeltaHom D d a).map_isDistinguished hd

/-- 各添加元の標準像は、一段候補のd像で割り切れる。 -/
theorem derivedDeltaDivisionMap_dvd (D : DeltaStructure p R) (d : R) (a : σ → R) (s : σ) :
    letI := derivedDeltaDivisionCommRing D d a
    derivedDeltaDivisionMap D d a d ∣ derivedDeltaDivisionMap D d a (a s) := by
  let := derivedDeltaDivisionCommRing D d a
  let U := DeltaDivisionTorsionQuotient D d a
  let c := pdCompletionUnit U p (deltaDivisionTorsionMap D d a d)
  let h : DeltaAdjoinDivision D d a →+* DerivedDeltaDivisionCompletion D d a :=
    c.comp (Ideal.Quotient.mk _)
  have he := congrArg h (deltaAdjoinDivision_relation D d a s)
  rw [map_mul] at he
  exact ⟨h (deltaAdjoinDivisionVariable D d a s), he.symm⟩

/-- 元族が生成する任意のイデアルは、一段候補のd像の主イデアルへ入る。 -/
theorem derivedDeltaDivisionMap_spanned_ideal_le (D : DeltaStructure p R) (d : R) (a : σ → R) :
    letI := derivedDeltaDivisionCommRing D d a
    Ideal.span (Set.range a) ≤ (Ideal.span {derivedDeltaDivisionMap D d a d}).comap
      (derivedDeltaDivisionMap D d a) := by
  let := derivedDeltaDivisionCommRing D d a
  apply Ideal.span_le.mpr
  rintro _ ⟨s, rfl⟩
  exact Ideal.mem_span_singleton.mpr (derivedDeltaDivisionMap_dvd D d a s)

/-- 正則なd像と可除性を持つδ基底射は、実一段候補から一意に延長する。
試験環のp,f(d)実導来完備性を明示し、一般のpねじれを許す。 -/
theorem existsUnique_derivedDeltaDivisionHom {T : Type u} [CommRing T]
    (D : DeltaStructure p R) (E : DeltaStructure p T) (d : R) (a : σ → R)
    (f : R →+* T) (hf : D.IsDeltaHom E f)
    (hreg : Function.Injective (fun x : T ↦ f d * x)) (ha : ∀ s, f d ∣ f (a s))
    (hp : IsModuleComplete T (p : T) (ModuleCat.of T T))
    (hd : IsModuleComplete T (f d) (ModuleCat.of T T)) :
    letI := derivedDeltaDivisionCommRing D d a
    ∃! h : DerivedDeltaDivisionCompletion D d a →+* T,
      (derivedDeltaDivisionStructure D d a).IsDeltaHom E h ∧
        h.comp (derivedDeltaDivisionMap D d a) = f := by
  let := derivedDeltaDivisionCommRing D d a
  let U := DeltaDivisionTorsionQuotient D d a
  let DU := deltaDivisionTorsionStructure D d a
  let j := deltaDivisionTorsionMap D d a
  let c := pdCompletionUnit U p (j d)
  obtain ⟨k, hk, hku⟩ := existsUnique_deltaDivisionTorsionHom D E d a f hf hreg ha
  have hkd : k (j d) = f d := RingHom.congr_fun hk.2 d
  have hd' : IsModuleComplete T (k (j d)) (ModuleCat.of T T) := by rw [hkd]; exact hd
  obtain ⟨h, hh, hu⟩ := existsUnique_deltaPDCompletionHom DU (j d) E k hk.1 hp hd'
  refine ⟨h, ⟨hh.1, ?_⟩, ?_⟩
  · change h.comp (c.comp j) = f
    rw [← RingHom.comp_assoc, hh.2, hk.2]
  · intro l hl
    apply hu l
    refine ⟨hl.1, ?_⟩
    apply hku (l.comp c)
    refine ⟨hl.1.comp (pdCompletionUnit_isDeltaHom DU (j d)), ?_⟩
    change (l.comp c).comp j = f
    rw [RingHom.comp_assoc]
    exact hl.2

end SerrePositivity.BhattScholze
