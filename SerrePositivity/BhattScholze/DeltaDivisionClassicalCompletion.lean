module

public import SerrePositivity.BhattScholze.DeltaAdicLift
public import SerrePositivity.BhattScholze.DeltaDivisionUniversal

/-! # δ除算商の古典的(p,d)完備化

著者公開版Prop 7.2の代数的商に古典的完備化を適用する具体的な工程。
導来完備化との比較、新dねじれの不存在、prismの存在は主張しない。
-/

@[expose] public noncomputable section
universe u v w
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R] {σ : Type v}

/-- 二段階δ除算商内の(p,d)イデアル。 -/
def deltaDivisionAdicIdeal (D : DeltaStructure p R) (d : R) (a : σ → R) :
    Ideal (DeltaDivisionTorsionQuotient D d a) :=
  Ideal.span {(p : DeltaDivisionTorsionQuotient D d a), deltaDivisionTorsionMap D d a d}

/-- 二段階δ除算商の古典的(p,d)完備化。 -/
abbrev ClassicalDeltaDivisionCompletion (D : DeltaStructure p R) (d : R) (a : σ → R) :=
  AdicCompletion (deltaDivisionAdicIdeal D d a) (DeltaDivisionTorsionQuotient D d a)

/-- (p,d)イデアルは有限生成。 -/
theorem deltaDivisionAdicIdeal_fg (D : DeltaStructure p R) (d : R) (a : σ → R) :
    (deltaDivisionAdicIdeal D d a).FG :=
  Submodule.fg_span (Set.toFinite _)

/-- 古典的(p,d)完備化のδ構造。 -/
def classicalDeltaDivisionStructure (D : DeltaStructure p R) (d : R) (a : σ → R) :
    DeltaStructure p (ClassicalDeltaDivisionCompletion D d a) :=
  (deltaDivisionTorsionStructure D d a).adicCompletion (deltaDivisionAdicIdeal D d a)
    (Ideal.subset_span (by simp))

/-- 基底から古典的(p,d)完備化への標準射。 -/
def classicalDeltaDivisionMap (D : DeltaStructure p R) (d : R) (a : σ → R) :
    R →+* ClassicalDeltaDivisionCompletion D d a :=
  (algebraMap (DeltaDivisionTorsionQuotient D d a) _).comp (deltaDivisionTorsionMap D d a)

/-- 二段階δ除算商への標準射はδ射。 -/
theorem deltaDivisionTorsionMap_isDeltaHom (D : DeltaStructure p R) (d : R) (a : σ → R) :
    D.IsDeltaHom (deltaDivisionTorsionStructure D d a) (deltaDivisionTorsionMap D d a) :=
  ((deltaAdjoinDivisionStructure D d a).isDeltaHom_quotient_mk _
    ((deltaAdjoinDivisionStructure D d a).isStable_deltaClosure _)).comp
      (deltaAdjoinDivisionMap_isDeltaHom D d a)

/-- 古典的完備化への標準基底射はδ射。 -/
theorem classicalDeltaDivisionMap_isDeltaHom (D : DeltaStructure p R) (d : R) (a : σ → R) :
    D.IsDeltaHom (classicalDeltaDivisionStructure D d a) (classicalDeltaDivisionMap D d a) :=
  ((deltaDivisionTorsionStructure D d a).isDeltaHom_adicCompletion
    (deltaDivisionAdicIdeal D d a) (Ideal.subset_span (by simp))).comp
      (deltaDivisionTorsionMap_isDeltaHom D d a)

/-- f(d)が正則、全f(a_s)がf(d)で割り切れ、終域がp,f(d)を含むJで完備なら、
古典的完備化したδ除算商から基底射fを延長するδ射が一意に存在する。 -/
theorem existsUnique_classicalDeltaDivisionHom {A : Type w} [CommRing A]
    (D : DeltaStructure p R) (E : DeltaStructure p A) (d : R) (a : σ → R)
    (f : R →+* A) (hf : D.IsDeltaHom E f)
    (hd : Function.Injective (fun x : A ↦ f d * x)) (ha : ∀ s, f d ∣ f (a s))
    (J : Ideal A) [IsAdicComplete J A] (hpJ : (p : A) ∈ J) (hdJ : f d ∈ J) :
    ∃! g : ClassicalDeltaDivisionCompletion D d a →+* A,
      (classicalDeltaDivisionStructure D d a).IsDeltaHom E g ∧
        g.comp (classicalDeltaDivisionMap D d a) = f := by
  let B := DeltaDivisionTorsionQuotient D d a
  let DB := deltaDivisionTorsionStructure D d a
  let j := deltaDivisionTorsionMap D d a
  let I := deltaDivisionAdicIdeal D d a
  let c := algebraMap B (AdicCompletion I B)
  have hc := DB.isDeltaHom_adicCompletion I (Ideal.subset_span (by simp))
  obtain ⟨k, hk, hku⟩ := existsUnique_deltaDivisionTorsionHom D E d a f hf hd ha
  have hIJ : I.map k ≤ J := by
    apply Ideal.map_le_iff_le_comap.mpr
    apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · change k (p : B) ∈ J
      simpa only [map_natCast] using hpJ
    · have h := DFunLike.congr_fun hk.2 d
      change k (j d) = f d at h
      change k (j d) ∈ J
      simpa only [h] using hdJ
  obtain ⟨g, hg, hgu⟩ := DB.existsUnique_adicCompletion_lift E I
    (Ideal.subset_span (by simp))
    (deltaDivisionAdicIdeal_fg D d a) J k hk.1 hIJ
  refine ⟨g, ⟨hg.2, ?_⟩, ?_⟩
  · change g.comp (c.comp j) = f
    rw [← RingHom.comp_assoc, hg.1, hk.2]
  · intro l hl
    have hlk : l.comp c = k := by
      apply hku (l.comp c)
      refine ⟨hl.1.comp hc, ?_⟩
      change (l.comp c).comp j = f
      rw [RingHom.comp_assoc]
      exact hl.2
    apply hgu l
    exact ⟨hlk, hl.1⟩

end SerrePositivity.BhattScholze
