module

public import SerrePositivity.BhattScholze.Delta.Division.DeltaAdjoinDivision
public import SerrePositivity.BhattScholze.Delta.Division.DeltaTorsionReduction

/-! # 正則なdの像へのδ除算の普遍性

著者公開版Prop 7.2の代数的な二段階。指定解族を公開定理の結論から除き、
基底射・可除性・dの像の正則性から一意なδ射を得る。
導来完備化後のねじれ除去やprismの存在は結論しない。
-/

@[expose] public noncomputable section
universe u v w
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R] {σ : Type v}

/-- 添加環からの基底射と両立する射は、必ず除算の関係式を満たす。 -/
theorem deltaAdjoinDivisionHom_relation {A : Type w} [CommRing A]
    (D : DeltaStructure p R) (d : R) (a : σ → R) (f : R →+* A)
    (g : DeltaAdjoinDivision D d a →+* A)
    (hg : g.comp (deltaAdjoinDivisionMap D d a) = f) (s : σ) :
    f d * g (deltaAdjoinDivisionVariable D d a s) = f (a s) := by
  have h := congrArg g (deltaAdjoinDivision_relation D d a s)
  rw [map_mul] at h
  have hc (r : R) : g (deltaAdjoinDivisionMap D d a r) = f r :=
    DFunLike.congr_fun hg r
  simpa only [hc] using h

/-- dの像が非零因子で、各a_sの像がdで割り切れるなら、
添加環から基底射fを延長するδ射が一意に存在する。解族の指定は不要。 -/
theorem existsUnique_deltaAdjoinDivisionHom_of_regular {A : Type w} [CommRing A]
    (D : DeltaStructure p R) (E : DeltaStructure p A) (d : R) (a : σ → R)
    (f : R →+* A) (hf : D.IsDeltaHom E f)
    (hd : Function.Injective (fun x : A ↦ f d * x))
    (ha : ∀ s, f d ∣ f (a s)) :
    ∃! g : DeltaAdjoinDivision D d a →+* A,
      (deltaAdjoinDivisionStructure D d a).IsDeltaHom E g ∧
        g.comp (deltaAdjoinDivisionMap D d a) = f := by
  choose b hb using ha
  obtain ⟨g, hg, hu⟩ := existsUnique_deltaAdjoinDivisionHom D E d a f hf b
    (fun s ↦ (hb s).symm)
  refine ⟨g, ⟨hg.1, hg.2.1⟩, ?_⟩
  intro k hk
  apply hu k
  refine ⟨hk.1, hk.2, ?_⟩
  intro s
  apply hd
  exact (deltaAdjoinDivisionHom_relation D d a f k hk.2 s).trans (hb s)

/-- 添加環の旧d冪ねじれのδ閉包商。局所化核と既存δ閉包を使用する。 -/
abbrev DeltaDivisionTorsionQuotient (D : DeltaStructure p R) (d : R) (a : σ → R) :=
  DeltaAdjoinDivision D d a ⧸
    (deltaAdjoinDivisionStructure D d a).deltaClosure
      (RingHom.ker (algebraMap (DeltaAdjoinDivision D d a)
        (Localization.Away (deltaAdjoinDivisionMap D d a d))))

/-- 除算と旧ねじれ除去の二段階商への標準射。 -/
def deltaDivisionTorsionMap (D : DeltaStructure p R) (d : R) (a : σ → R) :
    R →+* DeltaDivisionTorsionQuotient D d a :=
  (Ideal.Quotient.mk _).comp (deltaAdjoinDivisionMap D d a)

/-- 二段階商のδ構造。 -/
def deltaDivisionTorsionStructure (D : DeltaStructure p R) (d : R) (a : σ → R) :
    DeltaStructure p (DeltaDivisionTorsionQuotient D d a) :=
  (deltaAdjoinDivisionStructure D d a).quotient _
    ((deltaAdjoinDivisionStructure D d a).isStable_deltaClosure _)

/-- 正則なdの像と可除性を持つδ基底射は、除算・旧ねじれ除去の二段階商から
一意なδ射へ延長される。Prop 7.2の完備化前の具体的な普遍性。 -/
theorem existsUnique_deltaDivisionTorsionHom {A : Type w} [CommRing A]
    (D : DeltaStructure p R) (E : DeltaStructure p A) (d : R) (a : σ → R)
    (f : R →+* A) (hf : D.IsDeltaHom E f)
    (hd : Function.Injective (fun x : A ↦ f d * x))
    (ha : ∀ s, f d ∣ f (a s)) :
    ∃! g : DeltaDivisionTorsionQuotient D d a →+* A,
      (deltaDivisionTorsionStructure D d a).IsDeltaHom E g ∧
        g.comp (deltaDivisionTorsionMap D d a) = f := by
  let B := DeltaAdjoinDivision D d a
  let DB := deltaAdjoinDivisionStructure D d a
  let j := deltaAdjoinDivisionMap D d a
  let I := DB.deltaClosure (RingHom.ker (algebraMap B (Localization.Away (j d))))
  let q : B →+* B ⧸ I := Ideal.Quotient.mk I
  have hq := DB.isDeltaHom_quotient_mk I (DB.isStable_deltaClosure _)
  obtain ⟨k, hk, hku⟩ := existsUnique_deltaAdjoinDivisionHom_of_regular D E d a f hf hd ha
  have hkd : Function.Injective (fun x : A ↦ k (j d) * x) := by
    have h := DFunLike.congr_fun hk.2 d
    change k (j d) = f d at h
    simpa only [h] using hd
  obtain ⟨g, hg, hgu⟩ := DB.existsUnique_torsionReductionHom (j d) E k hk.1 hkd
  refine ⟨g, ⟨hg.2, ?_⟩, ?_⟩
  · change g.comp (q.comp j) = f
    rw [← RingHom.comp_assoc, hg.1, hk.2]
  · intro l hl
    have hlk : l.comp q = k := by
      apply hku (l.comp q)
      refine ⟨hl.1.comp hq, ?_⟩
      change (l.comp q).comp j = f
      rw [RingHom.comp_assoc]
      exact hl.2
    apply hgu l
    exact ⟨hlk, hl.1⟩

end SerrePositivity.BhattScholze
