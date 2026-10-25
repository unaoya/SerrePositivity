module

public import SerrePositivity.BhattScholze.Prism.Perfection.PCompletedDeltaDivision

/-! # 除算する元族の包含とp進完備δ除算候補の標準比較

著者公開版Prop 7.2のJ/d添加に向け、任意の生成元族の生成イデアルに関する
包含から具体的なδ比較射を作り、恒等射・合成との両立を証明する。
候補のperfectoid性や標準射の全射性は結論しない。
-/

@[expose] public noncomputable section
universe u v w t
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R]
variable {σ : Type v} {τ : Type w} {υ : Type t}

/-- 添加元族の生成イデアルの像は、候補環でdの像の主イデアルに入る。 -/
theorem pCompletedDeltaDivisionMap_spanned_ideal_le_span
    (D : DeltaStructure p R) (d : R) (a : σ → R) :
    Ideal.span (Set.range a) ≤ (Ideal.span {pCompletedDeltaDivisionMap D d a d}).comap
      (pCompletedDeltaDivisionMap D d a) := by
  apply Ideal.span_le.mpr
  rintro _ ⟨s, rfl⟩
  apply Ideal.mem_span_singleton.mpr
  exact pCompletedDeltaDivisionMap_dvd D d a s

/-- 候補環から完全p進完備δ終域へのδ射は、元の基底上の値で決まる。 -/
theorem pCompletedDeltaDivisionHom_ext {A : Type*} [CommRing A]
    (D : DeltaStructure p R) (E : DeltaStructure p A) (hE : E.IsPerfect)
    [IsAdicComplete (Ideal.span {(p : A)}) A] (d : R) (hd : D.IsDistinguished d) (a : σ → R)
    (f g : PCompletedDeltaDivision D d a →+* A)
    (hf : (pCompletedDeltaDivisionStructure D d a).IsDeltaHom E f)
    (hg : (pCompletedDeltaDivisionStructure D d a).IsDeltaHom E g)
    (hfg : f.comp (pCompletedDeltaDivisionMap D d a) =
      g.comp (pCompletedDeltaDivisionMap D d a)) : f = g := by
  let j := pCompletedDeltaDivisionMap D d a
  have hgj := hg.comp (pCompletedDeltaDivisionMap_isDeltaHom D d a)
  have ha (s : σ) : (g.comp j) d ∣ (g.comp j) (a s) := by
    obtain ⟨b, hb⟩ := pCompletedDeltaDivisionMap_dvd D d a s
    refine ⟨g b, ?_⟩
    change g (j (a s)) = g (j d) * g b
    rw [hb, map_mul]
  obtain ⟨k, _, hku⟩ := existsUnique_pCompletedDeltaDivisionHom D E hE d hd a (g.comp j) hgj ha
  exact (hku f ⟨hf, hfg⟩).trans (hku g ⟨hg, rfl⟩).symm

/-- 生成イデアルの包含から、候補間の基底と両立するδ射が一意に存在する。 -/
theorem existsUnique_pCompletedDeltaDivisionComparisonHom
    (D : DeltaStructure p R) (d : R) (hd : D.IsDistinguished d) (a : σ → R) (b : τ → R)
    (hab : Ideal.span (Set.range a) ≤ Ideal.span (Set.range b)) :
    ∃! g : PCompletedDeltaDivision D d a →+* PCompletedDeltaDivision D d b,
      (pCompletedDeltaDivisionStructure D d a).IsDeltaHom
        (pCompletedDeltaDivisionStructure D d b) g ∧
        g.comp (pCompletedDeltaDivisionMap D d a) = pCompletedDeltaDivisionMap D d b := by
  let := pCompletedDeltaDivision_isAdicComplete D d b
  apply existsUnique_pCompletedDeltaDivisionHom D (pCompletedDeltaDivisionStructure D d b)
    (pCompletedDeltaDivision_isPerfect D d b) d hd a (pCompletedDeltaDivisionMap D d b)
    (pCompletedDeltaDivisionMap_isDeltaHom D d b)
  intro s
  apply Ideal.mem_span_singleton.mp
  exact pCompletedDeltaDivisionMap_spanned_ideal_le_span D d b
    (hab (Ideal.subset_span (Set.mem_range_self s)))

/-- 生成イデアルの包含に対応する具体的な標準比較射。 -/
def pCompletedDeltaDivisionComparisonMap
    (D : DeltaStructure p R) (d : R) (hd : D.IsDistinguished d) (a : σ → R) (b : τ → R)
    (hab : Ideal.span (Set.range a) ≤ Ideal.span (Set.range b)) :
    PCompletedDeltaDivision D d a →+* PCompletedDeltaDivision D d b :=
  (existsUnique_pCompletedDeltaDivisionComparisonHom D d hd a b hab).choose

/-- 標準比較射はδ射。 -/
theorem pCompletedDeltaDivisionComparisonMap_isDeltaHom
    (D : DeltaStructure p R) (d : R) (hd : D.IsDistinguished d) (a : σ → R) (b : τ → R)
    (hab : Ideal.span (Set.range a) ≤ Ideal.span (Set.range b)) :
    (pCompletedDeltaDivisionStructure D d a).IsDeltaHom (pCompletedDeltaDivisionStructure D d b)
      (pCompletedDeltaDivisionComparisonMap D d hd a b hab) :=
  (existsUnique_pCompletedDeltaDivisionComparisonHom D d hd a b hab).choose_spec.1.1

/-- 標準比較射は元の基底射と可換。 -/
@[simp] theorem pCompletedDeltaDivisionComparisonMap_comp_base
    (D : DeltaStructure p R) (d : R) (hd : D.IsDistinguished d) (a : σ → R) (b : τ → R)
    (hab : Ideal.span (Set.range a) ≤ Ideal.span (Set.range b)) :
    (pCompletedDeltaDivisionComparisonMap D d hd a b hab).comp (pCompletedDeltaDivisionMap D d a) =
      pCompletedDeltaDivisionMap D d b :=
  (existsUnique_pCompletedDeltaDivisionComparisonHom D d hd a b hab).choose_spec.1.2

/-- 同じ元族への標準比較射は恒等射。 -/
@[simp] theorem pCompletedDeltaDivisionComparisonMap_id
    (D : DeltaStructure p R) (d : R) (hd : D.IsDistinguished d) (a : σ → R) :
    pCompletedDeltaDivisionComparisonMap D d hd a a le_rfl =
      RingHom.id (PCompletedDeltaDivision D d a) := by
  let := pCompletedDeltaDivision_isAdicComplete D d a
  apply pCompletedDeltaDivisionHom_ext D _ (pCompletedDeltaDivision_isPerfect D d a) d hd a
    _ _ (pCompletedDeltaDivisionComparisonMap_isDeltaHom D d hd a a le_rfl)
    (pCompletedDeltaDivisionStructure D d a).isDeltaHom_id
  rw [pCompletedDeltaDivisionComparisonMap_comp_base, RingHom.id_comp]

/-- 生成イデアルの包含の合成に対応する射は標準比較射の合成。 -/
theorem pCompletedDeltaDivisionComparisonMap_comp
    (D : DeltaStructure p R) (d : R) (hd : D.IsDistinguished d)
    (a : σ → R) (b : τ → R) (c : υ → R)
    (hab : Ideal.span (Set.range a) ≤ Ideal.span (Set.range b))
    (hbc : Ideal.span (Set.range b) ≤ Ideal.span (Set.range c)) :
    pCompletedDeltaDivisionComparisonMap D d hd a c (hab.trans hbc) =
      (pCompletedDeltaDivisionComparisonMap D d hd b c hbc).comp
        (pCompletedDeltaDivisionComparisonMap D d hd a b hab) := by
  let := pCompletedDeltaDivision_isAdicComplete D d c
  apply pCompletedDeltaDivisionHom_ext D _ (pCompletedDeltaDivision_isPerfect D d c) d hd a
    _ _ (pCompletedDeltaDivisionComparisonMap_isDeltaHom D d hd a c _)
    ((pCompletedDeltaDivisionComparisonMap_isDeltaHom D d hd b c hbc).comp
      (pCompletedDeltaDivisionComparisonMap_isDeltaHom D d hd a b hab))
  rw [pCompletedDeltaDivisionComparisonMap_comp_base, RingHom.comp_assoc,
    pCompletedDeltaDivisionComparisonMap_comp_base, pCompletedDeltaDivisionComparisonMap_comp_base]

end SerrePositivity.BhattScholze
