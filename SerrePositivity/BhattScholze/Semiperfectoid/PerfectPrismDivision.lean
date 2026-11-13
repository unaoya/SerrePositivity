module

public import SerrePositivity.BhattScholze.Delta.Division.Basic
public import SerrePositivity.BhattScholze.Prism.Perfection.PCompletedPerfection
public import SerrePositivity.BhattScholze.Prism.Basic.OrientedPrism
public import SerrePositivity.BhattScholze.Delta.Perfect.PerfectDelta
public import SerrePositivity.BhattScholze.Delta.Perfect.DistinguishedRegular

/-!
# 完全 prism の中で J/d を割る構成（BS 著者版 Proposition 7.2・BS 著者版 Corollary 7.3 の代数的部分）

## 概要
δ 環で元の族を d で割る包の p 進完備完全化とその普遍性、族の比較、d 商への標準射と完全 prism への延長、族の取り方によらないこと。

## 方針
d で割る包（Delta/Division）を p 進完備に完全化する。原典の全 prism の中の始対象（超限帰納）は経由しない。

## 規約
perfectoid 性・IsPerfectoidization はここでは結論しない。

## 使われ方
BS 著者版 Corollary 7.3（`Semiperfectoid/Perfectoidization`）、André の perfectoid 候補。
旧 `Prism/Perfection` から移した。
-/

universe u v w t

/-! ## δ除算添加環のp進完備δ完全化

BS 著者版 Proposition 7.2とBS 著者版 Lemma 3.9に使う具体的な代数的候補。
除算添加の後に既存のp進完備δ完全化を施し、完全p進完備δ環への普遍性を証明する。
mod d商のperfectoid性・prism性・導来(p,d)完備化との比較は結論しない。
-/

@[expose] public noncomputable section PCompletedDeltaDivision

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

end PCompletedDeltaDivision

/-! ## 除算する元族の包含とp進完備δ除算候補の標準比較

BS 著者版 Proposition 7.2のJ/d添加に向け、任意の生成元族の生成イデアルに関する
包含から具体的なδ比較射を作り、恒等射・合成との両立を証明する。
候補のperfectoid性や標準射の全射性は結論しない。
-/

@[expose] public noncomputable section PCompletedDeltaDivisionComparison

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

end PCompletedDeltaDivisionComparison

/-! ## p進完備δ除算完全化のd商と完全prismへの延長

BS 著者版 Proposition 7.2とBS 著者版 Corollary 7.3に向けた具体的な環・標準写像・普遍性の部分定理。
任意の基底イデアルJを扱うが、d商のperfectoid性とIsPerfectoidizationは未結論。
-/

@[expose] public noncomputable section PCompletedDeltaDivisionQuotient

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R]

/-- Jの全元の像は、具体的な候補環でdの像の主イデアルに含まれる。 -/
theorem pCompletedDeltaDivisionMap_ideal_le_span (D : DeltaStructure p R) (d : R) (J : Ideal R) :
    J ≤ (Ideal.span {pCompletedDeltaDivisionMap D d (fun x : J ↦ (x : R)) d}).comap
      (pCompletedDeltaDivisionMap D d (fun x : J ↦ (x : R))) := by
  intro x hx
  apply Ideal.mem_span_singleton.mpr
  exact pCompletedDeltaDivisionMap_dvd D d (fun x : J ↦ (x : R)) ⟨x, hx⟩

/-- 任意の基底商R/Jから、具体的な候補のmod d商への標準射。 -/
def pCompletedDeltaDivisionQuotientMap (D : DeltaStructure p R) (d : R) (J : Ideal R) :
    R ⧸ J →+*
      (PCompletedDeltaDivision D d (fun x : J ↦ (x : R)) ⧸
        Ideal.span {pCompletedDeltaDivisionMap D d (fun x : J ↦ (x : R)) d}) :=
  Ideal.Quotient.lift J
    ((Ideal.Quotient.mk _).comp (pCompletedDeltaDivisionMap D d (fun x : J ↦ (x : R))))
    (by
      intro x hx
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      exact pCompletedDeltaDivisionMap_ideal_le_span D d J hx)

/-- 基底商への標準射は、代表元に候補への標準射を適用してmod dへ送る。 -/
@[simp] theorem pCompletedDeltaDivisionQuotientMap_mk
    (D : DeltaStructure p R) (d : R) (J : Ideal R) (x : R) :
    pCompletedDeltaDivisionQuotientMap D d J (Ideal.Quotient.mk J x) =
      Ideal.Quotient.mk _ (pCompletedDeltaDivisionMap D d (fun x : J ↦ (x : R)) x) := rfl

/-- 完全prismへの基底δ射でdとJがprismイデアルへ入れば、候補環からの一意延長が存在。
終域の正則性・p完備性・Jの像の可除性をprismの既存APIで内部に供給する。 -/
theorem existsUnique_pCompletedDeltaDivisionHom_to_perfectPrism
    {A : Type v} [CommRing A] (D : DeltaStructure p R) (d : R) (hd : D.IsDistinguished d)
    (J : Ideal R) (Q : OrientedPrism p A) (hQ : Q.deltaStructure.IsPerfect)
    (f : R →+* A) (hf : D.IsDeltaHom Q.deltaStructure f)
    (hdf : f d ∈ Q.ideal) (hJ : J ≤ Q.ideal.comap f) :
    ∃! g : PCompletedDeltaDivision D d (fun x : J ↦ (x : R)) →+* A,
      (pCompletedDeltaDivisionStructure D d (fun x : J ↦ (x : R))).IsDeltaHom Q.deltaStructure g ∧
        g.comp (pCompletedDeltaDivisionMap D d (fun x : J ↦ (x : R))) = f := by
  let := Q.isAdicComplete_p_of_perfect hQ
  let := Q.isAdicComplete_generator
  have hspan : (Ideal.span {d}).map f = Q.ideal :=
    hf.map_span_eq_of_distinguished_of_mem_span hd hdf
      (IsAdicComplete.le_jacobson_bot (Ideal.span {Q.generator}) (Ideal.subset_span (by simp)))
      (IsAdicComplete.le_jacobson_bot (Ideal.span {(p : A)}) (Ideal.subset_span (by simp)))
  have ha (x : J) : f d ∣ f (x : R) := by
    apply Ideal.mem_span_singleton.mp
    have hx := hJ x.property
    rw [← hspan, Ideal.map_span, Set.image_singleton] at hx
    exact hx
  exact existsUnique_pCompletedDeltaDivisionHom D Q.deltaStructure hQ d hd
    (fun x : J ↦ (x : R)) f hf ha

section Lift
variable {A : Type v} [CommRing A] (D : DeltaStructure p R) (d : R) (hd : D.IsDistinguished d)
variable (J : Ideal R) (Q : OrientedPrism p A) (hQ : Q.deltaStructure.IsPerfect)
variable (f : R →+* A) (hf : D.IsDeltaHom Q.deltaStructure f)
variable (hdf : f d ∈ Q.ideal) (hJ : J ≤ Q.ideal.comap f)

/-- 任意の完全prismへの一意な具体的延長環射。候補環にはprism性を仮定しない。 -/
def pCompletedDeltaDivisionPrismLift :
    PCompletedDeltaDivision D d (fun x : J ↦ (x : R)) →+* A :=
  (existsUnique_pCompletedDeltaDivisionHom_to_perfectPrism D d hd J Q hQ f hf hdf hJ).choose

/-- 選んだ延長環射はδ射。 -/
theorem pCompletedDeltaDivisionPrismLift_isDeltaHom :
    (pCompletedDeltaDivisionStructure D d (fun x : J ↦ (x : R))).IsDeltaHom Q.deltaStructure
      (pCompletedDeltaDivisionPrismLift D d hd J Q hQ f hf hdf hJ) :=
  (existsUnique_pCompletedDeltaDivisionHom_to_perfectPrism D d hd J Q hQ
    f hf hdf hJ).choose_spec.1.1

/-- 選んだ延長環射は標準基底射を延長する。 -/
@[simp] theorem pCompletedDeltaDivisionPrismLift_comp_map :
    (pCompletedDeltaDivisionPrismLift D d hd J Q hQ f hf hdf hJ).comp
      (pCompletedDeltaDivisionMap D d (fun x : J ↦ (x : R))) = f :=
  (existsUnique_pCompletedDeltaDivisionHom_to_perfectPrism D d hd J Q hQ
    f hf hdf hJ).choose_spec.1.2

/-- 候補のmod d商から完全prismの標準商への具体的な誘導射。 -/
def pCompletedDeltaDivisionPrismQuotientMap :
    (PCompletedDeltaDivision D d (fun x : J ↦ (x : R)) ⧸
      Ideal.span {pCompletedDeltaDivisionMap D d (fun x : J ↦ (x : R)) d}) →+* A ⧸ Q.ideal :=
  Ideal.quotientMap Q.ideal (pCompletedDeltaDivisionPrismLift D d hd J Q hQ f hf hdf hJ) (by
    apply (Ideal.span_singleton_le_iff_mem _).mpr
    change pCompletedDeltaDivisionPrismLift D d hd J Q hQ f hf hdf hJ
      (pCompletedDeltaDivisionMap D d (fun x : J ↦ (x : R)) d) ∈ Q.ideal
    rw [show pCompletedDeltaDivisionPrismLift D d hd J Q hQ f hf hdf hJ
      (pCompletedDeltaDivisionMap D d (fun x : J ↦ (x : R)) d) = f d from
        RingHom.congr_fun (pCompletedDeltaDivisionPrismLift_comp_map D d hd J Q hQ f hf hdf hJ) d]
    exact hdf)

/-- 候補を経由した基底商の写像は、元のfによる標準商射に一致する。 -/
theorem pCompletedDeltaDivisionPrismQuotientMap_comp :
    (pCompletedDeltaDivisionPrismQuotientMap D d hd J Q hQ f hf hdf hJ).comp
      (pCompletedDeltaDivisionQuotientMap D d J) = Ideal.quotientMap Q.ideal f hJ := by
  apply RingHom.ext
  intro x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  change Ideal.Quotient.mk Q.ideal (pCompletedDeltaDivisionPrismLift D d hd J Q hQ f hf hdf hJ
    (pCompletedDeltaDivisionMap D d (fun x : J ↦ (x : R)) r)) = Ideal.Quotient.mk Q.ideal (f r)
  rw [show pCompletedDeltaDivisionPrismLift D d hd J Q hQ f hf hdf hJ
    (pCompletedDeltaDivisionMap D d (fun x : J ↦ (x : R)) r) = f r from
      RingHom.congr_fun (pCompletedDeltaDivisionPrismLift_comp_map D d hd J Q hQ f hf hdf hJ) r]

end Lift
end SerrePositivity.BhattScholze

end PCompletedDeltaDivisionQuotient

/-! ## p進完備δ除算候補の生成元族からの独立性

任意の二つの元族が同じイデアルを生成すれば、候補の具体的なδ環同型とmod d商同型を得る。
有限生成性は要求しない。perfectoid性やIsPerfectoidizationとはまだ同定しない。
-/

@[expose] public noncomputable section PCompletedDeltaDivisionPresentation

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R]
variable {σ : Type v} {τ : Type w}

/-- 同じイデアルを生成する任意の元族の標準比較射は全単射。 -/
theorem pCompletedDeltaDivisionComparisonMap_bijective_of_span_eq
    (D : DeltaStructure p R) (d : R) (hd : D.IsDistinguished d) (a : σ → R) (b : τ → R)
    (hab : Ideal.span (Set.range a) = Ideal.span (Set.range b)) :
    Function.Bijective (pCompletedDeltaDivisionComparisonMap D d hd a b hab.le) := by
  let f := pCompletedDeltaDivisionComparisonMap D d hd a b hab.le
  let g := pCompletedDeltaDivisionComparisonMap D d hd b a hab.ge
  have hgf : g.comp f = RingHom.id (PCompletedDeltaDivision D d a) := by
    simpa only [pCompletedDeltaDivisionComparisonMap_id] using
      (pCompletedDeltaDivisionComparisonMap_comp D d hd a b a hab.le hab.ge).symm
  have hfg : f.comp g = RingHom.id (PCompletedDeltaDivision D d b) := by
    simpa only [pCompletedDeltaDivisionComparisonMap_id] using
      (pCompletedDeltaDivisionComparisonMap_comp D d hd b a b hab.ge hab.le).symm
  have hl : Function.LeftInverse g f := fun x ↦ RingHom.congr_fun hgf x
  have hr : Function.RightInverse g f := fun x ↦ RingHom.congr_fun hfg x
  exact ⟨hl.injective, hr.surjective⟩

/-- 同じイデアルを生成する二つの元族の候補環の具体的な標準同型。 -/
def pCompletedDeltaDivisionPresentationEquiv
    (D : DeltaStructure p R) (d : R) (hd : D.IsDistinguished d) (a : σ → R) (b : τ → R)
    (hab : Ideal.span (Set.range a) = Ideal.span (Set.range b)) :
    PCompletedDeltaDivision D d a ≃+* PCompletedDeltaDivision D d b :=
  RingEquiv.ofBijective (pCompletedDeltaDivisionComparisonMap D d hd a b hab.le)
    (pCompletedDeltaDivisionComparisonMap_bijective_of_span_eq D d hd a b hab)

/-- 標準同型の台環射は生成イデアルの包含による標準比較射。 -/
@[simp] theorem pCompletedDeltaDivisionPresentationEquiv_toRingHom
    (D : DeltaStructure p R) (d : R) (hd : D.IsDistinguished d) (a : σ → R) (b : τ → R)
    (hab : Ideal.span (Set.range a) = Ideal.span (Set.range b)) :
    (pCompletedDeltaDivisionPresentationEquiv D d hd a b hab).toRingHom =
      pCompletedDeltaDivisionComparisonMap D d hd a b hab.le := rfl

/-- 標準同型は元の基底射と可換。 -/
@[simp] theorem pCompletedDeltaDivisionPresentationEquiv_comp_base
    (D : DeltaStructure p R) (d : R) (hd : D.IsDistinguished d) (a : σ → R) (b : τ → R)
    (hab : Ideal.span (Set.range a) = Ideal.span (Set.range b)) :
    (pCompletedDeltaDivisionPresentationEquiv D d hd a b hab).toRingHom.comp
      (pCompletedDeltaDivisionMap D d a) = pCompletedDeltaDivisionMap D d b :=
  pCompletedDeltaDivisionComparisonMap_comp_base D d hd a b hab.le

/-- 標準同型の逆もδ射。 -/
theorem pCompletedDeltaDivisionPresentationEquiv_symm_isDeltaHom
    (D : DeltaStructure p R) (d : R) (hd : D.IsDistinguished d) (a : σ → R) (b : τ → R)
    (hab : Ideal.span (Set.range a) = Ideal.span (Set.range b)) :
    (pCompletedDeltaDivisionStructure D d b).IsDeltaHom (pCompletedDeltaDivisionStructure D d a)
      (pCompletedDeltaDivisionPresentationEquiv D d hd a b hab).symm.toRingHom :=
  DeltaStructure.IsDeltaHom.symm (pCompletedDeltaDivisionComparisonMap_isDeltaHom D d hd a b hab.le)

/-- 任意の生成元族の候補と、イデアルの全元を添加する候補との具体的な同型。
有限表示への変更は行わず、任意のイデアルJを保つ。 -/
def pCompletedDeltaDivisionIdealEquiv
    (D : DeltaStructure p R) (d : R) (hd : D.IsDistinguished d) (a : σ → R)
    (J : Ideal R) (hJ : Ideal.span (Set.range a) = J) :
    PCompletedDeltaDivision D d a ≃+* PCompletedDeltaDivision D d (fun x : J ↦ (x : R)) :=
  pCompletedDeltaDivisionPresentationEquiv D d hd a (fun x : J ↦ (x : R))
    (hJ.trans (by
      have hr : Set.range (fun x : J ↦ (x : R)) = (J : Set R) := by
        ext r
        simp
      rw [hr, Ideal.span_eq]))

/-- 同じイデアルを生成する元族の候補のmod d商の具体的な同型。 -/
def pCompletedDeltaDivisionPresentationQuotientEquiv
    (D : DeltaStructure p R) (d : R) (hd : D.IsDistinguished d) (a : σ → R) (b : τ → R)
    (hab : Ideal.span (Set.range a) = Ideal.span (Set.range b)) :
    (PCompletedDeltaDivision D d a ⧸ Ideal.span {pCompletedDeltaDivisionMap D d a d}) ≃+*
      (PCompletedDeltaDivision D d b ⧸ Ideal.span {pCompletedDeltaDivisionMap D d b d}) :=
  Ideal.quotientEquiv _ _ (pCompletedDeltaDivisionPresentationEquiv D d hd a b hab) (by
    rw [Ideal.map_span, Set.image_singleton]
    change Ideal.span {pCompletedDeltaDivisionMap D d b d} =
      Ideal.span {(pCompletedDeltaDivisionComparisonMap D d hd a b hab.le
        (pCompletedDeltaDivisionMap D d a d))}
    rw [show pCompletedDeltaDivisionComparisonMap D d hd a b hab.le
      (pCompletedDeltaDivisionMap D d a d) = pCompletedDeltaDivisionMap D d b d from
        RingHom.congr_fun (pCompletedDeltaDivisionComparisonMap_comp_base D d hd a b hab.le) d])

/-- mod d商同型は代表元上で標準比較射を適用する。 -/
@[simp] theorem pCompletedDeltaDivisionPresentationQuotientEquiv_mk
    (D : DeltaStructure p R) (d : R) (hd : D.IsDistinguished d) (a : σ → R) (b : τ → R)
    (hab : Ideal.span (Set.range a) = Ideal.span (Set.range b))
    (x : PCompletedDeltaDivision D d a) :
    pCompletedDeltaDivisionPresentationQuotientEquiv D d hd a b hab (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (pCompletedDeltaDivisionComparisonMap D d hd a b hab.le x) := rfl

/-- mod d商の比較同型も、元のRからの二つの標準射と可換する。 -/
theorem pCompletedDeltaDivisionPresentationQuotientEquiv_comp_base
    (D : DeltaStructure p R) (d : R) (hd : D.IsDistinguished d) (a : σ → R) (b : τ → R)
    (hab : Ideal.span (Set.range a) = Ideal.span (Set.range b)) :
    (pCompletedDeltaDivisionPresentationQuotientEquiv D d hd a b hab).toRingHom.comp
      ((Ideal.Quotient.mk _).comp (pCompletedDeltaDivisionMap D d a)) =
        (Ideal.Quotient.mk _).comp (pCompletedDeltaDivisionMap D d b) := by
  apply RingHom.ext
  intro r
  simp only [RingHom.comp_apply]
  exact congrArg (Ideal.Quotient.mk _)
    (RingHom.congr_fun (pCompletedDeltaDivisionComparisonMap_comp_base D d hd a b hab.le) r)

end SerrePositivity.BhattScholze

end PCompletedDeltaDivisionPresentation

/-! ## 具体的なp進完備δ除算候補の生成元冪商の有界ねじれ

原典BS 著者版 Lemma 3.9に向け、distinguished像のn乗商の有界pねじれ条件を供給する。
商のp完備性や導来(p,d)完備化との比較は結論しない。
-/

@[expose] public noncomputable section PCompletedDeltaDivisionPowerTorsion

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R] {σ : Type v}

/-- 具体的な候補のj(d)ⁿ商でp冪ねじれはpⁿで消える。
基底Rの完全性・完備性は要求せず、候補について既存証明から供給する。 -/
theorem pCompletedDeltaDivision_quotient_power_p_pow_torsion_killed_by_p_pow
    (D : DeltaStructure p R) (d : R) (hd : D.IsDistinguished d) (a : σ → R) (n N : ℕ)
    (x : PCompletedDeltaDivision D d a ⧸ Ideal.span {(pCompletedDeltaDivisionMap D d a d) ^ n})
    (hx : (p : PCompletedDeltaDivision D d a ⧸
      Ideal.span {(pCompletedDeltaDivisionMap D d a d) ^ n}) ^ N * x = 0) :
    (p : PCompletedDeltaDivision D d a ⧸
      Ideal.span {(pCompletedDeltaDivisionMap D d a d) ^ n}) ^ n * x = 0 := by
  let := pCompletedDeltaDivision_isAdicComplete D d a
  have hC := pCompletedDeltaDivision_isPerfect D d a
  exact hC.distinguished_quotient_power_p_pow_torsion_killed_by_p_pow
      ((pCompletedDeltaDivisionMap_isDeltaHom D d a).map_isDistinguished hd) n N x hx

end SerrePositivity.BhattScholze

end PCompletedDeltaDivisionPowerTorsion
