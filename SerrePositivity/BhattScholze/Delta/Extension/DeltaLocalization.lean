module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.BhattScholze.Delta.Basic.DeltaRing
public import Mathlib.RingTheory.Localization.Basic

/-!
# δ 構造の局所化への延長（BS 著者版 Lemma 2.15、BS 著者版 Remark 2.16）

## 概要
Frobenius 安定な乗法集合での局所化に δ 構造が一意に延び、普遍性を持つ。任意の分母集合はその Frobenius 像で安定化する。

## 方針
W₂ の元が単元 ⇔ 第 0 座標と第 1 ghost 成分が単元、を使って切断を延ばす（自由 δ 環への帰着をしない）。

## 規約
p ねじれを許す。

## 使われ方
BS 著者版 Lemma 2.15 の局所化と Example 2.21 の普遍 distinguished δ 環に用いる。
-/

@[expose] public noncomputable section
universe u v w

/-! ## Frobenius安定な乗法集合におけるδ局所化

BS 著者版 Lemma 2.15。W₂切断と二成分の単元判定で、pねじれのある環も
直接扱う。基底のp正則性を追加せず、Mathlibの局所化の普遍性を再利用する。
-/

section DeltaLocalization

namespace SerrePositivity.BhattScholze.DeltaStructure
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R]
variable (D : DeltaStructure p R) (M : Submonoid R)
variable (B : Type v) [CommRing B] [Algebra R B] [IsLocalization M B]
variable (hφ : ∀ s : M, D.frobeniusLift s ∈ M)
include hφ

/-- 局所化先に移したW₂切断は、分母を単元に送る。 -/
theorem localization_section_isUnit (s : M) :
    IsUnit (((wittTwoMap (p := p) (algebraMap R B)).comp D.sectionHom) s) := by
  apply (wittTwo_isUnit_iff _).mpr
  constructor
  · simpa only [RingHom.comp_apply, wittTwoMap_coeff, D.coeff_zero] using
      IsLocalization.map_units B s
  · have h := IsLocalization.map_units B ⟨D.frobeniusLift s, hφ s⟩
    convert h using 1
    simp only [RingHom.comp_apply, wittTwoFrobenius_apply, wittTwoMap_coeff,
      D.coeff_zero, frobeniusLift_apply, map_add, map_pow, map_mul, map_natCast]
    rfl

/-- Frobenius安定な集合における局所化のW₂切断。 -/
def localizationSection : B →+* WittTwo p B :=
  IsLocalization.lift (M := M) (S := B) (D.localization_section_isUnit M B hφ)

/-- 局所化切断は基底上で元の切断と両立する。 -/
theorem localizationSection_comp :
    (D.localizationSection M B hφ).comp (algebraMap R B) =
      (wittTwoMap (p := p) (algebraMap R B)).comp D.sectionHom :=
  IsLocalization.lift_comp _

/-- 切断と第0座標射の合成は恒等射。局所化の射の外延性から従う。 -/
theorem localizationSection_projection :
    (wittTwoProjection p B).comp (D.localizationSection M B hφ) = RingHom.id B := by
  apply IsLocalization.ringHom_ext M
  ext r
  change wittTwoProjection p B (D.localizationSection M B hφ (algebraMap R B r)) =
    algebraMap R B r
  rw [show D.localizationSection M B hφ (algebraMap R B r) =
    wittTwoMap (algebraMap R B) (D.sectionHom r) from
    DFunLike.congr_fun (D.localizationSection_comp M B hφ) r]
  simp [D.coeff_zero]

/-- Frobenius安定な分母集合による局所化のδ構造（BS 著者版 Lemma 2.15 の構造の構成）。 -/
def localization : DeltaStructure p B where
  sectionHom := D.localizationSection M B hφ
  coeff_zero := by
    intro x
    exact DFunLike.congr_fun (D.localizationSection_projection M B hφ) x

/-- 標準局所化射はδ射。 -/
theorem isDeltaHom_localization : D.IsDeltaHom (D.localization M B hφ) (algebraMap R B) := by
  apply (D.isDeltaHom_iff_sectionHom_comp _ _).mpr
  exact (D.localizationSection_comp M B hφ).symm

/-- 標準射と両立する局所化のδ構造は一意。p正則性は不要。 -/
theorem localization_unique (E : DeltaStructure p B)
    (hE : D.IsDeltaHom E (algebraMap R B)) : E = D.localization M B hφ := by
  have he := (D.isDeltaHom_iff_sectionHom_comp E _).mp hE
  have hs : E.sectionHom = (D.localization M B hφ).sectionHom := by
    apply IsLocalization.ringHom_ext M
    exact he.symm.trans (D.localizationSection_comp M B hφ).symm
  apply ext
  intro x
  exact congrArg (fun y : WittTwo p B ↦ y.coeff 1) (DFunLike.congr_fun hs x)

/-- Frobenius安定な集合での局所化は一意な適合δ構造を持つ（BS 著者版 Lemma 2.15 の第一文の存在一意性）。 -/
theorem existsUnique_localization :
    ∃! E : DeltaStructure p B, D.IsDeltaHom E (algebraMap R B) :=
  ⟨D.localization M B hφ, D.isDeltaHom_localization M B hφ,
    fun E hE ↦ D.localization_unique M B hφ E hE⟩

/-- Mの元を単元に送るδ射は、局所化から一意なδ射へ延長する（BS 著者版 Lemma 2.15 の第二文の普遍性）。 -/
theorem existsUnique_localization_lift {A : Type w} [CommRing A]
    (E : DeltaStructure p A) (f : R →+* A) (hf : D.IsDeltaHom E f)
    (hM : ∀ s : M, IsUnit (f s)) :
    ∃! g : B →+* A,
      g.comp (algebraMap R B) = f ∧ (D.localization M B hφ).IsDeltaHom E g := by
  let g : B →+* A := IsLocalization.lift hM
  have hg : g.comp (algebraMap R B) = f := IsLocalization.lift_comp hM
  refine ⟨g, ⟨hg, ?_⟩, ?_⟩
  · apply ((D.localization M B hφ).isDeltaHom_iff_sectionHom_comp E g).mpr
    apply IsLocalization.ringHom_ext M
    ext r i
    have hj := DFunLike.congr_fun (D.localizationSection_comp M B hφ) r
    have hk := (D.isDeltaHom_iff_sectionHom_comp E f).mp hf
    have hl := DFunLike.congr_fun hk r
    simp only [RingHom.comp_apply] at hj hl ⊢
    change (wittTwoMap g (D.localizationSection M B hφ (algebraMap R B r))).coeff i =
      (E.sectionHom (g (algebraMap R B r))).coeff i
    rw [hj, wittTwoMap_coeff, wittTwoMap_coeff]
    have hc (x : R) : g (algebraMap R B x) = f x := DFunLike.congr_fun hg x
    rw [hc, hc]
    simpa only [wittTwoMap_coeff] using
      congrArg (fun x : WittTwo p A ↦ x.coeff i) hl
  · intro k hk
    apply IsLocalization.ringHom_ext M
    exact hk.1.trans hg.symm

end SerrePositivity.BhattScholze.DeltaStructure

end DeltaLocalization

/-! ## 任意の分母集合のFrobenius安定化

BS 著者版 Remark 2.16のT={S,φ(S),φ²(S),…}の代数的構成。
Tでの局所化はSを単元に送るδ基底射について普遍である。
p局所化・p完備化との比較は主張しない。
-/

section DeltaLocalizationSaturation

namespace SerrePositivity.BhattScholze.DeltaStructure
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R]

/-- 分母集合のFrobenius反復像を含む乗法的閉包（BS 著者版 Remark 2.16 の Frobenius 飽和の部分）。 -/
def frobeniusDenominators (D : DeltaStructure p R) (M : Submonoid R) : Submonoid R :=
  Submonoid.closure (Set.range (fun t : M × ℕ ↦ (D.frobeniusLift : R → R)^[t.2] t.1))

/-- 元の分母集合はFrobenius安定化に含まれる。 -/
theorem le_frobeniusDenominators (D : DeltaStructure p R) (M : Submonoid R) :
    M ≤ D.frobeniusDenominators M := by
  intro s hs
  exact Submonoid.subset_closure ⟨(⟨s, hs⟩, 0), rfl⟩

/-- 安定化した分母集合はFrobeniusで安定。 -/
theorem frobeniusDenominators_stable (D : DeltaStructure p R) (M : Submonoid R)
    (s : D.frobeniusDenominators M) :
    D.frobeniusLift s ∈ D.frobeniusDenominators M := by
  have h : D.frobeniusDenominators M ≤
      (D.frobeniusDenominators M).comap D.frobeniusLift.toMonoidHom := by
    apply Submonoid.closure_le.mpr
    rintro x ⟨⟨r, n⟩, rfl⟩
    apply Submonoid.subset_closure
    exact ⟨(r, n + 1), Function.iterate_succ_apply' _ _ _⟩
  exact h s.property

/-- 安定化はMを含む最小のFrobenius安定乗法集合。 -/
theorem frobeniusDenominators_le (D : DeltaStructure p R) (M N : Submonoid R)
    (hMN : M ≤ N) (hN : ∀ s : N, D.frobeniusLift s ∈ N) :
    D.frobeniusDenominators M ≤ N := by
  apply Submonoid.closure_le.mpr
  rintro x ⟨⟨s, n⟩, rfl⟩
  induction n with
  | zero => exact hMN s.property
  | succ n ih =>
    change (D.frobeniusLift : R → R)^[n + 1] s ∈ N
    rw [Function.iterate_succ_apply']
    exact hN ⟨_, ih⟩

/-- δ射が元の分母を単元に送れば、Frobenius安定化の全分母も単元に送る。 -/
theorem IsDeltaHom.isUnit_frobeniusDenominators {A : Type w} [CommRing A]
    {D : DeltaStructure p R} {E : DeltaStructure p A} {f : R →+* A}
    (hf : D.IsDeltaHom E f) (M : Submonoid R) (hM : ∀ s : M, IsUnit (f s))
    (s : D.frobeniusDenominators M) : IsUnit (f s) := by
  have hiter (r : M) (n : ℕ) : IsUnit (f ((D.frobeniusLift : R → R)^[n] r)) := by
    induction n with
    | zero => exact hM r
    | succ n ih =>
      rw [Function.iterate_succ_apply', hf.map_frobeniusLift]
      exact ih.map E.frobeniusLift
  exact Submonoid.closure_induction
    (fun x hx ↦ by obtain ⟨⟨r, n⟩, rfl⟩ := hx; exact hiter r n)
    (by simp)
    (fun x y _ _ hx hy ↦ by rw [map_mul]; exact hx.mul hy) s.property

/-- 任意のMを反復像で安定化して局所化すると、Mを単元に送るδ射の普遍対象となる（BS 著者版 Remark 2.16 の Frobenius 飽和での普遍性）。
源・標準射・局所化δ構造を具体的に明示する。 -/
theorem existsUnique_saturatedLocalization_lift (D : DeltaStructure p R) (M : Submonoid R)
    (B : Type v) [CommRing B] [Algebra R B] [IsLocalization (D.frobeniusDenominators M) B]
    {A : Type w} [CommRing A] (E : DeltaStructure p A) (f : R →+* A)
    (hf : D.IsDeltaHom E f) (hM : ∀ s : M, IsUnit (f s)) :
    ∃! g : B →+* A,
      g.comp (algebraMap R B) = f ∧
        (D.localization (D.frobeniusDenominators M) B
          (D.frobeniusDenominators_stable M)).IsDeltaHom E g :=
  D.existsUnique_localization_lift (D.frobeniusDenominators M) B
    (D.frobeniusDenominators_stable M) E f hf
    (hf.isUnit_frobeniusDenominators M hM)

end SerrePositivity.BhattScholze.DeltaStructure

end DeltaLocalizationSaturation

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Lemma 2.15"] _root_.SerrePositivity.BhattScholze.DeltaStructure.existsUnique_localization
attribute [cite BS19 "Lemma 2.15"] _root_.SerrePositivity.BhattScholze.DeltaStructure.existsUnique_localization_lift
attribute [cite BS19 "Lemma 2.15"] _root_.SerrePositivity.BhattScholze.DeltaStructure.localization
attribute [cite BS19 "Rem 2.16"] _root_.SerrePositivity.BhattScholze.DeltaStructure.existsUnique_saturatedLocalization_lift
attribute [cite BS19 "Rem 2.16"] _root_.SerrePositivity.BhattScholze.DeltaStructure.frobeniusDenominators
